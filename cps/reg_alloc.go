// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Register allocation version 3.
//
// Registers will be assigned to 'chains'.  The initial set
// of chains are just the inputs and outputs of each call
// (ignoring those that do not need to be in registers, and
// the arguments of jumps and outputs of JumpLambdas, which
// just pass values along, and values that do not start out in
// registers, which are described below).
// They can necessarily be assigned registers, as any single
// call is limited to the architecture's registers.
// A chain consists of a set of connected links.
//
// A 'link' is a live range that could be assigned a register.
// A link has:
//   - The set of program points in its live range.
//   - 'Starts' which is a slice of links from which it can receive a value.
//   - 'Ends' which is a slice of links to which it provides a value.
//   - A chain, if it has been assigned to one.
// Initially, the inputs and outputs of all calls have a chain
// with a single link that covers just that call.  These are
// connected by additional links, not initially in chains, that
// connect definitions and uses of variables.  For example, if
// variable X is defined in call A and has two uses, one in call
// B and the next in call C then we will get the following:
//  - Three links with anchors, one for each of the calls.
//  - Two connecting links without anchors, one between the
//    A and B anchor links and one between the B and C anchor
//    links.
//  - Thus the A anchor link will have no starts and one end,
//    the one at B will have one start and one end, and the
//    one at C will have one start and no ends.
// Links end at the end of a basic block and are connected to the
// links for the same variable at the start of the following blocks.
// Thus there are no parallel links: at each program point a variable
// has at most one link.  The exception is a variable that is live in a
// loop but not referenced in it.  It has a single link that covers the
// entire loop, or the outermost such loop if there are several, which
// is considered to be outside the loop.  At a jump the links of the
// arguments are connected to those of the JumpLambda's outputs.  Links
// and chains are for values, and the same value may be bound to
// different variables.  When all links have been added you can follow
// the links from where a value is created to all of the places that it
// is used.
//
// The next step is to merge chains using the links between them
// in such a way that the normal coloring algorithm will be able to
// assign a register to each chain.
//
// The main data structure is a priority queue of searches, one for
// each chain that has links below it that are not yet in chains.  A
// search is a tree of such links, going down from the chain.  A link
// is only added to a tree once, so the number of paths does not
// matter.  Searches are ordered by the depth of their shallowest leaf,
// in units of program points, with shallower ones having priority over
// deeper ones.  Constants come after everything else, as they never need
// to be spilled.  Links in inner loops come before those in outer ones, as
// good allocation is more important there.  Within a loop, paths that go
// through a jump from an argument to an output come after those that
// stay within one variable.  Otherwise an argument that is live after the
// jump may be merged with the output, which keeps it from being merged
// with the rest of its own variable.
//
// The algorithm progresses by removing the first search and extending
// it along its shallowest leaf.  If this reaches a chain, possibly the
// one it started from, then the path to it is made into a chain, merged
// with both of the chains it connects if possible, or with one or the
// other, or with neither.  The search for the upper chain, and for the
// path's chain if that is different, then start over.  The search for
// any chain that was merged into another is cancelled.  Any other
// search that was using a link that is now in a chain also starts
// over.  Going down is sufficient to find all of the links, as every
// link has some chain above it.  After a spill there may be links that
// are only reachable through the spilled one.  These stay in memory, and
// the value is loaded when it reaches the chain below them.
//
// A path can be merged with a set of chains, which may be empty, if
// none of their live ranges overlap and doing so meets the
// neighbor-count criteria.  The neighbors of a chain are the chains
// whose live ranges overlap its own.  A neighbor is significant if it
// has at least as many neighbors as it has allowed registers, with all of
// these counted as they will be after the merge.  The result must either
// have fewer significant neighbors than it has allowed registers (Briggs)
// or have all of its significant neighbors already be neighbors of one
// of the chains being merged that has the same allowed registers
// (George).
//
// If a path can't be added as a whole then the links in it are tried
// individually, from the lower end up.  The first that can't be put in
// a chain is spilled, along with any links above it that only lead to
// spilled links.  Other links above it are left for other paths.  Any
// link that never ends up in a chain is in memory.  There is no
// backtracking.  The search priorities are intended to make the
// link that does not get a register the right one to spill.
//
// Some values do not start out in registers assigned by the allocator.
// These are constants and values created in fixed registers, such as
// arguments and returned values.  Where such a value is created there is
// a source link, which is never in a chain.  Its location is the constant
// or the fixed register.  As there may be no chain above them, there are
// searches from source links, as there are from chains.  Values used in
// fixed registers are moved there as part of the call that uses them.  A
// link that leads to such a use can be the end of a path, as a chain can.
//
// Each procedure is allocated separately.  For now procedures cannot have
// free variables, as there are no lexical environments.
//
// Calls can change the values in some registers, such as those that a
// procedure call does not preserve.  Each chain has a set of registers
// that it is allowed, which excludes any that are changed by calls that
// the chain is live across.  The merging criteria and the coloring use
// each chain's number of allowed registers.
//
// Constants are not stored in memory.  They are instead loaded wherever
// they are needed and are not already in a register, with nothing done
// where they are bound.  As searches from constants have the lowest
// priority, there is also a search from the last link of each constant
// that is passed to a jump.  That may be the only source of the value of
// the JumpLambda's output.
//
// The chains are then assigned registers using the usual graph coloring
// algorithm, which the criteria ensure will succeed.  This leaves:
//  - Moves, wherever a link in one chain connects to one in a chain with
//    a different register.
//  - Stores, where values that are ever in memory are created.  If an
//    output of a JumpLambda is in memory then so are the arguments that
//    are passed to it, if they can share the same slot.  Otherwise the
//    value is stored by the jump.
//  - Loads, from memory or of a constant, where a link that is not in a
//    chain connects to one that is.
// These always come between calls, as any link that begins or ends within
// a call is the start or end of a value.  They are returned in a map from
// calls to what has to happen there.  Those between blocks are done either
// as part of a jump or, following a conditional, before the first call in
// the next block.

package cps

import (
	"fmt"
	"iter"
	"maps"
	"slices"

	"github.com/s48/transform/util"
)

// Variable fields used for register allocation.

type varRegAllocT struct {
	definition *linkT
	uses       map[NodeT]*linkT
}

func (vart *VariableT) Register() RegisterT {
	if vart.definition == nil {
		return nil
	}
	chain := vart.definition.chain.root()
	if chain == nil {
		return nil // a constant that is loaded when it is needed
	}
	return chain.Register
}

func (vart *VariableT) ReferenceRegister(node NodeT) RegisterT {
	link := vart.uses[node]
	if link == nil {
		panic(fmt.Sprintf("No register for %s", node))
	}
	return link.chain.root().Register
}

// Returns the literal if the variable is bound to a constant.  These are
// never stored in memory, as they can be loaded whenever they are needed.
func (vart *VariableT) constant() NodeT {
	if vart.Binder != nil && vart.Binder.Primop.Name() == "loadReg" {
		return vart.Binder.Inputs[0]
	}
	return nil
}

func (vart *VariableT) addUse(node NodeT, link *linkT) {
	uses := vart.uses
	if uses == nil {
		vart.uses = map[NodeT]*linkT{node: link}
	} else {
		uses[node] = link
	}
}

type linkT struct {
	id        int // for debugging
	variable  *VariableT
	starts    []*linkT
	ends      []*linkT
	liveRange liveRangeT
	chain     *chainT // if it is in one
	spilled   bool    // it cannot be in a chain
	// Non-nil for a source link, which is where a value is created other
	// than in a register that the allocator assigns.  Source links are never
	// in chains.  This is the value's location, either a constant or a fixed
	// register.
	source *RegLocationT
	// The link starts within a call, after a use whose anchor ends at the
	// call's early point.  As moves are only possible between calls, this
	// can only be in the anchor's chain or in memory.
	followsAnchor bool
	// If non-nil the value is moved from this link to a fixed register.  The
	// link can be the end of a path just as a chain can.
	fixedUse  *RegisterClassT
	searches  []*searchT // searches that may be using this link
	loopDepth int        // depth of the innermost loop containing the link
}

var nextLinkIdx = -1

func nextLinkId() int {
	nextLinkIdx += 1
	return nextLinkIdx
}

func joinLinks(from *linkT, to *linkT) {
	Push(&to.starts, from)
	Push(&from.ends, to)
}

// For debugging.  If true the links for each variable are printed.
var PrintRegisterLinks = false

func (alloc *allocatorT) printLinks(blocks []*regBlockT) {
	for _, block := range blocks {
		fmt.Printf("block %s_%d [%d, %d)\n", block.start.Name, block.start.Id, block.startIndex, block.endIndex)
	}
	// Sort the variables to get deterministic behavior.
	for _, vart := range sortedVars(maps.Keys(alloc.allVars)) {
		if vart.definition != nil {
			printVarLinks(vart, vart.definition)
		}
	}
	for _, block := range blocks {
		for _, vart := range block.start.Outputs {
			liveLink := block.liveLinks[vart]
			if liveLink != nil {
				printVarLinks(vart, liveLink.link)
			}
		}
	}
}

func printVarLinks(vart *VariableT, link *linkT) {
	seen := util.SetT[*linkT]{}
	fmt.Printf("%s:\n", vart)
	var printLink func(link *linkT, indent string)
	printLink = func(link *linkT, indent string) {
		// Jumps connect to the links of other variables.
		if seen.Contains(link) || link.variable != vart {
			fmt.Printf("%s -> %d %s\n", indent, link.id, link.variable)
			return
		}
		seen.Add(link)
		tag := ""
		if link.chain != nil {
			tag = " chain "
		}
		fmt.Printf("%s%d %s%s", indent, link.id, link.variable, tag)
		for _, interval := range link.liveRange.intervals {
			fmt.Printf("[%d, %d]", interval.start, interval.end)
		}
		fmt.Printf("\n")
		indent += "  "
		for _, end := range link.ends {
			printLink(end, indent)
		}
	}
	printLink(link, "")
}

type chainT struct {
	id        int
	links     []*linkT
	liveRange *liveRangeT // All of the links' intervals combined.
	class     *RegisterClassT
	conflicts util.SetT[*chainT]
	allowed   registerSetT // registers that the chain can be assigned
	search    *searchT     // for links below this, if there are any
	Register  RegisterT    // what gets assigned to this
	peer      *chainT
}

var nextChainIdx = -1

func nextChainId() int {
	nextChainIdx += 1
	return nextChainIdx
}

func newChain(link *linkT, class *RegisterClassT) *chainT {
	chain := &chainT{
		id:        nextChainId(),
		class:     class,
		liveRange: &liveRangeT{},
		conflicts: util.NewSet[*chainT](),
		allowed:   class.newRegisterSet(),
	}
	chain.addLink(link)
	return chain
}

func (chain *chainT) root() *chainT {
	if chain == nil {
		return chain
	}
	for chain.peer != nil {
		chain = chain.peer
	}
	return chain
}

func (chain *chainT) addLink(link *linkT) {
	chain = chain.root()
	link.chain = chain
	chain.liveRange = chain.liveRange.union(&link.liveRange)
	Push(&chain.links, link)
}

func (chain *chainT) merge(other *chainT) {
	chain = chain.root()
	other = other.root()
	other.peer = chain
	chain.liveRange = chain.liveRange.union(other.liveRange)
	chain.links = append(chain.links, other.links...)
	for otherConflict := range other.conflicts {
		otherConflict.conflicts.Remove(other)
		otherConflict.conflicts.Add(chain)
		chain.conflicts.Add(otherConflict)
	}
}

//----------------------------------------------------------------

type regBlockT struct {
	start      *CallNodeT
	end        *CallNodeT
	startIndex int // program point of the early phase of 'start'
	endIndex   int // program point after the late phase of 'end'
	callCount  int // number of calls in the block
	next       []*regBlockT

	seen        bool
	loop        *regLoopT                 // innermost loop containing this block, if any
	liveIn      util.SetT[*VariableT]     // variables live at the start of the block
	liveOutputs util.SetT[*VariableT]     // JumpLambda outputs whose values are used
	jumpArgs    []*VariableT              // jump arguments, nil if not in a register
	liveLinks   map[*VariableT]*liveLinkT // when done these are for the start of the block
	endLinks    map[*VariableT]*linkT     // links live at the end of the block
	inputSpecs  [][]*RegUseSpecT          // cached for each call in the block
	outputSpecs [][]*RegUseSpecT
}

// liveLinkT represents a live variable during the bottom-up scan
// that finds live ranges.
type liveLinkT struct {
	endIndex int    // The end of the current interval being scanned.
	link     *linkT // The connecting link that the interval will be added to.
}

func makeRegBlock() *regBlockT {
	return &regBlockT{}
}

// Caches the register specs of the block's calls.

func (block *regBlockT) initialize(start *CallNodeT, end *CallNodeT) {
	block.start = start
	block.end = end
	for call := start; ; call = call.Next[0] {
		inputs, outputs := call.Primop.RegisterUsage(call)
		// The generic primops in primop.go are only for evaluating code.
		for _, spec := range slices.Concat(inputs, outputs) {
			if spec != nil && spec.Class == generalRegister {
				panic(fmt.Sprintf("call %s uses a generic primop's register specs", call))
			}
		}

		block.inputSpecs = append(block.inputSpecs, inputs)
		block.outputSpecs = append(block.outputSpecs, outputs)

		if outputs != nil {
			if len(outputs) != len(call.Outputs) {
				panic(fmt.Sprintf("Primop %s returned %d output registers but has %d outputs.",
					call.Primop.Name(), len(outputs), len(call.Outputs)))
			}
		}
		if inputs != nil {
			if len(inputs) != len(call.Inputs) {
				panic(fmt.Sprintf("Primop %s returned %d input registers but has %d inputs.",
					call.Primop.Name(), len(inputs), len(call.Inputs)))
			}
		}
		if call == end {
			if end.Primop.Name() == "jump" {
				block.jumpArgs = findJumpArgs(end, inputs)
			}
			break
		}
	}
	block.callCount = len(block.inputSpecs)
}

func (block *regBlockT) addNext(rawNext BasicBlockT) {
	block.next = append(block.next, rawNext.(*regBlockT))
}

func (block *regBlockT) getEnd() *CallNodeT {
	return block.end
}

type allocatorT struct {
	allVars util.SetT[*VariableT]

	// This includes early and late points for each CPS call in the
	// program.  Equal to twice the number of CPS calls.
	numProgramPoints int

	allChains util.SetT[*chainT]
	// Registers whose values are changed at each program point, which is
	// the late point of each call that changes any.
	clobbers map[int][]RegisterT
	// Links whose values are moved to or from fixed registers.
	preferences []preferenceT
	// Links that have searches of their own, as their values may not come
	// from a chain.  These are source links and the last links of constants
	// that are passed to jumps.
	rootLinks []*linkT
	// The chains that are live at each program point.
	chainPoints []util.SetT[*chainT]
	searchQueue *util.PriorityQueueT[*searchT]
}

// Returns the moves, loads and stores needed at each call.

func AllocateRegisters(
	top *CallNodeT,
	classes ...*RegisterClassT,
) *RegAllocationT {
	makeVarsForLiterals()
	result := &RegAllocationT{
		Moves:  map[*CallNodeT]*RegMovesT{},
		Frames: map[*CallNodeT]*RegFrameT{},
	}
	for _, proc := range FindProcs(top) {
		allocator := &allocatorT{
			allVars:   util.NewSet[*VariableT](),
			allChains: util.NewSet[*chainT](),
		}
		allocation := allocator.allocate(proc, classes)
		maps.Copy(result.Moves, allocation.Moves)
		result.Frames[proc] = &RegFrameT{allocation.NumSlots, allocation.Registers}
	}
	return result
}

// Returns 'top' and all of the procedures within it, sorted by Id.  These
// do not include any inside the procedures' JumpLambdas.
func FindProcs(top *CallNodeT) []*CallNodeT {
	procs := []*CallNodeT{}
	var find func(call *CallNodeT)
	find = func(call *CallNodeT) {
		if call.CallType == ProcLambda {
			Push(&procs, call)
		}
		for _, input := range call.Inputs {
			if IsCallNode(input) {
				find(input.(*CallNodeT))
			}
		}
		for _, next := range call.Next {
			find(next)
		}
	}
	find(top)
	slices.SortFunc(procs, func(x, y *CallNodeT) int { return x.Id - y.Id })
	return procs
}

// Each procedure is allocated separately.
func (alloc *allocatorT) allocate(
	proc *CallNodeT,
	classes []*RegisterClassT,
) *procAllocationT {
	FindBasicBlocks[*regBlockT](proc, makeRegBlock)
	blocks := orderBlocks(proc.Block.(*regBlockT))
	index := 0
	for _, block := range blocks {
		block.startIndex = index
		index += block.callCount * 2 // early, late
		block.endIndex = index
	}

	alloc.numProgramPoints = index
	alloc.makeLinks(blocks)
	if len(blocks[0].liveIn) != 0 {
		panic(fmt.Sprintf("procedure %s_%d has free variables, which are not supported yet",
			proc.Name, proc.Id))
	}

	if PrintRegisterLinks {
		alloc.printLinks(blocks)
	}

	alloc.mergeChains()
	for _, class := range classes {
		alloc.colorChains(class)
	}
	return alloc.findMoves(blocks)
}

// Returns the blocks reachable from 'start' in reverse postorder.
// Except for the back edges of loops, every block comes before all of
// its next blocks.  Next blocks are visited last to first so that a
// block's first next block tends to come directly after it.

func orderBlocks(start *regBlockT) []*regBlockT {
	blocks := []*regBlockT{}
	var visit func(block *regBlockT)
	visit = func(block *regBlockT) {
		block.seen = true
		for _, next := range slices.Backward(block.next) {
			if !next.seen {
				visit(next)
			}
		}
		blocks = append(blocks, block)
	}
	visit(start)
	slices.Reverse(blocks)
	return blocks
}

// The blocks must be in the order returned by orderBlocks.

func (alloc *allocatorT) makeLinks(blocks []*regBlockT) {
	alloc.findClobbers(blocks)
	findLiveIn(blocks)
	makeLoopLinks(blocks)
	for _, block := range slices.Backward(blocks) {
		alloc.findLiveRanges(block.start)
	}
	// These are done last because with loops a block's next block may be
	// processed after the block.
	for _, block := range blocks {
		block.connectNext()
		alloc.connectJump(block)
	}
}

func (alloc *allocatorT) findLiveRanges(top *CallNodeT) {
	block := top.Block.(*regBlockT)
	// Links do not cross block boundaries.  Each variable that is live
	// at the end of the block gets a new link, which is connected to the
	// following blocks in connectNext.
	block.liveLinks = map[*VariableT]*liveLinkT{}
	block.endLinks = map[*VariableT]*linkT{}
	// Sort the variables to get deterministic behavior.
	for _, vart := range sortedVars(maps.Keys(block.liveOut())) {
		if block.loop.link(vart) == nil {
			link := block.makeLink(vart)
			block.liveLinks[vart] = &liveLinkT{endIndex: block.endIndex, link: link}
			block.endLinks[vart] = link
		}
	}

	callIndex := block.callCount - 1
	lateIndex := block.endIndex - 1
	for call := block.end; 0 <= callIndex; call = call.parent {
		for i, spec := range block.outputSpecs[callIndex] {
			// The values of a JumpLambda's outputs come from the jumps to it,
			// so they are just live at the start of the block.
			if spec == nil || call.CallType == JumpLambda {
				continue
			}
			vart := call.Outputs[i]
			alloc.allVars.Add(vart)
			start := lateIndex + spec.PhaseOffset
			end := lateIndex + 1 // inclusive -> exclusive

			liveLink := block.liveLinks[vart]
			source := RegLocationT{Register: spec.Fixed, Constant: vart.constant()}
			if source == (RegLocationT{}) {
				vart.definition = alloc.addAnchorLink(vart, start, end, spec.Class, liveLink)
			} else if liveLink != nil {
				// A source link, not an anchor, as this does not have to be in
				// a register.  A constant can be loaded when it is needed and
				// a value in a fixed register is moved out of it.
				link := block.makeLink(vart)
				link.liveRange.add(intervalT{start, end})
				link.source = &source
				if spec.Fixed != nil {
					alloc.addPreference(block, liveLink.link, spec.Fixed)
				}
				connectBelow(link, end, liveLink)
				vart.definition = link
				Push(&alloc.rootLinks, link)
			}
			delete(block.liveLinks, vart)
		}

		inputs := getInputs(call, anchoredSpecs(block.inputSpecs[callIndex]))
		if call.Primop.Name() == "jump" {
			inputs = nil // these just need to be live at the end of the block
		}
		// Values that are moved to fixed registers have no anchors.  They just
		// need to be live at the call's early point.
		for i, spec := range block.inputSpecs[callIndex] {
			if spec != nil && spec.Fixed != nil {
				vart := call.Inputs[i].(*ReferenceNodeT).Variable
				if block.liveLinks[vart] == nil {
					link := block.makeLink(vart)
					block.liveLinks[vart] = &liveLinkT{endIndex: lateIndex, link: link}
				}
				// This is set even if the value is used later.  The use may be
				// the only reason for the value to be in a register, as when the
				// value is passed around a loop.
				link := block.liveLinks[vart].link
				link.fixedUse = spec.Class
				alloc.addPreference(block, link, spec.Fixed)
			}
		}
		for _, input := range inputs {
			vart := input.variable
			start := lateIndex + EarlyRegUse
			end := lateIndex + input.phaseOffset + 1 // +1 for inclusive to exclusive
			liveLink := block.liveLinks[vart]
			if liveLink != nil && end != lateIndex+1 {
				liveLink.link.followsAnchor = true
			}
			link := alloc.addAnchorLink(vart, start, end, input.class, liveLink)
			for _, index := range input.argIndexes {
				vart.addUse(call.Inputs[index], link)
			}
			connectLink := block.makeLink(vart)
			joinLinks(connectLink, link)
			block.liveLinks[vart] = &liveLinkT{endIndex: start, link: connectLink}
		}
		callIndex -= 1
		lateIndex -= 2
	}

	// Each has its own link, so the order does not matter.
	for _, liveLink := range block.liveLinks {
		// They are equal if the variable is used early in the first call.
		if block.startIndex < liveLink.endIndex {
			liveLink.link.liveRange.add(intervalT{block.startIndex, liveLink.endIndex})
		}
	}
}

func (block *regBlockT) makeLink(vart *VariableT) *linkT {
	return &linkT{id: nextLinkId(), variable: vart, loopDepth: block.loop.depth()}
}

// Connect the links at the end of this block to those at the starts of
// the next ones.

func (block *regBlockT) connectNext() {
	for _, next := range block.next {
		for _, vart := range sortedVars(maps.Keys(next.liveIn)) {
			from := block.loop.link(vart)
			if from == nil {
				from = block.endLinks[vart]
			}
			to := next.loop.link(vart)
			if to == nil {
				to = next.liveLinks[vart].link
			}
			// They are the same if this is within a loop that does not
			// reference the variable, and a loop may have several exits to
			// the same block.
			if from != to && !slices.Contains(from.ends, to) {
				joinLinks(from, to)
			}
		}
	}
}

// If the block ends with a jump, connect the links of the jump's arguments
// to those of the outputs of the JumpLambda it jumps to.

func (alloc *allocatorT) connectJump(block *regBlockT) {
	for i, argument := range block.jumpArgs {
		// The output may not be used.
		output := block.next[0].outputLink(i)
		if argument != nil && output != nil {
			end := block.endLinks[argument]
			joinLinks(end, output)
			// The output's value may come only from constants, which are not in
			// chains.  Searches from constants have the lowest priority, so
			// this has a search of its own.
			if argument.constant() != nil && !slices.Contains(alloc.rootLinks, end) {
				Push(&alloc.rootLinks, end)
			}
		}
	}
}

// The link for the i'th output of a JumpLambda, or nil if it isn't used.
func (block *regBlockT) outputLink(i int) *linkT {
	liveLink := block.liveLinks[block.start.Outputs[i]]
	if liveLink == nil {
		return nil
	}
	return liveLink.link
}

// The first input is the jump target.
func findJumpArgs(jump *CallNodeT, specs []*RegUseSpecT) []*VariableT {
	args := make([]*VariableT, len(jump.Inputs)-1)
	for i := range args {
		if specs[i+1] != nil {
			args[i] = jump.Inputs[i+1].(*ReferenceNodeT).Variable
		}
	}
	return args
}

func sortedVars(vars iter.Seq[*VariableT]) []*VariableT {
	return slices.SortedFunc(vars, func(x, y *VariableT) int { return x.Id - y.Id })
}

// The specs for inputs that get anchors, which are those that are not in
// fixed registers.
func anchoredSpecs(specs []*RegUseSpecT) []*RegUseSpecT {
	result := make([]*RegUseSpecT, len(specs))
	for i, spec := range specs {
		if spec != nil && spec.Fixed == nil {
			result[i] = spec
		}
	}
	return result
}

// A call may have more than one reference to a variable, so we
// collect the uses of each variable in a call's inputs.  These are
// in the order in which the variables first appear.

type callInputT struct {
	variable    *VariableT
	class       *RegisterClassT
	phaseOffset int   // maximum phase offset of all uses
	argIndexes  []int // indexes into the call's inputs
}

func getInputs(call *CallNodeT, specs []*RegUseSpecT) []*callInputT {
	result := []*callInputT{}
	for i, spec := range specs {
		if spec == nil {
			continue
		}
		input := call.Inputs[i]
		if !IsReferenceNode(input) {
			panic("got register spec for non-reference " + CallString(call))
		}
		vart := input.(*ReferenceNodeT).Variable
		index := slices.IndexFunc(result, func(input *callInputT) bool {
			return input.variable == vart
		})
		if index < 0 {
			Push(&result, &callInputT{vart, spec.Class, spec.PhaseOffset, []int{i}})
		} else {
			callInput := result[index]
			callInput.phaseOffset = max(callInput.phaseOffset, spec.PhaseOffset)
			Push(&callInput.argIndexes, i)
		}
	}
	return result
}

func (alloc *allocatorT) addAnchorLink(
	vart *VariableT,
	start int,
	end int,
	class *RegisterClassT,
	liveLink *liveLinkT,
) *linkT {
	link := &linkT{
		id:        nextLinkId(),
		variable:  vart,
		liveRange: liveRangeT{[]intervalT{{start, end}}},
	}
	// It's nil if vart is never referenced.
	if liveLink != nil {
		connectBelow(link, end, liveLink)
	}
	chain := newChain(link, class)
	chain.allowed = alloc.allowedRegisters(&link.liveRange, class)
	alloc.allChains.Add(chain)
	return link
}

func (alloc *allocatorT) findClobbers(blocks []*regBlockT) {
	alloc.clobbers = map[int][]RegisterT{}
	for _, block := range blocks {
		for i, call := range block.calls() {
			primop, ok := call.Primop.(ClobbersRegistersT)
			if ok {
				alloc.clobbers[block.startIndex+2*i+1] = primop.ClobberedRegisters(call)
			}
		}
	}
}

// The registers in the class that are not clobbered anywhere in 'live'.
func (alloc *allocatorT) allowedRegisters(live *liveRangeT, class *RegisterClassT) registerSetT {
	allowed := class.newRegisterSet()
	for point, registers := range alloc.clobbers {
		if live.intervalConflicts(intervalT{point, point + 1}) {
			for _, register := range registers {
				_, found := class.registerIndex[register]
				if found {
					allowed = class.removeRegister(allowed, register)
				}
			}
		}
	}
	return allowed
}

// The value in the link is moved to or from the register.  It would be
// better if the link were in that register.  Those in deeper loops take
// precedence.
type preferenceT struct {
	link     *linkT
	register RegisterT
	weight   int
}

func (alloc *allocatorT) addPreference(block *regBlockT, link *linkT, register RegisterT) {
	Push(&alloc.preferences, preferenceT{link, register, block.loop.depth() + 1})
}

// Connect a link that ends at 'end' to the one below it.
func connectBelow(link *linkT, end int, liveLink *liveLinkT) {
	if liveLink.endIndex != end {
		liveLink.link.liveRange.add(intervalT{end, liveLink.endIndex})
	}
	joinLinks(link, liveLink.link)
}
