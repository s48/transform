// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Register allocation version 3.
//
// Registers will be assigned to 'chains'.  The initial set
// of chains are just the inputs and outputs of each call
// (ignoring those that do not need to be in registers).
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
// is considered to be outside the loop.  Jump arguments are connected to the outputs
// of the JumpLambda by links that contain no program points.  When
// all links have been added you can follow the links from a variable's
// definition to all of its references.  The combined live ranges of
// those links are the variable's live range.
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
// deeper ones.  Links in inner loops come before those in outer ones, as
// good allocation is more important there.  Within a loop, links from
// jump arguments to outputs come after all others.  They have no length
// and would otherwise come first, which can keep an argument that is
// live after the jump from being merged with the rest of its own
// variable.
//
// The algorithm progresses by removing the first search and extending
// it along its shallowest leaf.  If this reaches a chain, possibly the
// one it started from, then the path to it is made into a chain, merged
// with both of the chains it connects if possible, or with one or the
// other, or with neither.  The search for the upper chain, and for the
// path's chain if that is different, then start over.  The search for
// any chain that was merged into another is cancelled.  Any other
// search that comes across a link that is now in a chain also starts
// over.  Going down is sufficient to find all of the links, as every
// link has some chain above it.
//
// A path can be merged with a set of chains, which may be empty, if
// none of their live ranges overlap and doing so meets the
// neighbor-count criteria.  The neighbors of a chain are the chains
// whose live ranges overlap its own.  If there are N registers then
// a neighbor is significant if it has N or more neighbors itself, with
// all of these counted as they will be after the merge.  The result
// must either have fewer than N significant neighbors (Briggs) or have
// all of its significant neighbors already be neighbors of one of the
// chains being merged (George).  If no merge is possible then something needs to be
// spilled, which is not implemented.  The criteria are conservative, so
// it may be that no spill was actually required.
//
// Once all links are in chains they are assigned registers using the
// usual graph coloring algorithm, which the criteria ensure will
// succeed.  Moves then need to be inserted wherever a link in one chain
// connects to one in a chain with a different register.  The moves for
// jump arguments are done by the jump.  Other moves are not implemented.
//
// That should be enough to allocate registers for procedures where
// there are sufficient registers to avoid any spilling.  I would like to
// get that much working before addressing ones that require spilling.

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
	return vart.definition.chain.root().Register
}

func (vart *VariableT) ReferenceRegister(node NodeT) RegisterT {
	link := vart.uses[node]
	if link == nil {
		panic(fmt.Sprintf("No register for %s", node))
	}
	return link.chain.root().Register
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
	id         int       // for debugging
	variable   *VariableT
	starts     []*linkT
	ends       []*linkT
	liveRange  liveRangeT
	chain      *chainT   // if it is in one
	loopDepth  int       // depth of the innermost loop containing the link
}

var nextLinkIdx = -1

func nextLinkId () int {
	nextLinkIdx += 1
	return nextLinkIdx
}

func joinLinks(from *linkT, to *linkT) {
	Push(&to.starts, from)
	Push(&from.ends, to)
}

func printVarLinks(vart *VariableT) {
	link := vart.definition
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
	liveRange *liveRangeT      // All of the links' intervals combined.
	class     *RegisterClassT
	conflicts util.SetT[*chainT]
	search    *searchT         // for links below this, if there are any
	Register  RegisterT        // what gets assigned to this
	peer      *chainT
}

var nextChainIdx = -1

func nextChainId () int {
	nextChainIdx += 1
	return nextChainIdx
}

func newChain(link *linkT, class *RegisterClassT) *chainT {
	chain := &chainT{
		id: nextChainId(),
		class: class,
		liveRange: &liveRangeT{},
		conflicts: util.NewSet[*chainT](),
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
	chain.links = append(chain.links, other.links ...)
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

	seen       bool
	loop       *regLoopT            // innermost loop containing this block, if any
	liveIn     util.SetT[*VariableT] // variables live at the start of the block
	jumpLinks []*linkT              // links for jump arguments at end
	liveLinks map[*VariableT]*liveLinkT // when done these are for the start of the block
	endLinks  map[*VariableT]*linkT     // links live at the end of the block
	inputSpecs  [][]*RegUseSpecT // cached for each call in the block
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
		for _, spec := range inputs {
			if spec != nil && spec.Class.Name == "r" {
				panic(fmt.Sprintf("bad spec from call %s", call))
			}
		}
		for _, spec := range outputs {
			if spec != nil && spec.Class.Name == "r" {
				panic(fmt.Sprintf("bad spec from call %s", call))
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
				// -1 because we don't need the jump target.
				block.jumpLinks = make([]*linkT, len(end.Inputs) - 1)
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
	// The chains that are live at each program point.
	chainPoints []util.SetT[*chainT]
	searchQueue *util.PriorityQueueT[*searchT]
}

func AllocateRegisters(top *CallNodeT, classes ...*RegisterClassT) {
	makeVarsForLiterals()
	allocator := &allocatorT{
		allVars: util.NewSet[*VariableT](),
		allChains: util.NewSet[*chainT](),
	}
	PpCps(top)
	allocator.allocate(top, classes)
}

func (alloc *allocatorT) allocate(top *CallNodeT, classes []*RegisterClassT) {
	top.SetFlag(1)
	FindBasicBlocks[*regBlockT](top, makeRegBlock)
	blocks := orderBlocks(top.Block.(*regBlockT))
	index := 0
	for _, block := range blocks {
		block.startIndex = index
		index += block.callCount * 2 // early, late
		block.endIndex = index
	}

	alloc.numProgramPoints = index
	alloc.makeLinks(blocks)

	// Sort the variables to get deterministic behavior.
	for _, vart := range sortedVars(maps.Keys(alloc.allVars)) {
		printVarLinks(vart)
	}

	alloc.mergeChains()
	for _, class := range classes {
		alloc.colorChains(class)
	}
	moves := alloc.findMoves()
	if len(moves) != 0 {
		link := moves[0][0]
		panic(fmt.Sprintf("register allocation does not insert moves yet, %d needed, first is for %s at link %d",
			len(moves), link.variable, link.id))
	}
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
	findLiveIn(blocks)
	makeLoopLinks(blocks)
	for _, block := range slices.Backward(blocks) {
		alloc.findLiveRanges(block.start)
	}
	// These are done last because with loops a block's next block may be
	// processed after the block.
	for _, block := range blocks {
		block.connectNext()
		block.connectJump()
	}
}

func (alloc *allocatorT) findLiveRanges(top *CallNodeT) {
	block := top.Block.(*regBlockT)
	fmt.Printf("block %s_%d [%d, %d)\n", block.start.Name, block.start.Id, block.startIndex, block.endIndex)
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
	for call := block.end; 0 <= callIndex ; call = call.parent {
		for i, spec := range block.outputSpecs[callIndex] {
			if spec == nil {
				continue
			}
			vart := call.Outputs[i]
			alloc.allVars.Add(vart)
			start := lateIndex + spec.PhaseOffset
			end := lateIndex + 1 // inclusive -> exclusive

			link := alloc.addAnchorLink(vart, start, end, spec.Class, block.liveLinks[vart])
			vart.definition = link
			delete(block.liveLinks, vart)
		}

		for _, input := range getInputs(call, block.inputSpecs[callIndex]) {
			vart := input.variable
			start := lateIndex + EarlyRegUse
			end := lateIndex + input.phaseOffset + 1 // +1 for inclusive to exclusive
			liveLink := block.liveLinks[vart]
			link := alloc.addAnchorLink(vart, start, end, input.class, liveLink)
			for _, index := range input.argIndexes {
				vart.addUse(call.Inputs[index], link)
				if call.Primop.Name() == "jump" {
					// -1 because we don't need the jump target
					block.jumpLinks[index - 1] = link
				}
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

// If the block ends with a jump, connect the jump's arguments to the
// outputs of the JumpLambda it jumps to.  The connecting links contain
// no program points.

func (block *regBlockT) connectJump() {
	if block.end.Primop.Name() != "jump" {
		return
	}
	target := CalledLambda(block.end)
	for i, argument := range block.jumpLinks {
		// Either can be nil if it is not in a register.
		output := target.Outputs[i].definition
		if argument == nil || output == nil {
			continue
		}
		connectLink := block.makeLink(argument.variable)
		connectLink.loopDepth = commonLoop(block, target.Block.(*regBlockT)).depth()
		joinLinks(argument, connectLink)
		joinLinks(connectLink, output)
	}
}

func sortedVars(vars iter.Seq[*VariableT]) []*VariableT {
	return slices.SortedFunc(vars, func(x, y *VariableT) int { return x.Id - y.Id })
}

// A call may have more than one reference to a variable, so we
// collect the uses of each variable in a call's inputs.  These are
// in the order in which the variables first appear.

type callInputT struct {
	variable    *VariableT
	class       *RegisterClassT
	phaseOffset int   // maximum phase offset of all uses
	argIndexes  []int  // indexes into the call's inputs
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
		id: nextLinkId(),
		variable: vart,
		liveRange: liveRangeT{[]intervalT{{start, end}}},
	}
	// It's nil if vart is never referenced.
	if liveLink != nil {
		if liveLink.endIndex != end {
			liveLink.link.liveRange.add(intervalT{end, liveLink.endIndex})
		}
		joinLinks(link, liveLink.link)
	}
	alloc.allChains.Add(newChain(link, class))
	return link
}
