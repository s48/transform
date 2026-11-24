// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Register allocation version 3.
//
// Registers will be assigned to 'chains'.  The initial set
// of chains are just the inputs and outputs of each call
// (ignoring those that do not need to be in registers).
// The can necessarily be assigned registers, as any single
// call is limited to the architectures registers.
// A chain consists of a set of connected links.
//
// A 'link' is a live range that could be assigned a register.
// A link has:
//   - The set of program points in its live range.
//   - 'Starts' which is a slice of links from which can receive a value.
//   - 'Ends' which is a slice of links to which it provides a value.
//   - A chain, if it has been assigned to one.
// Initially, the inputs and outputs of all calls have a chain
// with a single link that covers just that call.  These are
// connected by additional links, not initially in chains, that
// connect definitions and uses of variables.  For example, if
// variable X is defined in call A and has two uses, on in call
// B and the next in call C then we will get the following:
//  - Three links with anchors, one for each of the calls.
//  - Two connecting links without anchors, one between the
//    A and B anchor links and one between the B and C anchor
//    links.
//  - Thus the A anchor link will have no starts and one end,
//    the one at B will have one start and one end, and the
//    the one at C will have one end.
// Conditionals and jumps also connect links.  When all links have
// been added you can follow the links from a variable's definition to
// all of its references.  The combined live ranges of those links are
// the the variable's live range.
//
// The next step is to join the anchor-less links into 'paths', where
// each path contains all links that lead from one anchor to another.
// In the example above there would be two paths, each containing one
// of the connecting links.  In more complex cases a path may contain
// many links.
//
// Paths are assigned a priority based on a hueristic and kept in a
// priority queue.  The highest priorty path is taken off the queue
// and checked to see if it can be assigned a register.  This requires
// looking at the set of chains that its live range overlaps, called
// neighbors.  If there are N registers we can turn the path into a
// chain if it has fewer than N neighbors that have N-1 neighbors
// themselves.
//
// When converting a path to a chain we first see if it can be joined
// to either or both of the chains it connects without breaking the
// neighbor criteria listed above.
//
// After converting a path to a chain the links in the path need to be
// removed from any other paths that contain them.  Those paths are
// removed from the priority queue.  The portions of them that are not
// part of the new chain are then added back to the queue as new,
// shorter paths.  For example, if path has four links and the second
// link is in the new chain, then there are two new paths, the first
// containing the first link and the second containing the last two.
// These paths connect the new chain with the chains at the ends of
// the original path.
//
// Once all links are part of chain (assuming no spilling is required)
// registers can be assigned to them using the usual graph coloring
// algorithm.  Moves then need to be inserted wherever a link in one
// chain connects to one in another chain.
//
// That should be enough to allocate registers for loop-free procedures
// where there are sufficient register to avoid any spilling.  I would
// like to get that much working before addressing procedures with
// loops and/or ones that require spilling.

package cps

import (
	"fmt"
	"slices"
	"sort"

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
	paths      []*pathT
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

func (link *linkT) addPath(path *pathT) {
	Push(&link.paths, path)
}

func (link *linkT) removePath(path *pathT) {
	i := slices.Index(link.paths, path)
	if i < 0 {
		return
	}
	paths := link.paths
	last := len(paths) - 1
	paths[i] = paths[last]
    link.paths = paths[:last]
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
	previous   []*regBlockT

	seen       bool

	jumpLinks []*linkT              // links for jump arguments at end
	liveLinks map[*VariableT]*liveLinkT
	inputSpecs  [][]*RegUseSpecT // cached for each call in the block
	outputSpecs [][]*RegUseSpecT

	// Only in the blocks of procedure nodes.
	blocks     []*regBlockT // all the blocks in this procedure
	callsTo    util.SetT[*CallNodeT]
	calledFrom util.SetT[*CallNodeT]
	// How many registers of each class are used in this procedure.
	regCounts   map[*RegisterClassT]int
	//liveBundles util.SetT[*bundleT]
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

// Finds the bound and live variables in the block.

func (block *regBlockT) initialize(start *CallNodeT, end *CallNodeT) {
	block.start = start
	block.end = end
	if start.CallType == ProcLambda {
		block.callsTo = util.NewSet[*CallNodeT]()
		block.calledFrom = util.NewSet[*CallNodeT]()
		block.regCounts = map[*RegisterClassT]int{}
	}
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
	next := rawNext.(*regBlockT)
	block.next = append(block.next, next)
	next.previous = append(next.previous, block)
}

func (block *regBlockT) getEnd() *CallNodeT {
	return block.end
}

type allocatorT struct {
	procs []*CallNodeT
	allVars util.SetT[*VariableT]

	// This includes early and late points for each CPS call in the
	// program.  Equal to twice the number of CPS calls.
	numProgramPoints int

	allChains util.SetT[*chainT]
	coloringQueue *util.PriorityQueueT[*pathT]
	chainPoints []util.SetT[*chainT]
	chainPointDiffs []util.SetT[*chainT]
	anchorLinks map[any]*linkT

	// Procedure calls, indexed by program point.
	procCalls map[int]*regBlockT
}

func AllocateRegisters(top *CallNodeT, classes ...*RegisterClassT) {
	makeVarsForLiterals()
	allocator := &allocatorT{
		procCalls: map[int]*regBlockT{},
		allVars: util.NewSet[*VariableT](),
		allChains: util.NewSet[*chainT](),
		anchorLinks: map[any]*linkT{},
	}
	PpCps(top)
	allocator.allocate(top, classes)
}

func (alloc *allocatorT) allocate(top *CallNodeT, classes []*RegisterClassT) {
	top.SetFlag(1)
	bbs := FindBasicBlocks[*regBlockT](top, makeRegBlock)
	top.Block.(*regBlockT).blocks = bbs

	blocks := orderBlocks(top.Block.(*regBlockT))
	index := 0
	for _, block := range blocks {
		block.startIndex = index
		index += block.callCount * 2 // early, late
		block.endIndex = index
	}

	alloc.numProgramPoints = index
	for i := len(blocks) - 1; 0 <= i; i-- {
		//fmt.Printf(" %s_%d block %d\n", alloc.procs[procIndex].Name, alloc.procs[procIndex].Id, i)
		alloc.findLiveRanges(blocks[i].start)
	}
	// This is done last because with loops a jump's target may be
	// processed after the jump.
	for _, block := range blocks {
		block.connectJump()
	}

	vars := alloc.allVars.Members()
	// Sort the variables to get deterministic behavior.
	sort.Slice(vars, func(i int, j int) bool {
		return vars[i].Id < vars[j].Id
	})

	for _, vart := range vars {
		printVarLinks(vart)
	}
	/*
	for _, class := range classes {
		alloc.allocateRegisterClass(class)
	}
	*/
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

func (alloc *allocatorT) findLiveRanges(top *CallNodeT) {
	block := top.Block.(*regBlockT)
	fmt.Printf("block %s_%d [%d, %d)\n", block.start.Name, block.start.Id, block.startIndex, block.endIndex)
	// Links do not cross block boundaries.  Each variable that is live
	// at the end of the block gets a new link, connected to the variable's
	// link at the start of each next block.
	block.liveLinks = map[*VariableT]*liveLinkT{}
	for _, next := range block.next {
		for vart, nextLiveLink := range next.liveLinks {
			liveLink := block.liveLinks[vart]
			if liveLink == nil {
				link := &linkT{id: nextLinkId(), variable: vart}
				liveLink = &liveLinkT{endIndex: block.endIndex, link: link}
				block.liveLinks[vart] = liveLink
			}
			joinLinks(liveLink.link, nextLiveLink.link)
		}
	}

	callIndex := block.callCount - 1
	lateIndex := block.endIndex - 1
	for call := block.end; 0 <= callIndex ; call = call.parent {
		// fmt.Printf("call %d(%s) %d lateIndex %d\n",
		//     call.Id, call.Primop.Name(), len(call.Outputs), lateIndex)

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

		for vart, input := range getInputs(call, block.inputSpecs[callIndex]) {
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
			connectLink := &linkT{id: nextLinkId(), variable: vart}
			joinLinks(connectLink, link)
			block.liveLinks[vart] = &liveLinkT{endIndex: start, link: connectLink}
		}
		callIndex -= 1
		lateIndex -= 2
	}

	for _, liveLink := range block.liveLinks {
		// They are equal if the variable is used early in the first call.
		if block.startIndex < liveLink.endIndex {
			liveLink.link.liveRange.add(intervalT{block.startIndex, liveLink.endIndex})
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
		connectLink := &linkT{id: nextLinkId(), variable: argument.variable}
		joinLinks(argument, connectLink)
		joinLinks(connectLink, output)
	}
}

// A call may have more than one reference to a variable, so we
// collect the uses of each variable in a call's inputs.

type callInputT struct {
	class       *RegisterClassT
	phaseOffset int   // maximum phase offset of all uses
	argIndexes  []int  // indexes into the call's inputs
}

func getInputs(call *CallNodeT, specs []*RegUseSpecT) map[*VariableT]*callInputT {
	result := map[*VariableT]*callInputT{}
	for i, spec := range specs {
		if spec == nil {
			continue
		}
		input := call.Inputs[i]
		if !IsReferenceNode(input) {
			panic("got register spec for non-reference " + CallString(call))
		}
		vart := input.(*ReferenceNodeT).Variable
		callInput := result[vart]
		if callInput == nil {
			result[vart] = &callInputT{spec.Class, spec.PhaseOffset, []int{i}}
		} else {
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

//----------------------------------------------------------------

type pathT struct {
	id int
	class *RegisterClassT
	from *linkT
	to *linkT
	links []*linkT
	length int // sum of program points for the links
	loopDepth int
}

var nextPathIdx = -1

func nextPathId () int {
	nextPathIdx += 1
	return nextPathIdx
}

//----------------------------------------------------------------

func getCalledProc(call *CallNodeT) *CallNodeT {
	switch primop := call.Primop.(type) {
	case CallsProcPrimopT:
		return primop.CalledProc(call)
	default:
		return nil
	}
}
