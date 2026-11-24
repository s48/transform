// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Register allocation version 3.
//
// This allocates registers to links between uses.
// Every anchor must be assigned a register.
// Every link must be assigned a location.

package cps

import (
	"fmt"
	"maps"
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
		if seen.Contains(link) {
			fmt.Printf("%s -> %d\n", indent, link.id)
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
	startIndex int // index of 'start' within the total call ordering
	endIndex   int // index after 'end' within the total call ordering
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
	endIndex  int         // The end of the current interval being scanned.
	link      *linkT      // The following link.
	liveRange liveRangeT  // The live range between endIndex and where link starts.
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

	// This includes early, middle, and late points for each CPS call in
	// the program.  Equal to three times the number of CPS calls.
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

	blocks := []*regBlockT{}
	proc := top
	todo := util.StackT[*regBlockT]{}
	todo.Push(proc.Block.(*regBlockT))
	for 0 < todo.Len() {
		block := todo.Pop()
		if !block.seen {
			block.seen = true
			blocks = append(blocks, block)
			for _, next := range block.next {
				todo.Push(next)
			}
		}
	}

	index := 0
	for _, block := range blocks {
		block.startIndex = index
		index += block.callCount * 2 // early, late
		block.endIndex = index
	}

	alloc.numProgramPoints = index * 2
	for i := len(blocks) - 1; 0 <= i; i-- {
		//fmt.Printf(" %s_%d block %d\n", alloc.procs[procIndex].Name, alloc.procs[procIndex].Id, i)
		alloc.findLiveRanges(blocks[i].start)
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

func (alloc *allocatorT) findLiveRanges(top *CallNodeT) {
	block := top.Block.(*regBlockT)
	fmt.Printf("block %s_%d [%d, %d]\n", block.start.Name, block.start.Id, block.startIndex, block.endIndex)
	liveLinks := map[*VariableT]map[*linkT]*liveLinkT{}
	for _, next := range block.next {
		for vart, liveLink := range next.liveLinks {
			links := liveLinks[vart]
			if links == nil {
				liveLinks[vart] = map[*linkT]*liveLinkT{liveLink.link: liveLink}
			} else {
				have := links[liveLink.link]
				if have == nil {
					links[liveLink.link] = liveLink
				} else {
					have.liveRange = *have.liveRange.union(&liveLink.liveRange)
				}
			}
		}
	}
	block.liveLinks = map[*VariableT]*liveLinkT{}
	for vart, liveLinks := range liveLinks {
		links := slices.Collect(maps.Values(liveLinks))
		if len(links) == 1 {
			// All paths lead to a single use.
			liveLink := links[0]
			block.liveLinks[vart] = &liveLinkT{
				endIndex: block.endIndex,
				link: liveLink.link,
				liveRange: *liveLink.liveRange.clone(),
			}
		} else {
			// Make a new link that connects all possible next uses.
			newLink := &linkT{id: nextLinkId(), variable: vart}
			for _, liveLink := range links {
				joinLinks(newLink, liveLink.link)
			}
			block.liveLinks[vart] = &liveLinkT{endIndex: block.endIndex, link: newLink}
		}
	}

	callIndex := block.callCount - 1
	lateIndex := block.endIndex
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
			block.liveLinks[vart] = &liveLinkT{endIndex: start, link: link}
		}
		callIndex -= 1
		lateIndex -= 2
	}

	for _, liveLink := range block.liveLinks {
		liveLink.liveRange.add(intervalT{block.startIndex, liveLink.endIndex})
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
			liveLink.liveRange.add(intervalT{end, liveLink.endIndex})
		}
		connectLink := &linkT{
			id: nextLinkId(),
			variable: vart,
			liveRange: liveLink.liveRange,
		}
		joinLinks(connectLink, liveLink.link)
		joinLinks(link, connectLink)
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
