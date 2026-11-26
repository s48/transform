// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Finding the moves, loads, and stores that are needed when connected
// links are in different chains or not in chains at all.
//
// A link's location is its source, its chain's register, its constant, or
// its variable's slot.  A move or load is needed where a link in a chain
// follows one with a different location, at the joint between them.
// Joints between blocks are done for each edge, as a joint at the start
// of a JumpLambda may be for several jumps.  A value that is ever in
// memory is stored when it is created.

package cps

import (
	"fmt"
	"maps"
	"slices"

	"github.com/s48/transform/util"
)

// What the back end needs to know, other than which registers are used
// for which variables.
type RegAllocationT struct {
	Moves  RegMoveMapT
	Frames map[*CallNodeT]*RegFrameT // for each procedure
}

type RegMoveMapT map[*CallNodeT]*RegMovesT

type RegFrameT struct {
	NumSlots  int         // slots in memory
	Registers []RegisterT // all registers assigned in the procedure
}

// The moves that have to happen at a call.  The moves in each slice are
// done in parallel.
type RegMovesT struct {
	Before []RegMoveT // done before the call
	// These are part of the call itself, and come after the ones in Before.
	// For jumps they include moving the arguments to wherever the
	// JumpLambda's outputs are.  For other calls they move values to fixed
	// registers.
	At []RegMoveT
}

type RegMoveT struct {
	From RegLocationT
	To   RegLocationT
}

// A register or, if that is nil, a constant or, if that is also nil, a
// slot in memory.  Values are never moved to constants.
type RegLocationT struct {
	Register RegisterT
	Constant NodeT
	Slot     int
}

type moveFinderT struct {
	blocks     []*regBlockT
	pointCalls []*CallNodeT // the call at each pair of program points
	// For each variable that may be in a slot, the others that are live at
	// the same time.
	varConflicts map[*VariableT]util.SetT[*VariableT]
	moves        RegMoveMapT
}

func (alloc *allocatorT) findMoves(blocks []*regBlockT) (RegMoveMapT, *RegFrameT) {
	finder := &moveFinderT{
		blocks:     blocks,
		pointCalls: make([]*CallNodeT, alloc.numProgramPoints/2),
		moves:      RegMoveMapT{},
	}
	for _, block := range blocks {
		copy(finder.pointCalls[block.startIndex/2:], block.calls)
	}
	arguments := finder.jumpArguments()
	// The variables that may be in slots.
	candidates := util.NewSet(alloc.inMemory...)
	for _, args := range arguments {
		candidates.Add(args...)
	}
	slotLinks, joints, fixedUseLinks := alloc.selectLinks(candidates)
	groups := finder.findSlotGroups(slotLinks, candidates, alloc.inMemory, arguments)
	numSlots := finder.assignSlots(groups)

	for _, link := range joints {
		finder.joinMoves(link)
	}
	for _, link := range fixedUseLinks {
		for _, use := range link.fixedUses {
			finder.addMoves(use.call, true, RegMoveT{finder.location(link), RegLocationT{Register: use.register}})
		}
	}
	for _, block := range blocks {
		finder.findStores(block)
		finder.findEdgeMoves(block)
	}

	registers := []RegisterT{}
	for _, inputs := range alloc.classes {
		for chain := range inputs.chains {
			if !slices.Contains(registers, chain.Register) {
				Push(&registers, chain.Register)
			}
		}
	}
	slices.SortFunc(registers, func(x, y RegisterT) int { return x.Number() - y.Number() })
	return finder.moves, &RegFrameT{numSlots, registers}
}

// Sorts out the links that findMoves needs, in one pass over all of them.
// The first result is the links of the variables that may be in slots,
// in no particular order.  The others may need moves, and are sorted by
// id to get deterministic behavior.  These are the links in chains that
// start where a link in a different chain, or not in one, ends, and the
// links with fixed uses.
func (alloc *allocatorT) selectLinks(candidates util.SetT[*VariableT]) ([]*linkT, []*linkT, []*linkT) {
	slotLinks := []*linkT{}
	joints := []*linkT{}
	fixedUseLinks := []*linkT{}
	selectLink := func(link *linkT) {
		if candidates.Contains(link.variable) {
			Push(&slotLinks, link)
		}
		root := link.chain.root()
		if root != nil && slices.ContainsFunc(link.starts, func(start *linkT) bool {
			return start.chain.root() != root
		}) {
			Push(&joints, link)
		}
		if len(link.fixedUses) != 0 {
			Push(&fixedUseLinks, link)
		}
	}
	for _, inputs := range alloc.classes {
		for chain := range inputs.chains {
			for _, link := range chain.links {
				selectLink(link)
			}
		}
	}
	for link := range alloc.unchainedLinks {
		selectLink(link)
	}
	byId := func(x, y *linkT) int { return x.id - y.id }
	slices.SortFunc(joints, byId)
	slices.SortFunc(fixedUseLinks, byId)
	return slotLinks, joints, fixedUseLinks
}

//----------------------------------------------------------------
// A slot holds values and not variables.  If a JumpLambda's output is in
// memory then, if possible, the arguments that are passed to it use the
// same slot.  Then nothing needs to be done at the jump and the store is
// moved to where the argument's value was created.  This isn't possible
// if the two have different values that are needed at the same time.

type slotGroupT struct {
	vars      []*VariableT
	conflicts util.SetT[*VariableT] // variables live at the same time as any of these
}

// The arguments passed to each JumpLambda output, other than constants.
func (finder *moveFinderT) jumpArguments() map[*VariableT][]*VariableT {
	arguments := map[*VariableT][]*VariableT{}
	for _, block := range finder.blocks {
		for i, argument := range block.jumpArgs {
			output := block.next[0].start.Outputs[i]
			if argument != nil && argument.constant == nil &&
				block.next[0].outputLink(i) != nil {
				arguments[output] = append(arguments[output], argument)
			}
		}
	}
	return arguments
}

// Groups the variables in memory with the arguments passed to them, where
// possible.  'links' are the links of the candidates, which are those
// variables and the arguments.
func (finder *moveFinderT) findSlotGroups(
	links []*linkT,
	candidates util.SetT[*VariableT],
	inMemory []*VariableT,
	arguments map[*VariableT][]*VariableT,
) []*slotGroupT {
	finder.findConflicts(links, candidates)

	groups := map[*VariableT]*slotGroupT{}
	todo := []*VariableT{}
	addVar := func(vart *VariableT) {
		groups[vart] = &slotGroupT{[]*VariableT{vart}, maps.Clone(finder.varConflicts[vart])}
		Push(&todo, vart)
	}
	for _, vart := range inMemory {
		addVar(vart)
	}
	for i := 0; i < len(todo); i++ {
		output := todo[i]
		for _, argument := range arguments[output] {
			group := groups[output]
			other := groups[argument]
			if other == group {
				continue
			}
			vars := []*VariableT{argument}
			if other != nil {
				vars = other.vars
			}
			if slices.ContainsFunc(vars, group.conflicts.Contains) {
				continue
			}
			if other == nil {
				addVar(argument)
				other = groups[argument]
			}
			group.conflicts.AddSet(other.conflicts)
			for _, vart := range other.vars {
				groups[vart] = group
				Push(&group.vars, vart)
			}
		}
	}

	result := []*slotGroupT{}
	for _, vart := range todo {
		if !slices.Contains(result, groups[vart]) {
			Push(&result, groups[vart])
		}
	}
	return result
}

// One of a variable's live intervals.
type varIntervalT struct {
	vart     *VariableT
	interval intervalT
}

// Finds which of the variables are live at the same time, by going through
// the starts and ends of their links' intervals in order.  An interval's
// end is exclusive, so at each program point the ends are done before the
// starts.
func (finder *moveFinderT) findConflicts(links []*linkT, vars util.SetT[*VariableT]) {
	finder.varConflicts = map[*VariableT]util.SetT[*VariableT]{}
	for vart := range vars {
		finder.varConflicts[vart] = util.NewSet[*VariableT]()
	}
	starts := []varIntervalT{}
	for _, link := range links {
		for _, interval := range link.liveRange.intervals {
			Push(&starts, varIntervalT{link.variable, interval})
		}
	}
	ends := slices.Clone(starts)
	slices.SortFunc(starts, func(x, y varIntervalT) int { return x.interval.start - y.interval.start })
	slices.SortFunc(ends, func(x, y varIntervalT) int { return x.interval.end - y.interval.end })

	liveVars := util.NewSet[*VariableT]()
	endIndex := 0
	for _, start := range starts {
		for ends[endIndex].interval.end <= start.interval.start {
			liveVars.Remove(ends[endIndex].vart)
			endIndex += 1
		}
		vart := start.vart
		finder.varConflicts[vart].AddSet(liveVars)
		for other := range liveVars {
			finder.varConflicts[other].Add(vart)
		}
		liveVars.Add(vart)
	}
}

// Groups that are not live at the same time can share a slot.  Returns
// the number of slots.
func (finder *moveFinderT) assignSlots(groups []*slotGroupT) int {
	slotConflicts := []util.SetT[*VariableT]{}
	for _, group := range groups {
		slot := slices.IndexFunc(slotConflicts, func(conflicts util.SetT[*VariableT]) bool {
			return !slices.ContainsFunc(group.vars, conflicts.Contains)
		})
		if slot < 0 {
			slot = len(slotConflicts)
			Push(&slotConflicts, util.NewSet[*VariableT]())
		}
		slotConflicts[slot].AddSet(group.conflicts)
		for _, vart := range group.vars {
			vart.hasSlot = true
			vart.slot = slot
		}
	}
	return len(slotConflicts)
}

//----------------------------------------------------------------

// Adds the moves to those done before the call or, if 'at' is true, as
// part of it.
func (finder *moveFinderT) addMoves(call *CallNodeT, at bool, moves ...RegMoveT) {
	for _, move := range moves {
		if move.From == move.To {
			continue
		}
		callMoves := finder.moves[call]
		if callMoves == nil {
			callMoves = &RegMovesT{}
			finder.moves[call] = callMoves
		}
		if at {
			callMoves.At = addMove(callMoves.At, move.From, move.To)
		} else {
			callMoves.Before = addMove(callMoves.Before, move.From, move.To)
		}
	}
}

// The moves into a link in a chain from the links above it, when the
// joint is within a block.  Those at the start of a block are done by
// findEdgeMoves.
func (finder *moveFinderT) joinMoves(link *linkT) {
	intervals := link.liveRange.intervals
	point := intervals[len(intervals)-1].start
	call := finder.pointCalls[point/2]
	if point%2 == 0 && call.Block != nil {
		return // at the start of a block
	}
	to := finder.location(link)
	for _, start := range link.starts {
		from := finder.location(start)
		if from == to {
			continue
		}
		if point%2 != 0 {
			// It follows an anchor that ends at the call's early point.
			panic(fmt.Sprintf("link %d needs a move within a call", link.id))
		}
		finder.addMoves(call, false, RegMoveT{from, to})
	}
}

// The link for a variable at the end of a block, and at the start.
func (block *regBlockT) endLink(vart *VariableT) *linkT {
	link := block.loop.link(vart)
	if link == nil {
		link = block.endLinks[vart]
	}
	return link
}

func (block *regBlockT) startLink(vart *VariableT) *linkT {
	link := block.loop.link(vart)
	if link == nil {
		link = block.liveLinks[vart].link
	}
	return link
}

// The moves at the joints between this block and the following ones.  If
// the next block is a JumpLambda then this one ends in a jump, and the
// moves are done there.  Otherwise the next block has no other
// predecessors and the moves are done before its first call.
func (finder *moveFinderT) findEdgeMoves(block *regBlockT) {
	isJump := block.end.Primop.Name() == "jump"
	for _, next := range block.next {
		moves := []RegMoveT{}
		// This does not include the outputs of a JumpLambda, even if they are
		// also live at the end of this block.  They are getting new values.
		// Sort the variables to get deterministic behavior.
		for _, vart := range sortedVars(maps.Keys(next.liveIn)) {
			from := block.endLink(vart)
			to := next.startLink(vart)
			if from == to {
				continue // a link around a loop
			}
			if to.chain != nil {
				moves = addMove(moves, finder.location(from), finder.location(to))
			}
		}
		if isJump {
			finder.addMoves(block.end, true, append(moves, finder.findJumpMoves(block, next)...)...)
		} else {
			finder.addMoves(next.start, false, moves...)
		}
	}
}

// Stores for the outputs of the block's calls, done before the next call.
func (finder *moveFinderT) findStores(block *regBlockT) {
	for i, call := range block.calls {
		if call.CallType == JumpLambda {
			continue // done by the jumps
		}
		stores := []RegMoveT{}
		for j, spec := range block.outputSpecs[i] {
			vart := call.Outputs[j]
			if spec != nil && vart.definition != nil && vart.hasSlot {
				Push(&stores, RegMoveT{finder.location(vart.definition), RegLocationT{Slot: vart.slot}})
			}
		}
		if i != len(block.calls)-1 {
			finder.addMoves(block.calls[i+1], false, stores...)
		} else {
			for _, next := range block.next {
				finder.addMoves(next.start, false, stores...)
			}
		}
	}
}

// The outputs get their values from the arguments.  An output that is in
// memory at any point is put there by the jump, if it isn't already.
func (finder *moveFinderT) findJumpMoves(block *regBlockT, next *regBlockT) []RegMoveT {
	moves := []RegMoveT{}
	for i, argument := range block.jumpArgs {
		output := next.start.Outputs[i]
		link := next.outputLink(i)
		if argument == nil || link == nil {
			continue
		}
		from := finder.location(block.endLinks[argument])
		if link.chain != nil {
			moves = addMove(moves, from, finder.location(link))
		}
		// The argument's slot may be the same without being in the same group,
		// but it still has the value.
		if output.hasSlot && !(argument.hasSlot && argument.slot == output.slot) {
			moves = addMove(moves, from, RegLocationT{Slot: output.slot})
		}
	}
	return moves
}

func (finder *moveFinderT) location(link *linkT) RegLocationT {
	if link.source != nil {
		return *link.source
	}
	if link.chain != nil {
		return RegLocationT{Register: link.chain.root().Register}
	}
	constant := link.variable.constant
	if constant != nil {
		return RegLocationT{Constant: constant}
	}
	return RegLocationT{Slot: link.variable.slot}
}

func addMove(moves []RegMoveT, from RegLocationT, to RegLocationT) []RegMoveT {
	if from == to || slices.Contains(moves, RegMoveT{from, to}) {
		return moves
	}
	return append(moves, RegMoveT{from, to})
}
