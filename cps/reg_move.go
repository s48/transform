// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Finding the moves, loads, and stores that are needed when connected
// links are in different chains or not in chains at all.
//
// A value that is not in a register at some point is in a slot in memory.
// It is stored in the slot when it is created and is loaded from there
// where a link that is not in a chain is followed by one that is.  Constants
// have no slots and are just loaded.

package cps

import (
	"maps"
	"slices"

	"github.com/s48/transform/util"
)

// What the back end needs to know, other than which registers are used
// for which variables.
type RegAllocationT struct {
	Moves    map[*CallNodeT]*RegMovesT
	NumSlots int
}

// The moves that have to happen at a call.  The moves in each slice are
// done in parallel.
type RegMovesT struct {
	Before []RegMoveT // done before the call
	// For jumps only, these are the jump itself.  They include moving the
	// arguments to wherever the JumpLambda's outputs are.  They come after
	// the ones in Before.
	Jump []RegMoveT
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
	blocks []*regBlockT
	// The link for each variable that is live at each program point.
	pointLinks []map[*VariableT]*linkT
	// Program points where each variable is live.
	varPoints map[*VariableT]util.SetT[int]
	slots     map[*VariableT]int // for variables that are in memory
	moves     map[*CallNodeT]*RegMovesT
}

func (alloc *allocatorT) findMoves(blocks []*regBlockT) *RegAllocationT {
	finder := &moveFinderT{
		blocks:     blocks,
		pointLinks: make([]map[*VariableT]*linkT, alloc.numProgramPoints),
		varPoints:  map[*VariableT]util.SetT[int]{},
		moves:      map[*CallNodeT]*RegMovesT{},
	}
	for i := range finder.pointLinks {
		finder.pointLinks[i] = map[*VariableT]*linkT{}
	}
	for _, link := range alloc.allLinks() {
		points := finder.varPoints[link.variable]
		if points == nil {
			points = util.NewSet[int]()
			finder.varPoints[link.variable] = points
		}
		for _, interval := range link.liveRange.intervals {
			for i := interval.start; i < interval.end; i++ {
				finder.pointLinks[i][link.variable] = link
				points.Add(i)
			}
		}
	}
	numSlots := finder.assignSlots(finder.findSlotGroups())
	for _, block := range blocks {
		finder.findBlockMoves(block)
	}
	return &RegAllocationT{finder.moves, numSlots}
}

func (alloc *allocatorT) allLinks() []*linkT {
	links := []*linkT{}
	seen := util.NewSet[*linkT]()
	add := func(link *linkT) {
		if !seen.Contains(link) {
			seen.Add(link)
			Push(&links, link)
		}
	}
	for _, chain := range alloc.sortedChains() {
		for _, link := range chain.links {
			add(link)
		}
	}
	for i := 0; i < len(links); i++ {
		for _, next := range slices.Concat(links[i].starts, links[i].ends) {
			add(next)
		}
	}
	return links
}

//----------------------------------------------------------------
// A slot holds values and not variables.  If a JumpLambda's output is in
// memory then, if possible, the arguments that are passed to it use the
// same slot.  Then nothing needs to be done at the jump and the store is
// moved to where the argument's value was created.  This isn't possible
// if the two have different values that are needed at the same time.

type slotGroupT struct {
	vars   []*VariableT
	points util.SetT[int] // where any of the variables are live
}

func (finder *moveFinderT) findSlotGroups() []*slotGroupT {
	// The arguments passed to JumpLambda outputs.
	arguments := map[*VariableT][]*VariableT{}
	for _, block := range finder.blocks {
		for i, argument := range block.jumpArgs {
			output := block.next[0].start.Outputs[i]
			if argument != nil && argument.constant() == nil &&
				finder.varPoints[output] != nil {
				arguments[output] = append(arguments[output], argument)
			}
		}
	}

	groups := map[*VariableT]*slotGroupT{}
	todo := []*VariableT{}
	addVar := func(vart *VariableT) {
		groups[vart] = &slotGroupT{[]*VariableT{vart}, maps.Clone(finder.varPoints[vart])}
		Push(&todo, vart)
	}
	for _, vart := range sortedVars(maps.Keys(finder.varPoints)) {
		if vart.constant() != nil {
			continue
		}
		for point := range finder.varPoints[vart] {
			if finder.pointLinks[point][vart].chain == nil {
				addVar(vart)
				break
			}
		}
	}
	for i := 0; i < len(todo); i++ {
		output := todo[i]
		for _, argument := range arguments[output] {
			group := groups[output]
			other := groups[argument]
			if other == group {
				continue
			}
			points := finder.varPoints[argument]
			if other != nil {
				points = other.points
			}
			if setsOverlap(group.points, points) {
				continue
			}
			if other == nil {
				addVar(argument)
				other = groups[argument]
			}
			group.points.AddSet(other.points)
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

func setsOverlap(x util.SetT[int], y util.SetT[int]) bool {
	if len(y) < len(x) {
		x, y = y, x
	}
	for i := range x {
		if y.Contains(i) {
			return true
		}
	}
	return false
}

// Groups that are not live at the same time can share a slot.  Returns
// the number of slots.
func (finder *moveFinderT) assignSlots(groups []*slotGroupT) int {
	finder.slots = map[*VariableT]int{}
	slotPoints := []util.SetT[int]{}
	for _, group := range groups {
		slot := slices.IndexFunc(slotPoints, func(points util.SetT[int]) bool {
			return !setsOverlap(points, group.points)
		})
		if slot < 0 {
			slot = len(slotPoints)
			Push(&slotPoints, util.NewSet[int]())
		}
		slotPoints[slot].AddSet(group.points)
		for _, vart := range group.vars {
			finder.slots[vart] = slot
		}
	}
	return len(slotPoints)
}

//----------------------------------------------------------------

func (finder *moveFinderT) callMoves(call *CallNodeT) *RegMovesT {
	moves := finder.moves[call]
	if moves == nil {
		moves = &RegMovesT{}
		finder.moves[call] = moves
	}
	return moves
}

func (finder *moveFinderT) addBefore(call *CallNodeT, moves []RegMoveT) {
	if len(moves) != 0 {
		callMoves := finder.callMoves(call)
		callMoves.Before = append(callMoves.Before, moves...)
	}
}

// Links only change between calls, or between blocks, so we can just look
// for any variable whose location changes there.
//
// If the next block is a JumpLambda then this one ends in a jump, and the
// moves are done there.  Otherwise the next block has no other
// predecessors and the moves are done before its first call.

func (finder *moveFinderT) findBlockMoves(block *regBlockT) {
	calls := block.calls()
	for i, call := range calls {
		point := block.startIndex + 2*i // early
		if i != 0 {
			live := util.NewSet[*VariableT]()
			for vart := range finder.pointLinks[point-1] {
				if finder.pointLinks[point][vart] != nil {
					live.Add(vart)
				}
			}
			finder.addBefore(call, finder.movesBetween(live, point-1, point))
		}
		stores := finder.findStores(block, i)
		if i != len(calls)-1 {
			finder.addBefore(calls[i+1], stores)
		} else {
			for _, next := range block.next {
				finder.addBefore(next.start, stores)
			}
		}
	}
	isJump := block.end.Primop.Name() == "jump"
	for _, next := range block.next {
		// This does not include the outputs of a JumpLambda, even if they are
		// also live at the end of this block.  They are getting new values.
		moves := finder.movesBetween(next.liveIn, block.endIndex-1, next.startIndex)
		if isJump {
			moves = append(moves, finder.findJumpMoves(block, next)...)
			if len(moves) != 0 {
				finder.callMoves(block.end).Jump = moves
			}
		} else {
			finder.addBefore(next.start, moves)
		}
	}
}

// Moves and loads for variables that are live at both program points.
// Sort the variables to get deterministic behavior.
func (finder *moveFinderT) movesBetween(vars util.SetT[*VariableT], from int, to int) []RegMoveT {
	moves := []RegMoveT{}
	for _, vart := range sortedVars(maps.Keys(vars)) {
		if finder.pointLinks[to][vart].chain != nil {
			moves = addMove(moves, finder.location(vart, from), finder.location(vart, to))
		}
	}
	return moves
}

// Stores for the outputs of the i'th call in the block.
func (finder *moveFinderT) findStores(block *regBlockT, i int) []RegMoveT {
	call := block.calls()[i]
	stores := []RegMoveT{}
	if call.CallType == JumpLambda {
		return stores // done by the jump
	}
	for j, spec := range block.outputSpecs[i] {
		if spec != nil {
			vart := call.Outputs[j]
			slot, found := finder.slots[vart]
			if found {
				register := vart.definition.chain.root().Register
				stores = addMove(stores, RegLocationT{Register: register}, RegLocationT{Slot: slot})
			}
		}
	}
	return stores
}

// The outputs get their values from the arguments.  An output that is in
// memory at any point is put there by the jump, if it isn't already.
func (finder *moveFinderT) findJumpMoves(block *regBlockT, next *regBlockT) []RegMoveT {
	moves := []RegMoveT{}
	for i, argument := range block.jumpArgs {
		output := next.start.Outputs[i]
		link := finder.pointLinks[next.startIndex][output]
		if argument == nil || link == nil {
			continue
		}
		from := finder.location(argument, block.endIndex-1)
		if link.chain != nil {
			moves = addMove(moves, from, finder.location(output, next.startIndex))
		}
		slot, found := finder.slots[output]
		argumentSlot, argumentFound := finder.slots[argument]
		// The argument's slot may be the same without being in the same group,
		// but it still has the value.
		if found && !(argumentFound && argumentSlot == slot) {
			moves = addMove(moves, from, RegLocationT{Slot: slot})
		}
	}
	return moves
}

func (finder *moveFinderT) location(vart *VariableT, point int) RegLocationT {
	link := finder.pointLinks[point][vart]
	if link.chain != nil {
		return RegLocationT{Register: link.chain.root().Register}
	}
	constant := vart.constant()
	if constant != nil {
		return RegLocationT{Constant: constant}
	}
	return RegLocationT{Slot: finder.slots[vart]}
}

func addMove(moves []RegMoveT, from RegLocationT, to RegLocationT) []RegMoveT {
	if from == to {
		return moves
	}
	return append(moves, RegMoveT{from, to})
}
