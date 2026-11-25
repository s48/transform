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
	Moves  map[*CallNodeT]*RegMovesT
	Frames map[*CallNodeT]*RegFrameT // for each procedure
}

type RegFrameT struct {
	NumSlots  int         // slots in memory
	Registers []RegisterT // all registers assigned in the procedure
}

// The result for a single procedure.
type procAllocationT struct {
	Moves     map[*CallNodeT]*RegMovesT
	NumSlots  int
	Registers []RegisterT
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
	blocks []*regBlockT
	// The link for each variable that is live at each program point.
	pointLinks []map[*VariableT]*linkT
	// Program points where each variable is live.
	varPoints map[*VariableT]util.SetT[int]
	slots     map[*VariableT]int // for variables that are in memory
	// Values that are in fixed registers at the point where they are created.
	fixedOutputs map[int]map[*VariableT]RegisterT
	moves        map[*CallNodeT]*RegMovesT
}

func (alloc *allocatorT) findMoves(blocks []*regBlockT) *procAllocationT {
	finder := &moveFinderT{
		blocks:       blocks,
		pointLinks:   make([]map[*VariableT]*linkT, alloc.numProgramPoints),
		varPoints:    map[*VariableT]util.SetT[int]{},
		fixedOutputs: map[int]map[*VariableT]RegisterT{},
		moves:        map[*CallNodeT]*RegMovesT{},
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
		for i, call := range block.calls() {
			for j, spec := range block.outputSpecs[i] {
				if spec != nil && spec.Fixed != nil && call.CallType != JumpLambda {
					point := block.startIndex + 2*i + 1 // where moves out of it start
					if finder.fixedOutputs[point] == nil {
						finder.fixedOutputs[point] = map[*VariableT]RegisterT{}
					}
					finder.fixedOutputs[point][call.Outputs[j]] = spec.Fixed
				}
			}
		}
	}
	for _, block := range blocks {
		finder.findBlockMoves(block)
	}
	registers := []RegisterT{}
	for _, chain := range alloc.sortedChains() {
		if !slices.Contains(registers, chain.Register) {
			Push(&registers, chain.Register)
		}
	}
	slices.SortFunc(registers, func(x, y RegisterT) int { return x.Number() - y.Number() })
	return &procAllocationT{finder.moves, numSlots, registers}
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
	// Some values never get to a chain.
	for _, link := range alloc.rootLinks {
		add(link)
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
		for _, move := range moves {
			callMoves.Before = addMove(callMoves.Before, move.From, move.To)
		}
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
			// Values created in fixed registers have no links where they are
			// created.
			for vart := range finder.fixedOutputs[point-1] {
				if finder.pointLinks[point][vart] != nil {
					live.Add(vart)
				}
			}
			finder.addBefore(call, finder.movesBetween(live, point-1, point))
		}
		stores := finder.findStores(call, block.outputSpecs[i])
		fixedMoves := []RegMoveT{}
		for j, spec := range block.inputSpecs[i] {
			if spec != nil && spec.Fixed != nil {
				vart := call.Inputs[j].(*ReferenceNodeT).Variable
				fixedMoves = addMove(fixedMoves, finder.location(vart, point), RegLocationT{Register: spec.Fixed})
			}
		}
		if len(fixedMoves) != 0 {
			moves := finder.callMoves(call)
			moves.At = append(moves.At, fixedMoves...)
		}
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
				callMoves := finder.callMoves(block.end)
				callMoves.At = append(callMoves.At, moves...)
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

// Stores for the outputs of a call.
func (finder *moveFinderT) findStores(call *CallNodeT, specs []*RegUseSpecT) []RegMoveT {
	moves := []RegMoveT{}
	if call.CallType == JumpLambda {
		return moves // done by the jump
	}
	for i, spec := range specs {
		vart := call.Outputs[i]
		if spec == nil || vart.definition == nil || vart.constant() != nil {
			continue
		}
		// A value in a fixed register is only there during the call.  It is
		// moved out by movesBetween().
		from := RegLocationT{Register: spec.Fixed}
		if spec.Fixed == nil {
			from.Register = vart.definition.chain.root().Register
		}
		slot, found := finder.slots[vart]
		if found {
			moves = addMove(moves, from, RegLocationT{Slot: slot})
		}
	}
	return moves
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
	fixed := finder.fixedOutputs[point][vart]
	if fixed != nil {
		return RegLocationT{Register: fixed}
	}
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
	if from == to || slices.Contains(moves, RegMoveT{from, to}) {
		return moves
	}
	return append(moves, RegMoveT{from, to})
}
