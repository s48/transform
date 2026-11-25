// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Finding the register moves that are needed when connected links are in
// different chains.

package cps

import (
	"maps"
)

type RegMoveT struct {
	From RegisterT
	To   RegisterT
}

// The moves that have to happen at a call.  The moves in each slice are
// done in parallel.
type RegMovesT struct {
	Before []RegMoveT // done before the call
	// For jumps only, these are the jump itself.  They include moving the
	// arguments to the registers of the JumpLambda's outputs.  They come
	// after the ones in Before.
	Jump []RegMoveT
}

// Links only change between calls, or between blocks, so we can just look
// for any variable whose register changes there.
//
// If the next block is a lambda then this one ends in a jump, and the
// moves are done there.  Otherwise the next block has no other
// predecessors and the moves are done before its first call.

func (alloc *allocatorT) findMoves(blocks []*regBlockT) map[*CallNodeT]*RegMovesT {
	// The link for each variable that is live at each program point.
	pointLinks := make([]map[*VariableT]*linkT, alloc.numProgramPoints)
	for i := range pointLinks {
		pointLinks[i] = map[*VariableT]*linkT{}
	}
	for _, chain := range alloc.sortedChains() {
		for _, link := range chain.links {
			for _, interval := range link.liveRange.intervals {
				for i := interval.start; i < interval.end; i++ {
					pointLinks[i][link.variable] = link
				}
			}
		}
	}

	result := map[*CallNodeT]*RegMovesT{}
	getMoves := func(call *CallNodeT) *RegMovesT {
		moves := result[call]
		if moves == nil {
			moves = &RegMovesT{}
			result[call] = moves
		}
		return moves
	}
	// Variables live at both program points.  Sort the variables to get
	// deterministic behavior.
	movesBetween := func(from int, to int) []RegMoveT {
		moves := []RegMoveT{}
		for _, vart := range sortedVars(maps.Keys(pointLinks[to])) {
			fromLink := pointLinks[from][vart]
			if fromLink != nil {
				moves = addMove(moves, fromLink, pointLinks[to][vart])
			}
		}
		return moves
	}

	for _, block := range blocks {
		for i, call := range block.calls() {
			if i != 0 {
				index := block.startIndex + 2*i
				moves := movesBetween(index-1, index)
				if len(moves) != 0 {
					getMoves(call).Before = moves
				}
			}
		}
		isJump := block.end.Primop.Name() == "jump"
		for _, next := range block.next {
			moves := movesBetween(block.endIndex-1, next.startIndex)
			if isJump {
				target := CalledLambda(block.end)
				for i, argument := range block.jumpLinks {
					output := target.Outputs[i].definition
					if argument != nil && output != nil {
						moves = addMove(moves, argument, output)
					}
				}
			}
			if len(moves) == 0 {
				continue
			} else if isJump {
				getMoves(block.end).Jump = moves
			} else {
				getMoves(next.start).Before = moves
			}
		}
	}
	return result
}

func addMove(moves []RegMoveT, from *linkT, to *linkT) []RegMoveT {
	fromRegister := from.chain.root().Register
	toRegister := to.chain.root().Register
	if fromRegister == toRegister {
		return moves
	}
	return append(moves, RegMoveT{fromRegister, toRegister})
}
