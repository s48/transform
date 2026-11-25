// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package cps

import (
	"math/rand"
	"slices"
	"testing"
)

// Put every link in its own chain and assign registers greedily, in a
// random order, so that values move around as much as possible.
func TestMovesRandom(t *testing.T) {
	setTestRegisters(60)
	count := 0
	for seed := range 1000 {
		random := rand.New(rand.NewSource(int64(seed)))
		blocks := orderBlocks(randomTestBlocks(random, 10, 5, seed%2 == 0)[0])
		alloc := newTestAllocator(blocks)
		alloc.makeLinks(blocks)
		for link := range allTestLinks(alloc) {
			if link.chain == nil {
				alloc.allChains.Add(newChain(link, testClass))
			}
		}
		alloc.startMerge()
		chains := alloc.sortedChains()
		random.Shuffle(len(chains), func(i, j int) {
			chains[i], chains[j] = chains[j], chains[i]
		})
		for _, chain := range chains {
			available := testClass.newRegisterSet()
			for other := range chain.conflicts {
				if other.Register != nil {
					available = testClass.removeRegister(available, other.Register)
				}
			}
			chain.Register = testClass.firstRegister(available)
		}
		checkAllocation(t, alloc)
		moves := alloc.findMoves(blocks)
		for _, callMoves := range moves {
			count += len(callMoves.Before) + len(callMoves.Jump)
		}
		for range 5 {
			simulate(t, random, blocks[0], moves, 60)
		}
	}
	if count < 1000 {
		t.Errorf("only %d moves", count)
	}
}

// A value that is in one register before a call, another during it, and a
// third after it, and the same for the edges to and from a conditional.
func TestMovePlacement(t *testing.T) {
	setTestRegisters(10)
	x := &VariableT{Name: "x", Id: 1}
	xs := []*VariableT{x}
	blocks := makeTestBlocks([][]int{{1, 2}, {}, {}})
	blocks[0].addTestCall(nil, EarlyRegUse, xs, LateRegUse)
	blocks[0].addTestCall(xs, EarlyRegUse, nil, LateRegUse)
	blocks[0].addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	blocks[1].addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	blocks[1].addTestCall(xs, EarlyRegUse, nil, LateRegUse)
	blocks[2].addTestCall(xs, EarlyRegUse, nil, LateRegUse)
	alloc := newTestAllocator(blocks)
	alloc.makeLinks(blocks)
	for _, chain := range alloc.sortedChains() {
		chain.Register = testClass.registers[0]
	}
	setRegister := func(link *linkT, i int) RegisterT {
		if link.chain == nil {
			alloc.allChains.Add(newChain(link, testClass))
		}
		link.chain.Register = testClass.registers[i]
		return link.chain.Register
	}
	definition := setRegister(x.definition, 1)
	use := setRegister(x.uses[blocks[0].calls()[1].Inputs[0]], 2)
	end := setRegister(blocks[0].endLinks[x], 3)
	top := setRegister(blocks[1].liveLinks[x].link, 4)
	// Contains no program points, as the use is in the first call.
	setRegister(blocks[2].liveLinks[x].link, 5)
	use1 := setRegister(x.uses[blocks[1].end.Inputs[0]], 6)
	use2 := setRegister(x.uses[blocks[2].end.Inputs[0]], 7)

	moves := alloc.findMoves(blocks)
	tests := []struct {
		call *CallNodeT
		move RegMoveT
	}{
		{blocks[0].calls()[1], RegMoveT{definition, use}},
		{blocks[0].end, RegMoveT{use, end}},
		{blocks[1].start, RegMoveT{end, top}},
		{blocks[1].end, RegMoveT{top, use1}},
		{blocks[2].start, RegMoveT{end, use2}},
	}
	for i, test := range tests {
		callMoves := moves[test.call]
		if callMoves == nil || len(callMoves.Jump) != 0 ||
			!slices.Equal(callMoves.Before, []RegMoveT{test.move}) {
			t.Errorf("wrong moves for test %d", i)
		}
	}
	if len(moves) != len(tests) {
		t.Errorf("moves at %d calls, expected %d", len(moves), len(tests))
	}
}
