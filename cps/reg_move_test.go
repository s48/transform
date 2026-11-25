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
		for _, link := range alloc.allLinks() {
			// And some are left in memory.
			if link.chain == nil && random.Intn(4) < seed%5 {
				chain := newChain(link, testClass)
				chain.allowed = alloc.allowedRegisters(&link.liveRange, testClass)
				alloc.allChains.Add(chain)
			}
		}
		alloc.startMerge()
		chains := alloc.sortedChains()
		random.Shuffle(len(chains), func(i, j int) {
			chains[i], chains[j] = chains[j], chains[i]
		})
		for _, chain := range chains {
			available := chain.allowed
			for other := range chain.conflicts {
				if other.Register != nil {
					available = testClass.removeRegister(available, other.Register)
				}
			}
			chain.Register = testClass.firstRegister(available)
		}
		checkAllocation(t, alloc)
		moves := alloc.findMoves(blocks).Moves
		for _, callMoves := range moves {
			count += len(callMoves.Before) + len(callMoves.At)
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
	setRegister := func(link *linkT, i int) RegLocationT {
		if link.chain == nil {
			alloc.allChains.Add(newChain(link, testClass))
		}
		link.chain.Register = testClass.registers[i]
		return RegLocationT{Register: link.chain.Register}
	}
	definition := setRegister(x.definition, 1)
	use := setRegister(x.uses[blocks[0].calls()[1].Inputs[0]], 2)
	end := setRegister(blocks[0].endLinks[x], 3)
	top := setRegister(blocks[1].liveLinks[x].link, 4)
	// Contains no program points, as the use is in the first call.
	setRegister(blocks[2].liveLinks[x].link, 5)
	use1 := setRegister(x.uses[blocks[1].end.Inputs[0]], 6)
	use2 := setRegister(x.uses[blocks[2].end.Inputs[0]], 7)

	moves := alloc.findMoves(blocks).Moves
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
		if callMoves == nil || len(callMoves.At) != 0 ||
			!slices.Equal(callMoves.Before, []RegMoveT{test.move}) {
			t.Errorf("wrong moves for test %d", i)
		}
	}
	if len(moves) != len(tests) {
		t.Errorf("moves at %d calls, expected %d", len(moves), len(tests))
	}
}

// A value that is passed around a loop without being used there, and for
// which there is no register, is stored once before the loop and loaded
// after it.  It is bound to 'a' outside the loop and 'q' inside.
func TestSpillAroundLoop(t *testing.T) {
	setTestRegisters(2)
	vars := testVars("a q x y")
	a, q, x, y := vars[0], vars[1], vars[2], vars[3]
	xy := []*VariableT{x, y}
	qs := []*VariableT{q}

	entry := makeRegBlock()
	entry.addTestCall(nil, EarlyRegUse, []*VariableT{a}, LateRegUse)
	entry.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	entry.addTestCall([]*VariableT{a}, EarlyRegUse, nil, LateRegUse)
	loop := makeRegBlock()
	loop.addTestCall(nil, EarlyRegUse, qs, LateRegUse)
	loop.addTestCall(nil, EarlyRegUse, xy, LateRegUse)
	loop.addTestCall(xy, EarlyRegUse, nil, LateRegUse)
	back := makeRegBlock()
	back.addTestCall(qs, EarlyRegUse, nil, LateRegUse)
	exit := makeRegBlock()
	exit.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	exit.addTestCall(qs, EarlyRegUse, nil, LateRegUse)
	entry.makeTestJump(loop)
	back.makeTestJump(loop)
	loop.addNext(back)
	loop.addNext(exit)

	blocks := orderBlocks(entry)
	alloc := allocateTestBlocks(blocks)
	checkAllocation(t, alloc)
	allocation := alloc.findMoves(blocks)
	if allocation.NumSlots != 1 {
		t.Errorf("%d slots, expected 1", allocation.NumSlots)
	}
	slot := RegLocationT{}
	store := RegMoveT{RegLocationT{Register: a.Register()}, slot}
	load := RegMoveT{slot, RegLocationT{Register: q.ReferenceRegister(exit.end.Inputs[0])}}
	for _, block := range blocks {
		for i, call := range block.calls() {
			moves := allocation.Moves[call]
			if moves == nil {
				moves = &RegMovesT{}
			}
			if len(moves.At) != 0 {
				t.Errorf("there should be nothing to do at jumps")
			}
			expected := []RegMoveT{}
			if block == entry && i == 1 {
				expected = append(expected, store)
			} else if block == exit && len(moves.Before) != 0 {
				// It can be loaded at either call.
				expected = append(expected, load)
			}
			if !slices.Equal(moves.Before, expected) {
				t.Errorf("wrong moves %v", moves.Before)
			}
		}
	}
	for range 10 {
		simulate(t, rand.New(rand.NewSource(1)), entry, allocation.Moves, 20)
	}
}

// Around the loop p and q are only ever passed to each other.
func TestUnusedOutputs(t *testing.T) {
	vars := testVars("a p q")
	a, p, q := vars[0], vars[1], vars[2]
	entry := makeRegBlock()
	entry.addTestCall(nil, EarlyRegUse, []*VariableT{a}, LateRegUse)
	entry.addTestCall([]*VariableT{a, a}, EarlyRegUse, nil, LateRegUse)
	loop := makeRegBlock()
	loop.addTestCall(nil, EarlyRegUse, []*VariableT{p, q}, LateRegUse)
	loop.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	back := makeRegBlock()
	back.addTestCall([]*VariableT{q, p}, EarlyRegUse, nil, LateRegUse)
	exit := makeRegBlock()
	exit.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	entry.makeTestJump(loop)
	back.makeTestJump(loop)
	loop.addNext(back)
	loop.addNext(exit)
	blocks := orderBlocks(entry)
	alloc := newTestAllocator(blocks)
	alloc.makeLinks(blocks)
	if len(alloc.allLinks()) != 1 {
		t.Errorf("only a's definition should have a link")
	}

	// They are needed if either one is used.
	exit.addTestCall([]*VariableT{q}, EarlyRegUse, nil, LateRegUse)
	alloc = newTestAllocator(blocks)
	alloc.makeLinks(blocks)
	for _, vart := range []*VariableT{p, q} {
		if loop.liveLinks[vart] == nil || back.endLinks[vart] == nil {
			t.Errorf("%s should be live", vart.Name)
		}
	}
}

// Link a leads to b and c, b and c to d, and c also to e.
func TestSpillUp(t *testing.T) {
	setTestRegisters(2)
	vart := &VariableT{Name: "v"}
	links := make([]*linkT, 5)
	for i := range links {
		links[i] = &linkT{id: i, variable: vart}
	}
	a, b, c, d, e := links[0], links[1], links[2], links[3], links[4]
	top := newChain(&linkT{variable: vart}, testClass)
	joinLinks(top.links[0], a)
	joinLinks(a, b)
	joinLinks(a, c)
	joinLinks(b, d)
	joinLinks(c, d)
	joinLinks(c, e)
	expectSpilled := func(expected ...*linkT) {
		t.Helper()
		for _, link := range links {
			if link.spilled != slices.Contains(expected, link) {
				t.Errorf("link %d: spilled is %v", link.id, link.spilled)
			}
		}
	}
	alloc := &allocatorT{}
	alloc.spill(d)
	expectSpilled(d, b) // c may be used to get to e
	alloc.spill(e)
	expectSpilled(a, b, c, d, e)
	if top.links[0].spilled {
		t.Errorf("links in chains should not be spilled")
	}
}

// Parameter x arrives in a fixed register, is passed to a call, and is
// used after it along with the call's result.  Both have to be moved out
// of the fixed registers, and x into one for the call.
func TestFixedRegisters(t *testing.T) {
	setTestRegisters(4)
	vars := testVars("x y")
	x, y := vars[0], vars[1]
	block := makeRegBlock()
	block.addTestCall(nil, EarlyRegUse, []*VariableT{x}, LateRegUse)
	setTestFixed(block.outputSpecs[0])
	block.addTestCall([]*VariableT{x}, EarlyRegUse, []*VariableT{y}, LateRegUse)
	setTestFixed(block.inputSpecs[1])
	setTestFixed(block.outputSpecs[1])
	block.addTestCall([]*VariableT{x, y}, EarlyRegUse, nil, LateRegUse)
	alloc := allocateTestBlocks([]*regBlockT{block})
	checkAllocation(t, alloc)
	allocation := alloc.findMoves([]*regBlockT{block})
	calls := block.calls()
	fixed := RegLocationT{Register: testFixedRegisters[0]}
	xRegister := RegLocationT{Register: x.ReferenceRegister(calls[2].Inputs[0])}
	yRegister := RegLocationT{Register: y.ReferenceRegister(calls[2].Inputs[1])}
	expected := map[*CallNodeT]RegMovesT{
		calls[1]: {Before: []RegMoveT{{fixed, xRegister}}, At: []RegMoveT{{xRegister, fixed}}},
		calls[2]: {Before: []RegMoveT{{fixed, yRegister}}},
	}
	for _, call := range calls {
		moves := allocation.Moves[call]
		if moves == nil {
			moves = &RegMovesT{}
		}
		if !slices.Equal(moves.Before, expected[call].Before) || !slices.Equal(moves.At, expected[call].At) {
			t.Errorf("wrong moves %v", *moves)
		}
	}
	if allocation.NumSlots != 0 {
		t.Errorf("nothing should be spilled")
	}
	simulate(t, rand.New(rand.NewSource(1)), block, allocation.Moves, 1)
}

// A call's result that is only passed to another call is moved directly,
// or through a register, without using memory.
func TestFixedToFixed(t *testing.T) {
	setTestRegisters(4)
	vars := testVars("y")
	block := makeRegBlock()
	block.addTestCall(nil, EarlyRegUse, vars, LateRegUse)
	setTestFixed(block.outputSpecs[0])
	block.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	block.addTestCall(vars, EarlyRegUse, nil, LateRegUse)
	setTestFixed(block.inputSpecs[2])
	alloc := allocateTestBlocks([]*regBlockT{block})
	allocation := alloc.findMoves([]*regBlockT{block})
	if allocation.NumSlots != 0 {
		t.Errorf("y should not be in memory")
	}
	simulate(t, rand.New(rand.NewSource(1)), block, allocation.Moves, 1)
}
