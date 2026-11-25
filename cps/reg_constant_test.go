// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package cps

import (
	"math/rand"
	"slices"
	"testing"
)

// Constant c is bound first and used last.  In between there are two
// other variables, which need two registers.
func constantTestBlock() (*regBlockT, *VariableT) {
	vars := testVars("c x y")
	xy := vars[1:]
	block := makeRegBlock()
	block.addTestConstant(vars[0])
	block.addTestCall(nil, EarlyRegUse, xy, LateRegUse)
	block.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	block.addTestCall(xy, EarlyRegUse, nil, LateRegUse)
	block.addTestCall(vars[:1], EarlyRegUse, nil, LateRegUse)
	return block, vars[0]
}

func TestConstantInRegister(t *testing.T) {
	setTestRegisters(3)
	block, c := constantTestBlock()
	alloc := allocateTestBlocks([]*regBlockT{block})
	checkAllocation(t, alloc)
	allocation := alloc.findMoves([]*regBlockT{block})
	if c.Register() == nil || c.Register() != c.ReferenceRegister(block.end.Inputs[0]) {
		t.Errorf("constant should be in one register")
	}
	if len(allocation.Moves) != 0 || allocation.NumSlots != 0 {
		t.Errorf("there should be no moves")
	}
}

// Without a register for it the constant is loaded just where it is used.
func TestConstantLoaded(t *testing.T) {
	setTestRegisters(2)
	block, c := constantTestBlock()
	alloc := allocateTestBlocks([]*regBlockT{block})
	checkAllocation(t, alloc)
	allocation := alloc.findMoves([]*regBlockT{block})
	if c.Register() != nil {
		t.Errorf("constant should not be loaded where it is bound")
	}
	use := c.ReferenceRegister(block.end.Inputs[0])
	expected := []RegMoveT{{RegLocationT{Constant: c.constant()}, RegLocationT{Register: use}}}
	moves := allocation.Moves[block.end]
	if allocation.NumSlots != 0 || len(allocation.Moves) != 1 || moves == nil ||
		!slices.Equal(moves.Before, expected) {
		t.Errorf("wrong moves")
	}
	simulate(t, rand.New(rand.NewSource(1)), block, allocation.Moves, 1)
}

// Output p's value only comes from constants.
func TestConstantArguments(t *testing.T) {
	setTestRegisters(3)
	vars := testVars("c d p x")
	c, d, p, x := vars[0], vars[1], vars[2], vars[3]
	blocks := []*regBlockT{makeRegBlock(), makeRegBlock(), makeRegBlock(), makeRegBlock()}
	blocks[0].addTestCall(nil, EarlyRegUse, []*VariableT{x}, LateRegUse)
	blocks[1].addTestConstant(c)
	blocks[1].addTestCall([]*VariableT{c}, EarlyRegUse, nil, LateRegUse)
	blocks[2].addTestConstant(d)
	blocks[2].addTestCall([]*VariableT{d}, EarlyRegUse, nil, LateRegUse)
	blocks[3].addTestCall(nil, EarlyRegUse, []*VariableT{p}, LateRegUse)
	blocks[3].addTestCall([]*VariableT{x}, EarlyRegUse, nil, LateRegUse)
	blocks[3].addTestCall([]*VariableT{p}, EarlyRegUse, nil, LateRegUse)
	blocks[0].addNext(blocks[1])
	blocks[0].addNext(blocks[2])
	blocks[1].makeTestJump(blocks[3])
	blocks[2].makeTestJump(blocks[3])
	alloc := allocateTestBlocks(blocks)
	checkAllocation(t, alloc)
	allocation := alloc.findMoves(blocks)
	if len(allocation.Moves) != 0 || allocation.NumSlots != 0 {
		t.Errorf("the constants should be loaded directly into p's register")
	}
	if c.Register() == nil || c.Register() != p.ReferenceRegister(blocks[3].end.Inputs[0]) ||
		c.Register() != d.Register() {
		t.Errorf("c, d and p should be in the same register")
	}
	random := rand.New(rand.NewSource(1))
	for range 10 {
		simulate(t, random, blocks[0], allocation.Moves, 10)
	}
}

// There is a register for only one of v and c while x is live.  c's path
// is shorter, but v gets the register because c is a constant.
func TestConstantPriority(t *testing.T) {
	setTestRegisters(2)
	vars := testVars("v c x")
	block := makeRegBlock()
	block.addTestCall(nil, EarlyRegUse, vars[:1], LateRegUse)
	block.addTestConstant(vars[1])
	block.addTestCall(nil, EarlyRegUse, vars[2:], LateRegUse)
	block.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	block.addTestCall(vars[2:], EarlyRegUse, nil, LateRegUse)
	block.addTestCall(vars[1:2], EarlyRegUse, nil, LateRegUse)
	block.addTestCall(vars[:1], EarlyRegUse, nil, LateRegUse)
	alloc := allocateTestBlocks([]*regBlockT{block})
	checkAllocation(t, alloc)
	allocation := alloc.findMoves([]*regBlockT{block})
	if allocation.NumSlots != 0 {
		t.Errorf("v should not be spilled")
	}
	simulate(t, rand.New(rand.NewSource(1)), block, allocation.Moves, 1)
}
