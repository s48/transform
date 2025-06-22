// Copyright 2025 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Common subexpression elimination.
//
// This is intended as a step towards full elminiation of partial
// redundancies.

package cps

import (
	"fmt"
	"math/big"
)

func init() { fmt.Sprintf("") }

func Cse(top *CallNodeT) {
	exprs := &cseStateT{
		map[PrimopT]int{},
		map[string]int{},
		map[[6]int]int{}}
	// PpCps(top)
	blocks := FindBasicBlocks[*cseBlockT](top, makeBlock)
	exprs.findAvailable(blocks[0], newCallMap(nil))
	for _, block := range blocks {
		block.Start.Block = nil
	}
}

func (state *cseStateT) findAvailable(block *cseBlockT, calls *callMapT) {
	call := block.Start
	if call.IsLambda() {
		if IsProcLambdaNode(call) {
			fmt.Printf("CSE for %s_%d\n", call.Name, call.Id)
		}
		call = call.Next[0]
	}
	for call != block.End {
		next := call.Next[0]
		for _, input := range call.Inputs {
			if IsCallNode(input) {
				block := input.(*CallNodeT).Block
				// How to handle proc lambdas?
				if block != nil {
					state.findAvailable(block.(*cseBlockT), newCallMap(calls))
				}
			}
		}
		exprCode := state.addCall(call)
		if exprCode < 0 {
			// do nothing
		} else if calls.have(exprCode) {
			original := calls.lookup(exprCode)
			fmt.Printf("CSE: %s\n", CallString(call))
			removeDuplicate(original, call)
		} else {
			calls.add(exprCode, call)
		}
		call = next
	}
	for _, next := range call.Next {
		state.findAvailable(next.Block.(*cseBlockT), newCallMap(calls))
	}
}

func removeDuplicate(original *CallNodeT, copy *CallNodeT) {
	for i, output := range copy.Outputs {
		newVar := original.Outputs[i]
		refs := output.Refs
		output.Refs = nil
		for _, ref := range refs {
			ReplaceInput(ref, MakeReferenceNode(newVar))
		}
	}
	RemoveCall(copy)
}

//----------------------------------------------------------------

type cseBlockT struct {
	Start    *CallNodeT
	End      *CallNodeT
	Next     []*cseBlockT
	Previous []*cseBlockT
}

func makeBlock() *cseBlockT {
	return &cseBlockT{}
}

func (block *cseBlockT) initialize(start *CallNodeT, end *CallNodeT) {
	block.Start = start
	block.End = end
}

func (block *cseBlockT) addNext(rawNext BasicBlockT) {
	next := rawNext.(*cseBlockT)
	block.Next = append(block.Next, next)
	next.Previous = append(next.Previous, block)
}

func (block *cseBlockT) getEnd() *CallNodeT {
	return block.End
}

// We keep a table of calls

type cseStateT struct {
	primops   map[PrimopT]int
	constants map[string]int
	exprsMap  map[[6]int]int
}

type callMapT struct {
	parent *callMapT
	bitMap *big.Int
	calls  map[int]*CallNodeT
}

func newCallMap(parent *callMapT) *callMapT {
	bitMap := new(big.Int)
	if parent != nil {
		bitMap.Set(parent.bitMap)
	}
	return &callMapT{parent, bitMap, map[int]*CallNodeT{}}
}

func (calls *callMapT) have(exprCode int) bool {
	return calls.bitMap.Bit(exprCode) == 1
}

func (calls *callMapT) add(exprCode int, call *CallNodeT) {
	calls.bitMap.SetBit(calls.bitMap, exprCode, 1)
	calls.calls[exprCode] = call
}

func (calls *callMapT) lookup(exprCode int) *CallNodeT {
	for ; calls != nil; calls = calls.parent {
		call := calls.calls[exprCode]
		if call != nil {
			return call
		}
	}
	return nil
}

func (state *cseStateT) addCall(call *CallNodeT) int {
	if 5 < len(call.Inputs) {
		return -1
	}
	if call.Primop.SideEffects() {
		return -1
	}
	if Any(IsCallNode, call.Inputs) {
		return -1
	}
	var key [6]int
	primopCode, found := state.primops[call.Primop]
	if !found {
		primopCode = len(state.primops)
		state.primops[call.Primop] = primopCode
	}
	key[0] = primopCode
	for i, input := range call.Inputs {
		key[i+1] = state.encodeInput(input)
	}
	exprCode, found := state.exprsMap[key]
	if !found {
		exprCode = len(state.exprsMap)
		state.exprsMap[key] = exprCode
	}
	for _, output := range call.Outputs {
		if output != nil {
			output.Flags["cse"] = exprCode
		}
	}
	return exprCode
}

func (state *cseStateT) encodeInput(rawInput NodeT) int {
	switch input := rawInput.(type) {
	case *LiteralNodeT:
		str := input.Value.ExactString()
		code, found := state.constants[str]
		if !found {
			code = len(state.constants)
			state.constants[str] = code
		}
		return code * 3
	case *ReferenceNodeT:
		vart := input.Variable
		exprCode, found := vart.Flags["cse"]
		if found {
			return exprCode.(int)*3 + 1
		} else {
			return vart.Id*3 + 2
		}
	default:
		panic("CSE got unexpected input node type")
	}
}
