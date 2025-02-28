// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Code simplification.

package cps

import (
	"fmt"
)

func simplifyCall(call *CallNodeT) {
	call.Primop.Simplify(call)
}

// The simplifier for primops that have nothing specific to look for.
// We just simplify the inputs and then the continuations.

func DefaultSimplify(call *CallNodeT) {
	simplifyInputs(call)
	SimplifyNext(call)
}

func simplifyInputs(call *CallNodeT) {
	for i := range call.Inputs {
		for !call.Inputs[i].IsSimplified() {
			rawInput := call.Inputs[i]
			rawInput.SetIsSimplified(true)
			switch input := rawInput.(type) {
			case *CallNodeT:
				simplifyCall(input)
			case *LiteralNodeT:
				// nothing
			case *ReferenceNodeT:
				// nothing
			default:
				panic(fmt.Sprintf("ppCpsValue got funny node %+v", rawInput))
			}
		}
	}
}

func SimplifyNext(call *CallNodeT) {
	for i := range call.Next {
		for !call.Next[i].IsSimplified() {
			next := call.Next[i]
			next.SetIsSimplified(true)
			simplifyCall(next)

			next = call.Next[i]
			if next.IsSimplified() && !next.Primop.SideEffects() && len(next.Next) == 1 &&
				Every(func(vart *VariableT) bool { return len(vart.Refs) == 0 },
					next.Outputs) {
				RemoveCall(next)
			}
		}
	}
	call.SetIsSimplified(true)
}

//----------------------------------------------------------------

func SimplifyLet(call *CallNodeT) {
	if len(call.Outputs) != len(call.Inputs) {
		panic("wrong number of inputs in call " + CallString(call))
	}
	if len(call.Inputs) == 0 {
		RemoveCall(call)
	} else {
		simplifyInputs(call)
		// Check for unused inputs to LET-bound lambdas.
		for {
			call.SetIsSimplified(true)
			SimplifyNext(call)
			if substituteLetInputs(call, false) {
				RemoveCall(call)
				break
			} else if substituteJoinInputs(call) {
				// do nothing
			} else if call.IsSimplified() {
				break
			}
		}
	}
}

// Removed inputs to a lambda-node in call position.
// If any inputs are actually removed
// REMOVE-NULL-INPUTS shortens the input vector.

func substituteLetInputs(call *CallNodeT, quick bool) bool {
	CheckNode(TopLambda)
	inputs := call.Inputs
	removed := 0
	for i, vart := range call.Outputs {
		val := inputs[i]
		if substituteValForVar(vart, val, quick) {
			Substitute(vart, val, true)
			removed += 1
		}
	}
	if removed == len(call.Outputs) {
		return true // nothing left
	}
	if 0 < removed {
		RemoveUnusedOutputs(call)
		RemoveNullInputs(call, len(call.Inputs)-removed)
	}
	return false
}

func substituteValForVar(vart *VariableT, rawVal NodeT, quick bool) bool {
	switch val := rawVal.(type) {
	case *LiteralNodeT:
		return true
	case *ReferenceNodeT:
		return true
	case *CallNodeT:
		return !quick && substituteLambdaForVar(vart, val)
	}
	return false
}

func substituteLambdaForVar(vart *VariableT, node *CallNodeT) bool {
	if !Every(IsCalledRef, vart.Refs) {
		return false
	}
	// Duplicate single-call calls (jumps and returns).
	if node.CallType == JumpLambda && len(node.Next[0].Next) == 0 {
		return true
	}
	return len(vart.Refs) == 1
}

//----------------------------------------------------------------
// If the jump target is a lambda this is just a let.

func SimplifyJump(call *CallNodeT) {
	if IsCallNode(call.Inputs[0]) {
		target := call.Inputs[0].(*CallNodeT)
		target.CallType = CallExit
		target.Primop = LookupPrimop("let")
		target.Inputs = append(target.Inputs, make([]NodeT, len(call.Inputs)-1)...)
		for i := 1; i < len(call.Inputs); i++ {
			AttachInput(target, i-1, DetachInput(call.Inputs[i]))
		}
		ReplaceNext(call, DetachInput(target).(*CallNodeT))
	} else {
		DefaultSimplify(call)
	}
}

func SimplifyProcCall(call *CallNodeT) {
	if IsCallNode(call.Inputs[0]) {
		InlineProcedure(call, call.Inputs[0].(*CallNodeT))
	} else {
		DefaultSimplify(call)
	}
}

// Remove values whose vars are not referenced and substitute
// those that have only one reference.

func SimplifyLetrec(call *CallNodeT) {
	simplifyInputs(call)
	SimplifyNext(call)
	call.SetFlag(1)
	for {
		removed := 0
		for i, vart := range call.Outputs {
			if substituteLetrec(vart, call.Inputs[i].(*CallNodeT)) {
				removed += 1
			}
		}
		if removed == 0 {
			break
		}
		RemoveUnusedOutputs(call)
		RemoveNullInputs(call, len(call.Inputs)-removed)
	}
	call.SetFlag(0)
	if len(call.Outputs) == 0 {
		RemoveCall(call)
	}
}

func substituteLetrec(vart *VariableT, val *CallNodeT) bool {
	if len(vart.Refs) == 0 {
		Erase(DetachInput(val))
		return true
	} else if len(vart.Refs) == 1 {
		val.SetFlag(1)
		caller := markedAncestor(vart.Refs[0])
		val.SetFlag(0)
		DetachInput(val)
		if caller == val {
			Erase(DetachInput(val)) // only called by itself
		} else {
			ReplaceInput(vart.Refs[0], val)
		}
		return true
	} else if val.CallType == JumpLambda && len(val.Next[0].Next) == 0 ||
		vart.Flags["substitute"] != nil {
		Substitute(vart, val, true)
		return true
	}
	return false
}

//----------------------------------------------------------------
// Iteratively remove any unused inputs to jump lambdas.  This is
// a non-local transformation so it needs to be done outside of
// the normal simplification.
// If we do remove anything we have to simplify the program and
// go again, in case removing unused jump arguments caused other
// values to become unused.

func RemoveUnusedInputs(top *CallNodeT) {
	for {
		change := true
		for change {
			change = false
			for lambda, _ := range Lambdas {
				if lambda.CallType == JumpLambda &&
					removeUnusedJumpInputs(lambda) {
					change = true
				}
			}
		}
		if top.Next[0].simplified {
			// Nothing changes, so we're done.
			break
		}
		SimplifyNext(top)
	}
}

func removeUnusedJumpInputs(lambda *CallNodeT) bool {
	unused := []int{}
	for i, vart := range lambda.Outputs {
		if vart.IsUnused() {
			Push(&unused, i)
		}
	}
	if len(unused) == 0 {
		return false
	}
	RemoveUnusedOutputs(lambda)
	for _, ref := range lambdaBinding(lambda).Refs {
		call := ref.parent
		for _, i := range unused {
			Erase(DetachInput(call.Inputs[i+1]))
		}
		RemoveNullInputs(call, len(call.Inputs)-len(unused))
		MarkChanged(call)
	}
	return true
}

//----------------------------------------------------------------
// Checks the uses of the output of a MakeCell call.  If:
//  - There are none, then remove the call.
//  - There are two or more CellSets then give up.
//  - There are no CellSets, then panic (not a great solution)
//  - There is exactly one CellSet and all of the uses are
//    within it's scope then the CellSet becomes a Let and the
//    CellRef calls are elided.
// This gets rid of the majority of the cells in a program
// without the trouble of doing any flow analysis.

func SimplifyMakeCell(call *CallNodeT) {
	simplifyInputs(call)
	SimplifyNext(call)
	cellVar := call.Outputs[0]
	if len(cellVar.Refs) == 0 {
		RemoveCall(call)
		return
	}
	var cellSetCall *CallNodeT
	refCalls := []*CallNodeT{}
	for _, ref := range cellVar.Refs {
		call := ref.parent
		switch call.Primop.Name() {
		case "cellSet":
			if cellSetCall == nil {
				cellSetCall = call
			} else {
				return // set two or more times, nothing we can do
			}
		case "cellRef":
			refCalls = append(refCalls, call)
		default:
			panic("unexpected cell use")
		}
	}
	if cellSetCall == nil {
		PpCps(TopLambda)
		panic("cell is never set")
	}
	cellSetCall.parent.SetFlag(1)
	inScope := Every(func(ref *ReferenceNodeT) bool { return hasMarkedAncestor(ref) },
		cellVar.Refs)
	cellSetCall.parent.SetFlag(0)
	if inScope {
		valueVar := replaceCellSet(cellSetCall)
		for _, call := range refCalls {
			replaceCellRef(call, valueVar)
		}
	}
}

//   cellSet(cellRef, value)
// ->
//   let(value) -> valueVar

func replaceCellSet(call *CallNodeT) *VariableT {
	cellRef := call.Inputs[0]
	cellVar := cellRef.(*ReferenceNodeT).Variable
	value := DetachInput(call.Inputs[1])
	valueVar := MakeVariable(cellVar.Name, cellVar.Type)
	call.Outputs = []*VariableT{valueVar}
	valueVar.Binder = call
	call.Primop = LookupPrimop("let")
	Erase(DetachInput(cellRef))
	AttachInput(call, 0, value)
	call.Inputs = call.Inputs[0:1]
	MarkChanged(call)
	return valueVar
}

//   cellRef(cellVar) -> var
// ->
//   let(valueVar) -> var

func replaceCellRef(call *CallNodeT, valueVar *VariableT) {
	Erase(DetachInput(call.Inputs[0]))
	AttachInput(call, 0, MakeReferenceNode(valueVar))
	call.Primop = LookupPrimop("let")
	MarkChanged(call)
}

//----------------------------------------------------------------
// If the result of a boolean operator like == or < is used in an
// 'if' then replace the 'if' with a conditional version of the
// original boolean operator.
//    t := x < y
//    if t B C
// ->
//    if-< x y B C

func SimplifyBooleanOp(call *CallNodeT, condPrimop string, negate bool) {
	simplifyInputs(call)
	SimplifyNext(call)
	valueVar := call.Outputs[0]
	if len(valueVar.Refs) != 1 {
		return
	}
	ifCall := valueVar.Refs[0].parent
	if ifCall.Primop.Name() != "if" {
		return
	}

	Erase(DetachInput(valueVar.Refs[0]))
	AttachInput(ifCall, 0, DetachInput(call.Inputs[0]))
	for i, input := range call.Inputs[1:] {
		ifCall.Inputs = append(ifCall.Inputs, nil)
		AttachInput(ifCall, i+1, DetachInput(input))
	}
	if negate {
		temp := DetachNext(ifCall.Next[0])
		AttachNext(ifCall, DetachNext(ifCall.Next[1]), 0)
		AttachNext(ifCall, temp, 1)
	}
	ifCall.Primop = LookupPrimop(condPrimop)
	RemoveCall(call)
}

// Inline 'proc' as the procedured called at 'call'.
//
// Call "procCall" [procVar, input0, ...] [callOut0, ...] [callNext]
// Proc "procLambda" [] [procOut0, ...] [procNext]
// =>
// Call "let" [Proc, Input0, ...] [procOut0, ...] [procNext]
// Proc "jumpLambda" [] [callOut0, ...] [callNext]

func InlineProcedure(call *CallNodeT, proc *CallNodeT) {
	// Proc's returns become jumps now that the continuation is known.
	for _, ref := range proc.Outputs[0].Refs {
		ref.parent.Primop = LookupPrimop("jump")
	}
	proc.CallType = JumpLambda
	proc.Primop = LookupPrimop("jumpLambda")

	callNext := DetachNext(call.Next[0])
	procNext := DetachNext(proc.Next[0])
	AttachNext(call, procNext, 0)
	AttachNext(proc, callNext, 0)

	callOutputs := call.Outputs
	setOutputs(call, proc.Outputs)
	setOutputs(proc, callOutputs)

	if call.Inputs[0] != proc {
		ReplaceInput(call.Inputs[0], proc)
	}
	call.Primop = LookupPrimop("let")
	MarkChanged(call)
}

func setOutputs(call *CallNodeT, outputs []*VariableT) {
	call.Outputs = outputs
	for _, vart := range outputs {
		vart.Binder = call
	}
}
