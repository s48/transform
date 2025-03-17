// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// This implements a single code transformation that simplifies
// a common control-flow situation.  A traditional name for this
// is 'evaluation for effect'.
//
// For example, the CPS for this
//   if A && B { Body }
// is something like this, where 'join' is the continuation to
// 'A && B' and C is the continuation to the 'if' itself.
//
//   join := func (x0 bool) { if x0 { Body; C() } else { C() }}
//   x1 := A
//   if x1 {
//      join(true)
//   } else {
//      x2 := B
//      if x2 { join(true) } else { join(false) }
//   }
//
// The transformation done here eliminates the 'if' in the join
// continuation by splitting into one continuation for true and one
// for false.
//
//   joinTrue := func () { Body; C() }
//   joinFalse := func () { C() }
//   x1 := A
//   if x1 {
//      joinTrue()
//   } else {
//      x2 := B
//      if x2 { joinTrue() } else { joinFalse() }
//   }

package cps

import (
	"fmt"
)

func init() { fmt.Scanf("") } // appease the import gods

// Call joinSubstitute on all variable/value pairs.

func substituteJoinInputs(call *CallNodeT) bool {
	change := false
	for i, vart := range call.Outputs {
		input := call.Inputs[i]
		if IsCallNode(input) &&
			input.(*CallNodeT).CallType ==
				JumpLambda && joinSubstitute(vart, input.(*CallNodeT)) {

			change = true
		}
	}
	return change
}

// Check if the body of 'val' is a block ending in a conditional
// that tests 'val's variable.  If the block can be made small
// enough to be duplicated and 'var' is passed any constants we
// put the test's continuations in separate jump lambdas.  The
// calls with constants can then call the continuation directly
// and skip the conditional.
//
// This shows up when source conditionals use 'and' or 'or.  It's
// sometimes called 'evaluation for effect'.
//
// Restricting to a single variable makes it simpler but may
// miss some opportunities.
//
// The Scheme version also checked if the body of the
// (LET (vart val) ...) had no side effects and always called
// 'vart'.  If so then anything in 'val's body that does not
// depend on 'valueVar' can be moved above the LET.

func joinSubstitute(vart *VariableT, val *CallNodeT) bool {
	if len(val.Outputs) != 1 {
		return false
	}
	valueVar := val.Outputs[0]
	call := val.Next[0]
	for {
		// Everything before the IF needs to either be moved above
		// the (LET (vart val) ...) or down into the IF's continuations.
		// We don't do any downward movement at this point.
		if call.Primop.Name() == "if" {
			if IsVarReferenceNode(call.Inputs[0], valueVar) {
				break
			} else {
				return false
			}
		} else if call.Primop.Name() == "let" {
			// Could move any call where ordering doesn't matter
			// and it does not depend on valueVar.
			// KnownProcLambdas would also be okay in a LET.
			if !Every(IsJumpLambdaNode, call.Inputs) {
				return false
			}
			call = call.Next[0]
		} else {
			// We could allow calls small enough to be duplicated
			// to remain and be copied.
			return false
		}
	}

	return doJoinSubstitute(vart, val)
}

//  (let ((j (lambda (v)
//             (let ((k (lambda (n) ...)))
//               ... small ...
//               (test (lambda () true ...a... k(i) ...)
//                     (lambda () false ...b... k(j) ...)
//                     v))))
//    ... (jump j 0) ... (jump j 1) ... (jump j x) ...)
// ->
//  (let ()
//    (let ((k (lambda (n v0) ...[v0/v])))
//      (let ((t (lambda (v1) ... small ...a[v1/v]... k(i v1) ...))
//            (f (lambda (v2) ... small ...b[v2/v]... k(i v2) ...)))
//        (let ((j (lambda (v)
//                   (test (lambda () (t v))
//                         (lambda () (f v))
//                         v))))
//          ... (jump f 0) ... (jump t 1) ... (jump j x) ...))))
//
// We leave the original call in place because simplifiers are not
// allowed to change code above them in the tree.

func doJoinSubstitute(vart *VariableT, val *CallNodeT) bool {
	joinValueVar := val.Outputs[0]
	top := val.parent

	// walk vart's references categorizing them as true,
	// false, or unknown depending on the value they are passed
	trueRefs := []*ReferenceNodeT{}
	falseRefs := []*ReferenceNodeT{}
	unknownRefs := []*ReferenceNodeT{}
	for _, ref := range vart.Refs {
		val := ref.parent.Inputs[1]
		if !IsLiteralNode(val) {
			Push(&unknownRefs, ref)
		} else if val.(*LiteralNodeT).Value.ExactString() == "true" {
			Push(&trueRefs, ref)
		} else {
			Push(&falseRefs, ref)
		}
	}
	if len(trueRefs) == 0 && len(falseRefs) == 0 {
		// fmt.Printf("no constant applications\n")
		return false
	}

	unbindLambda(val) // removes it and vart from the top call

	block := MakeCalls()

	// Any vars & vals from LETs found before the IF call in val.
	letVars := []*VariableT{}
	letVals := []*CallNodeT{}

	call := val.Next[0]
	for len(call.Next) == 1 {
		if call.Primop.Name() == "let" {
			for i, vart := range call.Outputs {
				Push(&letVars, vart)
				Push(&letVals, call.Inputs[i].(*CallNodeT))
			}

			// Splice out 'call' and move it to the body of 'top'.
			callParent := call.parent
			nextCall := call.Next[0]
			DetachNext(call)
			AttachNext(callParent, DetachNext(nextCall))
			block.AppendCall(call)
			call.SetIsSimplified(false)
			call = nextCall
		} else {
			panic("found non-LET in join body")
		}
	}

	// Map from jump lambdas to their replacements for joinVar.
	// Every joinVar reference has a flagged ancestor with a
	// joinVar replacement (or the original).
	newJoinValueVars := map[NodeT]*VariableT{val: joinValueVar}
	val.SetFlag(1)

	makeNewJoinValueVar := func(call *CallNodeT) {
		newJoinValueVar := CopyVariable(joinValueVar)
		newJoinValueVars[call] = newJoinValueVar
		call.SetFlag(1)
		newJoinValueVar.Binder = call
		Push(&call.Outputs, newJoinValueVar)
	}

	for i, vart := range letVars {
		makeNewJoinValueVar(letVals[i])
		for _, ref := range vart.Refs {
			call := ref.parent
			Push(&call.Inputs, nil)
			AttachInput(call, len(call.Inputs)-1, MakeReferenceNode(joinValueVar))
			MarkChanged(call)
		}
	}

	jumpLambdas := []NodeT{}
	jumpVars := []*VariableT{}
	name := "true"
	for i := 0; i < 2; i++ {
		jumpLambda := MakeLambda(name, JumpLambda, nil)
		makeNewJoinValueVar(jumpLambda)
		jumpVar := MakeVariable(name, nil)
		ifCont := call.Next[i]
		AttachNext(jumpLambda, DetachNext(ifCont))
		jumpCall := MakeCall(LookupPrimop("jump"),
			nil,
			MakeReferenceNode(jumpVar),
			MakeReferenceNode(joinValueVar))
		jumpCall.Next = nil
		AttachNext(call, jumpCall, i)
		Push(&jumpLambdas, NodeT(jumpLambda))
		Push(&jumpVars, jumpVar)
		name = "false"
	}

	block.AddPrimopVarsCall("let", jumpVars, jumpLambdas...)
	block.AddPrimopVarsCall("let", []*VariableT{vart}, val)
	AttachNext(block.Last, DetachNext(top.Next[0]))
	AttachNext(top, block.First)

	temp := joinValueVar.Refs
	joinValueVar.Refs = []*ReferenceNodeT{}
	for _, ref := range temp {
		jumpLambda := markedAncestor(ref)
		ReplaceInput(ref, MakeReferenceNode(newJoinValueVars[jumpLambda]))
	}
	for jumpLambda, _ := range newJoinValueVars {
		jumpLambda.SetFlag(0)
	}

	for _, ref := range trueRefs {
		ReplaceInput(ref, MakeReferenceNode(jumpVars[0]))
	}
	for _, ref := range falseRefs {
		ReplaceInput(ref, MakeReferenceNode(jumpVars[1]))
	}

	return true
}
