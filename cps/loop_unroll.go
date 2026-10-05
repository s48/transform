// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Unrolling loops.

package cps
/*
import (
	"slices"

	"github.com/s48/transform/util"
)

// Will need to know the index variable as well.
// Move up from the recursive call's parent looking for a
// conditional.  Maybe do verification first.
//
// var and lambda
// 1. Var has one reference in lambda, any number outside
//    (could have more inside and we leave the others to
//     call back to the original).
// 2. Body of lambda is an if< between a variable
//    bound by the lambda and either a literal or a variable
//    bound above the lambda.
// 3. The iteration variable is passed 1+ itself.
//

// 1. Identify entry reference and internal reference (what
//    if more than interal reference?).
// 2. Make a new entry copy and add it to the letrec,
//    saving saving the newly-added last reference which
//    is the new internal reference.
// 3. Count times make a new copy and replaced the previous
//    new interal reference.
// 4. External reference get replaced by new variable.

func unrollLoop(vart *VariableT, lambda *CallNodeT, count int) bool {
	lambda.SetFlag(1)
	internalRefs := []*ReferenceNodeT{}
	externalRefs := []*ReferenceNodeT{}
	for _, ref := range vart.Refs {
		if hasMarkedAncestor(ref) {
			util.Push(&internalRefs, ref)
		} else {
			util.Push(&externalRefs, ref)
		}
	}
	numInternalRefs := len(internalRefs)
	if numInternalRefs != 1 {
		if numInternalRefs == 0 {
			fmt.Printf("Loop to unroll has no internal reference.\n")
		} else {
			fmt.Printf("Loop to unroll has %d internal references, allowed only one.\n", numInternalRefs)
		}
		return false
	}
	recursiveRef := internalRefs[0]
	condCall := lambda.Next[0]
	primop := condCall.Primop.Name()
	if primop != "If<U" && primop != "if<S" {
		fmt.Printf("Loop starts with '%s', not 'if<S' or 'if<U'.\n", primop)
	}
	iterationVar := condCall.InputVariable(0)
	if iterationVar == nil || iterationVar.Binder != lambda {
		panic("conditional does not check iteration variable")
	}
	high := condCall.Inputs[1]
	trueArm := condCall.Next[0]
	trueArm.SetFlag(1)
	if MarkedAncestor(recursiveRef != trueArm) {
		panic("recursive all not in true arm of conditional")
	}
	loopCall := recursiveRef.Parent()

}
*/
