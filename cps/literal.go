// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Binding literals to variables where needed for code generation.

package cps

import (
	"fmt"
)

// Add explicit calls to assign literals to variables for those
// primops that need their inputs in registers.

func makeVarsForLiterals() {
	for lambda := range Lambdas {
		varsForLiterals(lambda, map[string]*VariableT{})
	}
}

// Do we need to worry about register types?  Yes.

func varsForLiterals(call *CallNodeT, vars map[string]*VariableT) {
	inputs, _ := call.Primop.RegisterUsage(call)
	addedValues := []string{}
	if inputs != nil {
		if len(inputs) != len(call.Inputs) {
			panic(fmt.Sprintf("Primop %s returned %d input registers but has %d inputs.",
				call.Primop.Name(), len(inputs), len(call.Inputs)))
		}
		for i, input := range call.Inputs {
			if inputs[i] == nil || !IsLiteralNode(input) {
				continue
			}
			literal := input.(*LiteralNodeT)
			typeString := ""
			if literal.Type != nil {
				typeString = literal.Type.String()
			}
			value := literal.Value.ExactString() + "$" + typeString
			vart := vars[value]
			if vart != nil {
				ReplaceInput(input, MakeReferenceNode(vart))
				continue
			}
			vart = MakeVariable("v", literal.Type, literal.source)
			loadCall := MakeCall(LookupPrimop("loadReg"), []*VariableT{vart}, DetachInput(literal))
			InsertCallParent(call, loadCall)
			AttachInput(call, i, MakeReferenceNode(vart))
			vars[value] = vart
			addedValues = append(addedValues, value)
		}
	}
	for _, next := range call.Next {
		varsForLiterals(next, vars)
	}
	for _, value := range addedValues {
		delete(vars, value)
	}
}
