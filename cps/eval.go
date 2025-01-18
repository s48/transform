// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Run CPS nodes as a program for testing.  The primops in
// primops.go all have evaluation methods that get used here.
//
// Values can either be associated with variables or with
// registers, after register assignment.

package cps

import (
	"fmt"
	"strconv"

	"go/constant"
)

func Evaluate(proc *CallNodeT, args []int) []int {
	return evaluate(proc, args, &VarEnvT{map[*VariableT]any{}})
}

func RegEvaluate(proc *CallNodeT, args []int) []int {
	return evaluate(proc, args, newRegEnv())
}

func evaluate(proc *CallNodeT, args []int, env EnvT) []int {
	for i, arg := range args {
		env.Set(proc.Outputs[i+1], arg)
	}
	call := proc
	for call.Primop.Name() != "return" {
		// fmt.Printf("eval %d %s\n", call.Id, call.Primop.Name())
		call, env = call.Primop.(EvalPrimopT).Evaluate(call, env)
	}
	returnVals := call.Inputs[1:] // skip cont var
	results := make([]int, len(returnVals))
	for i, value := range returnVals {
		results[i] = nodeIntValue(value, env)
	}
	return results
}

type EvalPrimopT interface {
	Evaluate(*CallNodeT, EnvT) (*CallNodeT, EnvT)
}

//----------------------------------------------------------------
// Values for variables.

type EnvT interface {
	Get(*VariableT) any
	Set(*VariableT, any)
}

type VarEnvT struct {
	values map[*VariableT]any
}

func (env *VarEnvT) Get(vart *VariableT) any {
	return env.values[vart]
}

func (env *VarEnvT) Set(vart *VariableT, value any) {
	env.values[vart] = value
}

type RegEnvT struct {
	values map[RegisterT]any
	labels map[*VariableT]any
}

func newRegEnv() *RegEnvT {
	return &RegEnvT{map[RegisterT]any{}, map[*VariableT]any{}}
}

func (env *RegEnvT) Get(vart *VariableT) any {
	labelValue := env.labels[vart]
	if labelValue != nil {
		return labelValue
	}
	return env.values[vart.Register]
}

func (env *RegEnvT) Set(vart *VariableT, rawValue any) {
	switch value := rawValue.(type) {
	case *CallNodeT:
		env.labels[vart] = value
	default:
		env.values[vart.Register] = value
	}
}

//----------------------------------------------------------------
// Get a node's value.

func NodeValue(rawNode NodeT, env EnvT) any {
	switch node := rawNode.(type) {
	case *LiteralNodeT:
		switch node.Value.Kind() {
		case constant.Int:
			n, err := strconv.ParseInt(node.Value.ExactString(), 0, 64)
			if err != nil {
				panic(fmt.Sprintf("failed to parser int literal '%s'", err))
			}
			return int(n)
		default:
			panic("literal node has no int value")
		}
	case *ReferenceNodeT:
		return env.Get(node.Variable)
	case *CallNodeT:
		if node.CallType != JumpLambda {
			panic("NodeValue has non-jump lambda node")
		}
		return node
	default:
		panic("NodeValue got unknown node type")
	}
}

func nodeIntValue(node NodeT, env EnvT) int {
	switch value := NodeValue(node, env).(type) {
	case int:
		return value
	default:
		panic("node value is not an int: " + node.String())
	}
}

func nodeBoolValue(node NodeT, env EnvT) bool {
	switch value := NodeValue(node, env).(type) {
	case bool:
		return value
	default:
		panic("node value is not a bool: " + node.String())
	}
}

func nodeJumpLambdaValue(node NodeT, env EnvT) *CallNodeT {
	switch value := NodeValue(node, env).(type) {
	case *CallNodeT:
		return value
	default:
		panic("node value is not a jump lambda: " + node.String())
	}
}

func nodeIntSliceValue(node NodeT, env EnvT) []int {
	switch value := NodeValue(node, env).(type) {
	case []int:
		return value
	default:
		panic("node value is not an []int: " + node.String())
	}
}

func nodeIntPointerValue(node NodeT, env EnvT) *int {
	switch value := NodeValue(node, env).(type) {
	case *int:
		return value
	default:
		panic("node value is not a *int: " + node.String())
	}
}
