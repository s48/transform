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
	return evaluate(proc, args, &VarEnvT{map[*VariableT]*valueT{}})
}

func RegEvaluate(proc *CallNodeT, args []int) []int {
	return evaluate(proc, args, newRegEnv())
}

func evaluate(proc *CallNodeT, args []int, env EnvT) []int {
	for i, arg := range args {
		env.Set(proc.Outputs[i+1], &valueT{kind: intKind, intValue: arg})
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
	Get(*VariableT) *valueT
	Set(*VariableT, *valueT)
}

type VarEnvT struct {
	values map[*VariableT]*valueT
}

func (env *VarEnvT) Get(vart *VariableT) *valueT {
	return env.values[vart]
}

func (env *VarEnvT) Set(vart *VariableT, value *valueT) {
	env.values[vart] = value
}

type RegEnvT struct {
	values map[RegisterT]*valueT
	labels map[*VariableT]*valueT
}

func newRegEnv() *RegEnvT {
	return &RegEnvT{map[RegisterT]*valueT{}, map[*VariableT]*valueT{}}
}

func (env *RegEnvT) Get(vart *VariableT) *valueT {
	labelValue := env.labels[vart]
	if labelValue != nil {
		return labelValue
	}
	return env.values[vart.Register]
}

func (env *RegEnvT) Set(vart *VariableT, value *valueT) {
	if value.kind == jumpKind {
		env.labels[vart] = value
	} else {
		env.values[vart.Register] = value
	}
}

type valueKindT int

// The four possible types of values.
const (
	intKind = iota
	boolKind
	cellKind
	jumpKind
)

type valueT struct {
	kind         valueKindT
	intValue     int // also used as 0 and 1 for bools
	cellContents *valueT
	lambda       *CallNodeT // jump lambdas
}

//----------------------------------------------------------------
// Get a node's value.

func NodeValue(rawNode NodeT, env EnvT) *valueT {
	switch node := rawNode.(type) {
	case *LiteralNodeT:
		switch node.Value.Kind() {
		case constant.Int:
			n, err := strconv.ParseInt(node.Value.ExactString(), 0, 64)
			if err != nil {
				panic(fmt.Sprintf("failed to parser int literal '%s'", err))
			}
			return &valueT{kind: intKind, intValue: int(n)}
		default:
			panic("literal node has no int value")
		}
	case *ReferenceNodeT:
		return env.Get(node.Variable)
	case *CallNodeT:
		if node.CallType != JumpLambda {
			panic("NodeValue has non-jump lambda node")
		}
		return &valueT{kind: jumpKind, lambda: node}
	default:
		panic("NodeValue has call node")
	}
}

func nodeIntValue(node NodeT, env EnvT) int {
	value := NodeValue(node, env)
	if value.kind != intKind {
		PpCps(node)
		fmt.Printf("kind is %d\n", value.kind)
		panic("node has no int value")
	}
	return value.intValue
}

func nodeJumpValue(rawNode NodeT, env EnvT) *CallNodeT {
	switch node := rawNode.(type) {
	case *ReferenceNodeT:
		value := env.Get(node.Variable)
		if value.kind != jumpKind {
			panic("value is not a jump lambda")
		}
		return value.lambda
	default:
		panic("node has no int value")
	}
}
