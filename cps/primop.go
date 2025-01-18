// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Primops for running test programs.

package cps

import (
	"fmt"
	"strconv"

	"go/constant"
	"go/token"
)

func init() { fmt.Scanf("") } // appease the import gods

// We just have one register class.

type registerT struct {
	class *RegisterClassT
	name  string
}

func (reg *registerT) Class() *RegisterClassT { return reg.class }
func (reg *registerT) String() string         { return reg.name }

const (
	numRegs     = 5
	allRegsMask = (1 << numRegs) - 1
)

var generalRegister = &RegisterClassT{Name: "r", Registers: make([]RegisterT, numRegs)}

var procOutputSpecs = make([]*RegUseSpecT, numRegs+1)
var inputSpec = &RegUseSpecT{IsEarly: true, Class: generalRegister, RegisterMask: allRegsMask}
var outputSpec = &RegUseSpecT{Class: generalRegister, RegisterMask: allRegsMask}

func init() {
	for i := range numRegs {
		generalRegister.Registers[i] = &registerT{generalRegister, "r" + strconv.Itoa(i)}
		procOutputSpecs[i+1] = &RegUseSpecT{Class: generalRegister, RegisterMask: 1 << i}
	}
}

func registerUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return registerUsageSpec(call, inputSpec, outputSpec)
}

// Use 'inputSpec' for all inputs and 'outputSpec' for all outputs.

func registerUsageSpec(call *CallNodeT,
	inputSpec *RegUseSpecT,
	outputSpec *RegUseSpecT) ([]*RegUseSpecT, []*RegUseSpecT) {

	inputs := make([]*RegUseSpecT, len(call.Inputs))
	for i, input := range call.Inputs {
		if IsReferenceNode(input) { // Don't require registers for literals
			inputs[i] = inputSpec
		}
	}
	outputs := make([]*RegUseSpecT, len(call.Outputs))
	for i := range call.Outputs {
		outputs[i] = outputSpec
	}
	return inputs, outputs
}

//----------------------------------------------------------------
// The methods we care about:
//  - simplify
//  - registerUsage
//  - eval
// Only 'eval' has any real code here.  The others just call predefined
// compiler functions.

func addPrimop(primop PrimopT) {
	PrimopTable[primop.Name()] = primop
}

func DefinePrimops() {
	addPrimop(&ProcLambdaPrimopT{})
	addPrimop(&JumpLambdaPrimopT{})
	addPrimop(&LetPrimopT{})
	addPrimop(&MakeCellPrimopT{})
	addPrimop(&CellRefPrimopT{})
	addPrimop(&CellSetPrimopT{})
	addPrimop(&PointerSetPrimopT{})
	addPrimop(&LetrecPrimopT{})
	addPrimop(&JumpPrimopT{})
	addPrimop(&ReturnPrimopT{})
	addPrimop(&LoadRegPrimopT{})
	addPrimop(&MakeLiteralPrimopT{})
	addPrimop(&IfPrimopT{})
	addPrimop(&IfLtPrimopT{})
	addPrimop(&IfEqPrimopT{})
	addPrimop(&BinopPrimopT{"+"})
	addPrimop(&BinopPrimopT{"-"})
	addPrimop(&BinopPrimopT{"*"})
	addPrimop(&CompPrimopT{"<", "if<", false})
	addPrimop(&CompPrimopT{">=", "if<", true})
	addPrimop(&CompPrimopT{"==", "if=", false})
	addPrimop(&CompPrimopT{"!=", "if=", true})
	addPrimop(&NotPrimopT{})
	addPrimop(&LenPrimopT{})
	addPrimop(&SliceIndexPrimopT{})
	addPrimop(&PointerRefPrimopT{})
}

// No macros...

type ProcLambdaPrimopT struct{}

func (primop *ProcLambdaPrimopT) Name() string             { return "procLambda" }
func (primop *ProcLambdaPrimopT) SideEffects() bool        { return false }
func (primop *ProcLambdaPrimopT) Simplify(call *CallNodeT) { DefaultSimplify(call) }
func (primop *ProcLambdaPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return nil, procOutputSpecs[:len(call.Outputs)]
}
func (primop *ProcLambdaPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	return call.Next[0], env
}

type JumpLambdaPrimopT struct {
}

func (primop *JumpLambdaPrimopT) Name() string             { return "jumpLambda" }
func (primop *JumpLambdaPrimopT) SideEffects() bool        { return false }
func (primop *JumpLambdaPrimopT) Simplify(call *CallNodeT) { DefaultSimplify(call) }
func (primop *JumpLambdaPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return registerUsageSpec(call, nil, jumpRegUseSpec)
}
func (primop *JumpLambdaPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	return call.Next[0], env
}

type LetPrimopT struct{}

func (primop *LetPrimopT) Name() string             { return "let" }
func (primop *LetPrimopT) SideEffects() bool        { return false }
func (primop *LetPrimopT) Simplify(call *CallNodeT) { SimplifyLet(call) }
func (primop *LetPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return nil, nil
}
func (primop *LetPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	for i, vart := range call.Outputs {
		env.Set(vart, nodeJumpLambdaValue(call.Inputs[i], env))
	}
	return call.Next[0], env
}

type MakeCellPrimopT struct{}

func (primop *MakeCellPrimopT) Name() string             { return "makeCell" }
func (primop *MakeCellPrimopT) SideEffects() bool        { return false }
func (primop *MakeCellPrimopT) Simplify(call *CallNodeT) { SimplifyMakeCell(call) }
func (primop *MakeCellPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	panic("Generating code for " + primop.Name())
}
func (primop *MakeCellPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	return nil, env
}

type CellRefPrimopT struct{}

func (primop *CellRefPrimopT) Name() string             { return "cellRef" }
func (primop *CellRefPrimopT) SideEffects() bool        { return true }
func (primop *CellRefPrimopT) Simplify(call *CallNodeT) { DefaultSimplify(call) }
func (primop *CellRefPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	panic("Generating code for " + primop.Name())
}
func (primop *CellRefPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	return nil, env
}

type CellSetPrimopT struct{}

func (primop *CellSetPrimopT) Name() string             { return "cellSet" }
func (primop *CellSetPrimopT) SideEffects() bool        { return true }
func (primop *CellSetPrimopT) Simplify(call *CallNodeT) { DefaultSimplify(call) }
func (primop *CellSetPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	panic("Generating code for " + primop.Name())
}
func (primop *CellSetPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	return nil, env
}

type PointerSetPrimopT struct{}

func (primop *PointerSetPrimopT) Name() string             { return "PointerSet" }
func (primop *PointerSetPrimopT) SideEffects() bool        { return true }
func (primop *PointerSetPrimopT) Simplify(call *CallNodeT) { DefaultSimplify(call) }
func (primop *PointerSetPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	panic("Generating code for " + primop.Name())
}
func (primop *PointerSetPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	return nil, env
}

type LetrecPrimopT struct{}

func (primop *LetrecPrimopT) Name() string             { return "letrec" }
func (primop *LetrecPrimopT) SideEffects() bool        { return false }
func (primop *LetrecPrimopT) Simplify(call *CallNodeT) { SimplifyLetrec(call) }
func (primop *LetrecPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return nil, nil
}
func (primop *LetrecPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	for i, vart := range call.Outputs {
		env.Set(vart, nodeJumpLambdaValue(call.Inputs[i], env))
	}
	return call.Next[0], env
}

type JumpPrimopT struct{}

func (primop *JumpPrimopT) Name() string             { return "jump" }
func (primop *JumpPrimopT) SideEffects() bool        { return false }
func (primop *JumpPrimopT) Simplify(call *CallNodeT) { SimplifyJump(call) }
func (primop *JumpPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return registerUsageSpec(call, jumpRegUseSpec, nil)
}
func (primop *JumpPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	jumpLambda := nodeJumpLambdaValue(call.Inputs[0], env)
	for i, vart := range jumpLambda.Outputs {
		env.Set(vart, NodeValue(call.Inputs[i+1], env))
	}
	return jumpLambda.Next[0], env
}

type ReturnPrimopT struct{}

func (primop *ReturnPrimopT) Name() string             { return "return" }
func (primop *ReturnPrimopT) SideEffects() bool        { return false }
func (primop *ReturnPrimopT) Simplify(call *CallNodeT) { DefaultSimplify(call) }
func (primop *ReturnPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	inputs := make([]*RegUseSpecT, len(call.Inputs))
	for i := range len(call.Inputs) - 1 {
		inputs[i+1] = inputSpec
	}
	return inputs, nil
}
func (primop *ReturnPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	return nil, env
}

// Load a register with an immediage value.
type LoadRegPrimopT struct{}

func (primop *LoadRegPrimopT) Name() string             { return "loadReg" }
func (primop *LoadRegPrimopT) SideEffects() bool        { return false }
func (primop *LoadRegPrimopT) Simplify(call *CallNodeT) { DefaultSimplify(call) }
func (primop *LoadRegPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return nil, nil
}
func (primop *LoadRegPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	x := nodeIntValue(call.Inputs[0], env)
	env.Set(call.Outputs[0], x)
	return call.Next[0], env
}

// Load a register with an immediage value.
type MakeLiteralPrimopT struct{}

func (primop *MakeLiteralPrimopT) Name() string             { return "makeLiteral" }
func (primop *MakeLiteralPrimopT) SideEffects() bool        { return false }
func (primop *MakeLiteralPrimopT) Simplify(call *CallNodeT) { DefaultSimplify(call) }
func (primop *MakeLiteralPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return registerUsage(call)
}
func (primop *MakeLiteralPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	value := make([]int, len(call.Inputs))
	for i, input := range call.Inputs {
		value[i] = nodeIntValue(input, env)
	}
	env.Set(call.Outputs[0], value)
	return call.Next[0], env
}

type IfPrimopT struct{}

func (primop *IfPrimopT) Name() string             { return "if" }
func (primop *IfPrimopT) SideEffects() bool        { return false }
func (primop *IfPrimopT) Simplify(call *CallNodeT) { DefaultSimplify(call) }
func (primop *IfPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	panic("Generating code for " + primop.Name())
}
func (primop *IfPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	if nodeBoolValue(call.Inputs[0], env) {
		return call.Next[0], env
	} else {
		return call.Next[1], env
	}
}

type IfLtPrimopT struct{}

func (primop *IfLtPrimopT) Name() string      { return "if<" }
func (primop *IfLtPrimopT) SideEffects() bool { return false }
func (primop *IfLtPrimopT) Simplify(call *CallNodeT) {
	simplifyCond(call, token.LSS)
}

func (primop *IfLtPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return registerUsage(call)
}

func (primop *IfLtPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	x := nodeIntValue(call.Inputs[0], env)
	y := nodeIntValue(call.Inputs[1], env)
	if x < y {
		return call.Next[0], env
	} else {
		return call.Next[1], env
	}
}

type IfEqPrimopT struct{}

func (primop *IfEqPrimopT) Name() string      { return "if=" }
func (primop *IfEqPrimopT) SideEffects() bool { return false }
func (primop *IfEqPrimopT) Simplify(call *CallNodeT) {
	simplifyCond(call, token.EQL)
}
func (primop *IfEqPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return registerUsage(call)
}
func (primop *IfEqPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	x := nodeIntValue(call.Inputs[0], env)
	y := nodeIntValue(call.Inputs[1], env)
	if x == y {
		return call.Next[0], env
	} else {
		return call.Next[1], env
	}
}

func simplifyCond(call *CallNodeT, tok token.Token) {
	x := call.Inputs[0]
	y := call.Inputs[1]
	if IsLiteralNode(x) && IsLiteralNode(y) {
		nextIndex := 1
		if constant.Compare(x.(*LiteralNodeT).Value,
			tok,
			y.(*LiteralNodeT).Value) {

			nextIndex = 0
		}
		ReplaceNext(call, DetachNext(call.Next[nextIndex]))
	} else {
		DefaultSimplify(call)
	}
}

type BinopPrimopT struct {
	MyName string
}

func (primop *BinopPrimopT) Name() string      { return primop.MyName }
func (primop *BinopPrimopT) SideEffects() bool { return false }
func (primop *BinopPrimopT) Simplify(call *CallNodeT) {
	SimplifyArithBinop(call)
}

var goOpToken = map[string]token.Token{"+": token.ADD,
	"-": token.SUB,
	"*": token.MUL,
	"&": token.AND,
	"|": token.OR,
}

func SimplifyArithBinop(call *CallNodeT) {
	x := call.Inputs[0]
	y := call.Inputs[1]
	if IsLiteralNode(x) {
		if IsLiteralNode(y) {
			xLit := x.(*LiteralNodeT)
			xLit.Value = constant.BinaryOp(xLit.Value,
				goOpToken[call.Primop.Name()],
				y.(*LiteralNodeT).Value)
			DetachInput(y)
			RemoveNullInputs(call, 1)
			call.Primop = LookupPrimop("let")
			MarkChanged(call)
			return
		} else if call.Primop.Name() != "-" {
			// If only one literal put it second.  This makes code
			// generation easier and will help with simplifying
			// expressions like '(x + 3) + 4'.
			temp := DetachInput(x)
			AttachInput(call, 0, DetachInput(y))
			AttachInput(call, 1, temp)
			MarkChanged(call)
			return
		}
	}
	DefaultSimplify(call)
}
func (primop *BinopPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return registerUsage(call)
}
func (primop *BinopPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	return evalBinop(call, env)
}

func evalBinop(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	x := nodeIntValue(call.Inputs[0], env)
	y := nodeIntValue(call.Inputs[1], env)
	var z any
	switch call.Primop.Name() {
	case "+":
		z = x + y
	case "-":
		z = x - y
	case "*":
		z = x * y
	case "<", ">=", "==", "!=":
		switch call.Primop.Name() {
		case "<":
			z = x < y
		case ">=":
			z = x >= y
		case "==":
			z = x == y
		case "!=":
			z = x != y
		}
	}
	env.Set(call.Outputs[0], z)
	return call.Next[0], env
}

type CompPrimopT struct {
	MyName     string
	CondPrimop string
	CondNegate bool
}

func (primop *CompPrimopT) Name() string      { return primop.MyName }
func (primop *CompPrimopT) SideEffects() bool { return false }
func (primop *CompPrimopT) Simplify(call *CallNodeT) {
	SimplifyBooleanOp(call, primop.CondPrimop, primop.CondNegate)
}
func (primop *CompPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	panic("Generating code for " + primop.Name())
}
func (primop *CompPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	return evalBinop(call, env)
}

type NotPrimopT struct{}

func (primop *NotPrimopT) Name() string      { return "!" }
func (primop *NotPrimopT) SideEffects() bool { return false }
func (primop *NotPrimopT) Simplify(call *CallNodeT) {
	SimplifyBooleanOp(call, "if", true)
}
func (primop *NotPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	panic("Generating code for 'not'")
}
func (primop *NotPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	return nil, env
}

type LenPrimopT struct{}

func (primop *LenPrimopT) Name() string             { return "len" }
func (primop *LenPrimopT) SideEffects() bool        { return false }
func (primop *LenPrimopT) Simplify(call *CallNodeT) { DefaultSimplify(call) }
func (primop *LenPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return registerUsage(call)
}
func (primop *LenPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	slice := nodeIntSliceValue(call.Inputs[0], env)
	env.Set(call.Outputs[0], len(slice))
	return call.Next[0], env
}

type SliceIndexPrimopT struct{}

func (primop *SliceIndexPrimopT) Name() string             { return "sliceIndex" }
func (primop *SliceIndexPrimopT) SideEffects() bool        { return false }
func (primop *SliceIndexPrimopT) Simplify(call *CallNodeT) { DefaultSimplify(call) }
func (primop *SliceIndexPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return registerUsage(call)
}
func (primop *SliceIndexPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	slice := nodeIntSliceValue(call.Inputs[0], env)
	index := nodeIntValue(call.Inputs[1], env)
	env.Set(call.Outputs[0], &slice[index])
	return call.Next[0], env
}

type PointerRefPrimopT struct{}

func (primop *PointerRefPrimopT) Name() string             { return "pointerRef" }
func (primop *PointerRefPrimopT) SideEffects() bool        { return false }
func (primop *PointerRefPrimopT) Simplify(call *CallNodeT) { DefaultSimplify(call) }
func (primop *PointerRefPrimopT) RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT) {
	return registerUsage(call)
}
func (primop *PointerRefPrimopT) Evaluate(call *CallNodeT, env EnvT) (*CallNodeT, EnvT) {
	pointer := nodeIntPointerValue(call.Inputs[0], env)
	env.Set(call.Outputs[0], *pointer)
	return call.Next[0], env
}
