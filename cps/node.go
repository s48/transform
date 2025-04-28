// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package cps

import (
	"fmt"
	"go/constant"
	"go/token"
	"go/types"
	"maps"

	"github.com/s48/transform/util"
)

// Wart: We need an interface to replace Go's tokens for source data.
// token.FileSet is not an interface so we can't create our own.
var TheFileSet *token.FileSet

//----------------------------------------------------------------
// A call node represents both a call to some primitive operation and
// that call's continuation.  Thus they have both inputs, which are nodes,
// and outputs, which are the continuation's variables.
//
// Non-continuation lambdas are represented using call nodes that have
// no inputs, just bound output variables.  This is a little confusing
// but has the advantage that all interior nodes in the node tree are
// calls, and all the leaves are literals and references.

type NodeTypeT int

const (
	LiteralNode = iota
	ReferenceNode
	CallNode
)

type NodeT interface {
	NodeType() NodeTypeT
	Parent() *CallNodeT
	SetParent(parent *CallNodeT)
	Index() int // index in parent's inputs
	SetIndex(index int)

	IsNil() bool
	// Is this a literal, variable references, or non-continuation
	// lambda.
	IsValue() bool

	// The simplifier applies a set of optimizing code tranformations.
	// Nodes that have been simplified are flagged and any change to a
	// node clears that flag.  There is an invariant that if a node
	// has been simplified then all of its descendents have also been
	// simplified.
	IsSimplified() bool
	SetIsSimplified(isSimplified bool)

	// Temporary marker used in analysing the node tree.  Must be set
	// back to zero upon completion.
	Flag() int
	SetFlag(flag int)

	String() string // So they're easy to print.
}

type NodeBaseT struct {
	parent     *CallNodeT
	index      int
	simplified bool
	flag       int
	source     token.Pos
}

func (node *NodeBaseT) IsSimplified() bool                { return node.simplified }
func (node *NodeBaseT) SetIsSimplified(isSimplified bool) { node.simplified = isSimplified }
func (node *NodeBaseT) Flag() int                         { return node.flag }
func (node *NodeBaseT) SetFlag(flag int)                  { node.flag = flag }
func (node *NodeBaseT) Parent() *CallNodeT                { return node.parent }
func (node *NodeBaseT) SetParent(parent *CallNodeT)       { node.parent = parent }
func (node *NodeBaseT) Index() int                        { return node.index }
func (node *NodeBaseT) SetIndex(index int)                { node.index = index }
func (node *NodeBaseT) Source() token.Pos                 { return node.source }
func (node *NodeBaseT) SetSource(source token.Pos)        { node.source = source }

func IsLiteralNode(node NodeT) bool   { return node != nil && node.NodeType() == LiteralNode }
func IsReferenceNode(node NodeT) bool { return node != nil && node.NodeType() == ReferenceNode }
func IsCallNode(node NodeT) bool      { return node != nil && node.NodeType() == CallNode }
func IsJumpLambdaNode(node NodeT) bool {
	return node != nil && node.NodeType() == CallNode && node.(*CallNodeT).CallType == JumpLambda
}
func IsProcLambdaNode(node NodeT) bool {
	return node != nil && node.NodeType() == CallNode && node.(*CallNodeT).CallType == ProcLambda
}

func IsNil(node NodeT) bool {
	return node == nil || node.IsNil()
}

//----------------------------------------------------------------

type LiteralNodeT struct {
	NodeBaseT
	Value constant.Value
	// types.Type is an easy-to-implement interface, so it's not Go specific.
	Type types.Type
}

func (node *LiteralNodeT) NodeType() NodeTypeT { return LiteralNode }
func (node *LiteralNodeT) IsNil() bool         { return node == nil }
func (node *LiteralNodeT) IsValue() bool       { return true }
func (node *LiteralNodeT) String() string {
	return node.Value.ExactString()
}

func MakeLiteral(value any, typ types.Type) *LiteralNodeT {
	return &LiteralNodeT{Value: constant.Make(value), Type: typ}
}

func CopyLiteralNode(node *LiteralNodeT) *LiteralNodeT {
	return &LiteralNodeT{Value: node.Value,
		Type:      node.Type,
		NodeBaseT: NodeBaseT{source: node.source}}
}

//----------------------------------------------------------------

type ReferenceNodeT struct {
	NodeBaseT
	Variable *VariableT
}

func (node *ReferenceNodeT) NodeType() NodeTypeT { return ReferenceNode }
func (node *ReferenceNodeT) IsNil() bool         { return node == nil }
func (node *ReferenceNodeT) IsValue() bool       { return true }
func (node *ReferenceNodeT) String() string {
	return fmt.Sprintf("{reference %s_%d}", node.Variable.Name, node.Variable.Id)
}

func MakeReferenceNode(variable *VariableT) *ReferenceNodeT {
	node := &ReferenceNodeT{Variable: variable}
	variable.Refs = append(variable.Refs, node)
	return node
}

func IsVarReferenceNode(node NodeT, vart *VariableT) bool {
	return IsReferenceNode(node) && node.(*ReferenceNodeT).Variable == vart
}

//----------------------------------------------------------------

type CallTypeT int

const (
	CallExit   = iota // directly follows some other call
	ProcLambda        // full procedure that is passed a continuation
	JumpLambda        // only called tail-recursively and has no
	// continuation argument
)

type CallNodeT struct {
	NodeBaseT

	CallType CallTypeT
	Primop   PrimopT // the primitive operator being called
	Inputs   []NodeT
	Outputs  []*VariableT
	Next     []*CallNodeT // calls that immediately follow this one

	Block BasicBlockT // proc and jump lambdas and call exits of conditionals

	Name string // for debugging
	Id   int    // ditto
}

// Most calls have one Next call.  Conditionals have two or more,
// jumps and returns have none.

func (node *CallNodeT) NodeType() NodeTypeT { return CallNode }
func (node *CallNodeT) IsNil() bool         { return node == nil }
func (node *CallNodeT) IsExit() bool        { return node.CallType == CallExit }
func (node *CallNodeT) IsValue() bool       { return node.CallType != CallExit }
func (node *CallNodeT) IsLambda() bool      { return node.CallType != CallExit }

func (node *CallNodeT) InputVariable(i int) *VariableT {
	switch input := node.Inputs[i].(type) {
	case *ReferenceNodeT:
		return input.Variable
	}
	return nil
}

func (node *CallNodeT) String() string {
	return fmt.Sprintf("{call %s}", CallString(node))
}

func MakeCall(primop PrimopT, outputs []*VariableT, inputs ...NodeT) *CallNodeT {
	id := nextVariableId
	nextVariableId += 1
	call := &CallNodeT{CallType: CallExit,
		Primop:  primop,
		Id:      id,
		Name:    "c",
		Inputs:  make([]NodeT, len(inputs)),
		Outputs: outputs,
		Next:    make([]*CallNodeT, 1)}
	for i, arg := range inputs {
		AttachInput(call, i, arg)
	}
	for _, output := range outputs {
		output.Binder = call
	}
	return call
}

func MakeLambda(name string, callType CallTypeT, outputs []*VariableT) *CallNodeT {
	primopName := ""
	switch callType {
	case ProcLambda:
		primopName = "procLambda"
	case JumpLambda:
		primopName = "jumpLambda"
	}
	call := MakeCall(LookupPrimop(primopName), outputs)
	call.CallType = callType
	call.Name = name
	Lambdas.Add(call)
	return call
}

// Set containing all calls that do not have a single predecessor.
var Lambdas = util.SetT[*CallNodeT]{}

// For debugging.  This is the topmost node and has no parent.
var TopLambda *CallNodeT

//----------------------------------------------------------------
// variables
//
// types.Type is an easy-to-implement interface, so it's not Go specific.

type VariableT struct {
	Name         string
	Id           int
	Binder       *CallNodeT
	Refs         []*ReferenceNodeT
	Flags        map[string]any
	Copy         *VariableT // used when copying node trees
	Type         types.Type
	Source       token.Pos
	varRegAllocT // register allocation stuff
}

func (vart *VariableT) String() string {
	return fmt.Sprintf("%s_%d", vart.Name, vart.Id)
}

func (vart *VariableT) IsUsed() bool {
	return vart != nil && 0 < len(vart.Refs)
}

func (vart *VariableT) IsUnused() bool {
	return vart == nil || len(vart.Refs) == 0
}

func (vart *VariableT) HasFlag(flag string) bool {
	_, found := vart.Flags[flag]
	return found
}

var nextVariableId = 0

func MakeVariable(name string, typ types.Type, source ...token.Pos) *VariableT {
	id := nextVariableId
	nextVariableId += 1
	var src token.Pos
	if 0 < len(source) {
		src = source[0]
	}
	return &VariableT{Name: name, Id: id, Type: typ, Source: src, Flags: map[string]any{}}
}

// A 'cell' variable is one that holds the value of a variable in
// the source, allowing that variable to be set.  The type of a
// cell variable is the type of the contents, not of the cell itself
// (we know it's a cell).

func MakeCellVariable(name string, typ types.Type, source ...token.Pos) *VariableT {
	result := MakeVariable(name, typ, source...)
	result.Flags["cell"] = true
	return result
}

func CopyVariable(vart *VariableT) *VariableT {
	id := nextVariableId
	nextVariableId += 1
	return &VariableT{Name: vart.Name, Id: id, Type: vart.Type, Source: vart.Source, Flags: maps.Clone(vart.Flags)}
}

// Safety checking.

func EraseVariable(vart *VariableT) {
	if vart.Name == "<erased>" {
		panic("variable erased twice")
	}
	if 0 < len(vart.Refs) {
		panic("erasing variable with references")
	}
	vart.Name = "<erased>"
}

//----------------------------------------------------------------
// Primitive operations.

// Every call has a primitive operation that defines what the call does.

type PrimopT interface {
	Name() string
	SideEffects() bool
	Simplify(call *CallNodeT)
	// The return values are the inputs' and outputs' register usages.
	RegisterUsage(call *CallNodeT) ([]*RegUseSpecT, []*RegUseSpecT)
}

var PrimopTable = map[string]PrimopT{}

func LookupPrimop(name string) PrimopT {
	primop := PrimopTable[name]
	if primop == nil {
		panic(fmt.Sprintf("no primop named '%s'", name))
	}
	return primop
}

// Primops that call a procedure implement this.
type CallsProcPrimopT interface {
	CalledProc(*CallNodeT) *CallNodeT // Proc being called.
}

//----------------------------------------------------------------------------
// This walks the tree rooted at `node` and removes all pointers that
// point into this tree from outside.
//
// Reference nodes are removed from the refs list of the variable they reference.
//
// Would be good to check for double erasures
//    (set-node-index! node '<erased>))))

func EraseAll(nodes []NodeT) {
	for _, node := range nodes {
		Erase(node)
	}
}

func Erase(rawNode NodeT) {
	if IsNil(rawNode) {
		return
	}
	switch node := rawNode.(type) {
	case *CallNodeT:
		for _, input := range node.Inputs {
			Erase(input)
		}
		for _, next := range node.Next {
			Erase(next)
		}
		for _, vart := range node.Outputs {
			EraseVariable(vart)
		}
		Lambdas.Remove(node)
	case *LiteralNodeT:
		// nothing to do
	case *ReferenceNodeT:
		vart := node.Variable
		refs := vart.Refs
		for i, ref := range refs {
			if ref == node {
				last := len(refs) - 1
				refs[i] = refs[last] // this may be a no-op
				vart.Refs = refs[:last]
				break
			}
		}
	}
}

func ProclaimEmpty(node NodeT) {
	if !IsNil(node) {
		panic("node not empty")
	}
}

//----------------------------------------------------------------
// Disconnecting and reconnecting nodes.

func DetachInput(node NodeT) NodeT {
	parent := node.Parent()
	parent.Inputs[node.Index()] = nil
	node.SetIndex(-1)
	node.SetParent(nil)
	return node
}

func DetachNext(node *CallNodeT) *CallNodeT {
	if node.IsValue() {
		panic("detaching value call")
	}
	parent := node.Parent()
	parent.Next[node.Index()] = nil
	node.SetIndex(-1)
	node.SetParent(nil)
	return node
}

func AttachInput(parent *CallNodeT, index int, child NodeT) {
	ProclaimEmpty(child.Parent())
	ProclaimEmpty(parent.Inputs[index])
	parent.Inputs[index] = child
	child.SetParent(parent)
	child.SetIndex(index)
}

func AttachNext(parent *CallNodeT, next *CallNodeT, optionalIndex ...int) {
	index := 0
	if 0 < len(optionalIndex) {
		index = optionalIndex[0]
	}
	if next.IsLambda() {
		panic("attaching lambda as next")
	}
	if len(parent.Next) <= index {
		panic("AttachNext index too large")
	}
	ProclaimEmpty(next.parent)
	ProclaimEmpty(parent.Next[index])
	parent.Next[index] = next
	next.index = index
	next.parent = parent
}

//----------------------------------------------------------------

func CheckNode(topCall *CallNodeT) {
	refs := map[*VariableT]int{}
	var check func(rawNode NodeT, parent *CallNodeT)
	check = func(rawNode NodeT, parent *CallNodeT) {
		if rawNode.IsNil() {
			panic(fmt.Sprintf("nil node"))
		}
		if rawNode.Flag() != 0 {
			panic(fmt.Sprintf("node has flag set %+v", rawNode))
		}
		if parent != nil && rawNode.IsValue() && rawNode.Parent() != parent {
			PpCps(parent)
			panic(fmt.Sprintf("bad parent pointer %+v", rawNode))
		}
		switch node := rawNode.(type) {
		case *CallNodeT:
			if !(parent == nil || node.IsValue() ||
				(node.index < len(parent.Next) && parent.Next[node.index] == node)) {
				PpCps(parent)
				panic(fmt.Sprintf("bad parent pointer %+v", node))
			}
			if node.Primop.Name() == "letrec" {
				for _, output := range node.Outputs {
					refs[output] = 0
				}
			}
			for i, input := range node.Inputs {
				if input == nil {
					fmt.Printf("Input %d is nil ", i)
					PpCps(node)
					panic("input is nil")
				}
				if input.Parent() != node || input.Index() != i {
					PpCps(node)
					panic(fmt.Sprintf("bad parent pointer %+v", input))
				}
				check(input, node)
			}
			if node.Primop.Name() != "letrec" {
				for _, output := range node.Outputs {
					refs[output] = 0
				}
			}
			for i, next := range node.Next {
				if next == nil {
					fmt.Printf("call %s:%d next is nil: %+v\n", node.Name, node.Id, node)
					PpCps(node)
					panic("nil Next call")
				}
				if next.Parent() != node || next.Index() != i {
					PpCps(node)
					panic(fmt.Sprintf("bad parent pointer %+v %+v", next))
				}
				check(next, node)
				for _, output := range node.Outputs {
					if output.Binder != node {
						fmt.Printf("%s_%d has bad binder %+v\n",
							output.Name, output.Id, output.Binder)
					}
					if len(output.Refs) != refs[output] {
						panic(fmt.Sprintf("%s_%d has %d refs but %d reference nodes",
							output.Name, output.Id, len(output.Refs), refs[output]))
					}
					delete(refs, output)
				}
			}

		case *LiteralNodeT:
			// nothing to do
		case *ReferenceNodeT:
			vart := node.Variable
			// Global variables don't have binders.
			if vart.HasFlag("global") {
				break
			}
			if vart.Binder == nil {
				panic(fmt.Sprintf("%s_%d has no binder", vart.Name, vart.Id))
			}
			count, found := refs[vart]
			if !found {
				panic(fmt.Sprintf("%s_%d referenced out of scope", vart.Name, vart.Id))
			}
			refs[vart] = count + 1
		}
	}
	check(topCall, nil)
}
