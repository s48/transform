// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Various CPS manipulation and analysis procedures.

package cps

import (
	"fmt"

	"go/constant"
	"go/token"
	"go/types"
)

func init() { fmt.Sprintf("") } // suppress '"fmt" imported and not used' error

// Replace old-node with new-node, noting that a change has been made at this
// point in the tree.

func ReplaceInput(oldNode NodeT, newNode NodeT) {
	index := oldNode.Index()
	parent := oldNode.Parent()
	Erase(DetachInput(oldNode))
	AttachInput(parent, index, newNode)
	MarkChanged(parent)
}

func ReplaceNext(oldNode *CallNodeT, newNode *CallNodeT) {
	index := oldNode.Index()
	parent := oldNode.Parent()
	Erase(DetachNext(oldNode))
	AttachNext(parent, newNode, index)
	MarkChanged(parent)
	MarkChanged(newNode)
}

func InsertCallParent(child *CallNodeT, newParent *CallNodeT) {
	index := child.Index()
	parent := child.Parent()
	DetachNext(child)
	AttachNext(parent, newParent, index)
	MarkChanged(parent)
	AttachNext(newParent, child, 0)
	MarkChanged(child)
}

// Starting with the parent of NODE, set the SIMPLIFIED? flags of the
// ancestors of NODE to be #F.

func MarkChanged(node NodeT) {
	start := node
	for !node.IsNil() && node.IsSimplified() {
		node.SetIsSimplified(false)
		node = node.Parent()
	}
	for !node.IsNil() {
		if node.IsSimplified() {
			for !start.IsNil() {
				if IsCallNode(start) {
					fmt.Printf("Simplified %v %s\n", start.IsSimplified(), CallString(start.(*CallNodeT)))
				} else {
					fmt.Printf("Simplified %v ", start.IsSimplified())
					PpCps(start)
				}
				start = start.Parent()
			}
			PpCps(TopLambda)
			panic("IsSimplified bubble\n")
		}
		node = node.Parent()
	}
}

//----------------------------------------------------------------
// This is a utility for building up a sequence of calls.  The calls
// in a CallsT are not necessarily a single basic block, just that
// control flows from First to Last.

type CallsT struct {
	First    *CallNodeT // The first
	Last     *CallNodeT // and last calls in a block.
	recent   *CallNodeT // start of most recently added calls, for adding source
	contents string     // A debug string that lists the IDs of the calls
}

func MakeCalls() *CallsT {
	return &CallsT{}
}

// A 'final' call is one that has either no continuations or
// more than one.  New calls cannot be added to a block that
// ends with final call.

func (calls *CallsT) HasFinal() bool {
	return calls.Last != nil && len(calls.Last.Next) != 1
}

func (calls *CallsT) AppendCalls(more *CallsT) {
	calls.contents = fmt.Sprintf("%s [%s]", calls.contents, more.contents)
	// fmt.Printf("AppendCalls %s\n", calls.contents)
	if more == nil {
		return // nothing to do
	}
	if calls.First == nil {
		calls.First = more.First
	} else if more.First != nil {
		AttachNext(calls.Last, more.First)
	}
	calls.Last = more.Last
}

func (calls *CallsT) AddFirst(call *CallNodeT) {
	calls.contents = fmt.Sprintf("first.%d %s", call.Id, calls.contents)
	// fmt.Printf("AddFirst %s\n  %s\n", calls.contents, CallString(call))
	if calls.First == nil {
		calls.Last = call
	} else {
		AttachNext(call, calls.First)
	}
	calls.First = call
}

func (calls *CallsT) AppendCall(call *CallNodeT) {
	calls.contents = fmt.Sprintf("%s %d", calls.contents, call.Id)
	// fmt.Printf("AppendCall %s\n  %s\n", calls.contents, CallString(call))
	if calls.First == nil {
		calls.First = call
	} else {
		AttachNext(calls.Last, call)
	}
	calls.Last = call
}

// Set a new last call in a block.

func (calls *CallsT) SetLast(call *CallNodeT) {
	calls.contents = fmt.Sprintf("%s last.%d", calls.contents, call.Id)
	// fmt.Printf("SetLast %s\n  %s\n", calls.contents, CallString(call))
	if calls.First == nil {
		calls.First = call
	}
	calls.Last = call
}

func (calls *CallsT) SetLastSource(source token.Pos) {
	for call := calls.recent; ; call = call.Next[0] {
		call.source = source
		for _, vart := range call.Outputs {
			if vart != nil && vart.Source == 0 {
				vart.Source = source
			}
		}
		if call == calls.Last {
			break
		}
	}
}

// Various utilities calls for making nodes.

type CompilatorT interface {
	ToCps(args []NodeT, resultVars []*VariableT, calls *CallsT)
}

func (calls *CallsT) AddCall(primop PrimopT, outputs []*VariableT, inputs []NodeT) {
	oldLast := calls.Last
	switch primop := primop.(type) {
	case CompilatorT:
		primop.ToCps(inputs, outputs, calls)
	default:
		calls.AppendCall(MakeCall(primop, outputs, inputs...))
	}
	if oldLast == nil {
		calls.recent = calls.First
	} else {
		calls.recent = oldLast.Next[0]
	}
}

func (calls *CallsT) AddPrimopVarsCall(primopName string, outputs []*VariableT, inputs ...NodeT) {
	calls.AddCall(LookupPrimop(primopName), outputs, inputs)
}

func (calls *CallsT) BuildCall(primopName string, outputName string, outputType types.Type, inputs ...any) *VariableT {
	output := MakeVariable(outputName, outputType)
	calls.AddCall(LookupPrimop(primopName), []*VariableT{output}, Map(Nodeify, inputs))
	return output
}

func (calls *CallsT) BuildVarCall(primopName string, output *VariableT, inputs ...any) {
	calls.AddCall(LookupPrimop(primopName), []*VariableT{output}, Map(Nodeify, inputs))
}

func (calls *CallsT) BuildNoOutputCall(primopName string, inputs ...any) {
	nodeInputs := Map(Nodeify, inputs)
	if primopName == "cellSet" && nodeInputs[1].NodeType() == CallNode {
		nodeInputs[1].(*CallNodeT).Name = nodeInputs[0].(*ReferenceNodeT).Variable.Name
	}
	calls.AddCall(LookupPrimop(primopName), nil, nodeInputs)
}

func (calls *CallsT) BuildFinalCall(primopName string, exits int, args ...any) *CallNodeT {
	argNodes := Map(Nodeify, args)
	call := MakeCall(LookupPrimop(primopName), nil, argNodes[exits:]...)
	call.Next = make([]*CallNodeT, exits)
	for i, next := range argNodes[0:exits] {
		AttachNext(call, next.(*CallNodeT), i)
	}
	calls.AppendCall(call)
	calls.recent = call
	return call
}

func Nodeify(rawSpec any) NodeT {
	switch spec := rawSpec.(type) {
	case NodeT:
		return spec
	case *VariableT:
		return MakeReferenceNode(spec)
	case int:
		return MakeLiteral(constant.MakeInt64(int64(spec)), types.Typ[types.Int])
	case bool:
		return MakeLiteral(constant.MakeBool(spec), types.Typ[types.Bool])
	default:
		panic(fmt.Sprintf("can't coerce to a node: %v", spec))
		return nil
	}
}

//----------------------------------------------------------------
// Substituting Values For Variables
//
// Substitute VAL for VAR.  If DETACH? is true then VAL should be detached
// and so can be used instead of a copy for the first substitution.
//
// If VAL is a reference to a variable named V, it was probably introduced by
// the CPS conversion code.  In that case, the variable is renamed with the
// name of VAR.  This helps considerably when debugging the compiler.

func Substitute(vart *VariableT, val NodeT, detachVal bool) {
	if val.NodeType() == ReferenceNode {
		newVar := val.(*ReferenceNodeT).Variable
		if newVar.Name == "v" {
			newVar.Name = vart.Name
		}
	}
	refs := vart.Refs
	vart.Refs = []*ReferenceNodeT{}
	if 0 < len(refs) {
		for i, ref := range refs {
			if i == 0 && detachVal {
				ReplaceInput(ref, DetachInput(val))
			} else {
				ReplaceInput(ref, CopyNodeTree(val))
			}
		}
	} else if detachVal {
		Erase(DetachInput(val))
	}
}

//----------------------------------------------------------------
// Copying Node Trees

// Copy the node-tree `node`.  This dispatches on the type of the node.
// Variables which have been copied have the copy in their `copy` field.

func CopyNodeTree(rawNode NodeT) NodeT {
	switch node := rawNode.(type) {
	case *CallNodeT:
		return copyCall(node)
	case *LiteralNodeT:
		return CopyLiteralNode(node)
	case *ReferenceNodeT:
		vart := node.Variable
		if vart.Copy != nil {
			vart = vart.Copy
		}
		result := MakeReferenceNode(vart)
		result.source = node.source
		return result
	default:
		panic("unknown node type")
	}
}

// The outputs' copies are put in their VARIABLE-FLAG while call is being copied.

func copyCall(node *CallNodeT) *CallNodeT {
	outputs := make([]*VariableT, len(node.Outputs))
	for i, oldVar := range node.Outputs {
		if oldVar != nil {
			newVar := copyVariable(oldVar)
			oldVar.Copy = newVar
			outputs[i] = newVar
		}
	}
	inputs := make([]NodeT, len(node.Inputs))
	for i, input := range node.Inputs {
		inputs[i] = CopyNodeTree(input)
	}
	newNode := MakeCall(node.Primop, outputs, inputs...)
	newNode.CallType = node.CallType
	newNode.source = node.source
	newNode.Next = make([]*CallNodeT, len(node.Next))
	for i, next := range node.Next {
		AttachNext(newNode, CopyNodeTree(next).(*CallNodeT), i)
	}
	for _, oldVar := range node.Outputs {
		if oldVar != nil {
			oldVar.Copy = nil
		}
	}
	if node.IsLambda() {
		Lambdas.Add(newNode)
	}
	return newNode
}

func copyVariable(oldVar *VariableT) *VariableT {
	newVar := MakeVariable(oldVar.Name, oldVar.Type)
	// Could use golang.org/x/exp.maps.Copy(newVar.Flags, oldVar.Flags)
	for k, v := range oldVar.Flags {
		newVar.Flags[k] = v
	}
	return newVar
}

//----------------------------------------------------------------
// Finding the lambda node called by CALL, JUMP, or RETURN

func IsCalledNode(node NodeT) bool {
	return !node.Parent().IsNil() && node == CalledNode(node.Parent())
}

func IsCalledRef(node *ReferenceNodeT) bool {
	return !node.Parent().IsNil() && node == CalledNode(node.Parent())
}

func CalledNode(node *CallNodeT) NodeT {
	if node.Primop.Name() == "jump" {
		return node.Inputs[0]
	}
	return nil
}

func CalledLambda(call *CallNodeT) *CallNodeT {
	rawCalledNode := call.Inputs[0]
	switch calledNode := rawCalledNode.(type) {
	case *CallNodeT:
		return calledNode
	case *ReferenceNodeT:
		vart := calledNode.Variable
		binder := vart.Binder
		switch binder.Primop.Name() {
		case "let", "letrec":
			for i := 0; ; i++ {
				if vart == binder.Outputs[i] {
					return binder.Inputs[i].(*CallNodeT)
				}
			}
		default:
			panic("unknown called-variable binding call " + CallString(binder))
		}
	default:
		panic("unknown called node type")
	}
	return nil
}

func lambdaBinding(call *CallNodeT) *VariableT {
	bindingCall := call.parent
	switch bindingCall.Primop.Name() {
	case "let", "letrec":
		return bindingCall.Outputs[call.index]
	default:
		panic("unknown lambda binding call")
	}
}

// Disconnect 'call' and return the variable it was bound to.

func unbindLambda(call *CallNodeT) *VariableT {
	binder := call.parent
	index := call.Index()
	vars := binder.Outputs
	vart := vars[index]
	vart.Binder = nil // safety
	binder.Outputs = append(vars[0:index], vars[index+1:]...)
	DetachInput(call)
	RemoveNullInputs(binder, len(binder.Inputs)-1)
	return vart
}

//----------------------------------------------------------------
// Replace `node` with the body of its continuation.

func RemoveCall(node *CallNodeT) {
	if len(node.Next) == 1 {
		ReplaceNext(node, DetachNext(node.Next[0]))
	} else {
		panic("removing a call with other then one next call")
	}
}

// Remove all of `lambda`s unused variables.

func RemoveUnusedOutputs(node *CallNodeT) {
	pred := func(vart *VariableT) bool {
		if vart.IsUsed() {
			return true
		} else {
			EraseVariable(vart)
			return false
		}
	}
	node.Outputs = Filter(pred, node.Outputs)
}

// Remove all inputs to `node` that are empty.  `inputCount` is the number of
// non-empty inputs.

func RemoveNullInputs(node *CallNodeT, inputCount int) {
	newInputs := make([]NodeT, inputCount)
	newIndex := 0
	for _, input := range node.Inputs {
		if !IsNil(input) {
			newInputs[newIndex] = input
			input.SetIndex(newIndex)
			newIndex += 1
			if newIndex == inputCount {
				break
			}
		}
	}
	node.Inputs = newInputs
	MarkChanged(node)
}

//----------------------------------------------------------------
// Checking the scoping of identifers

// Mark all ancestors of N with FLAG

func markAncestors(node NodeT, flag int) {
	for ; !IsNil(node); node = node.Parent() {
		node.SetFlag(flag)
	}
}

// Does N have an ancestor with a set flag?

func hasMarkedAncestor(node NodeT) bool {
	for ; !IsNil(node); node = node.Parent() {
		if node.Flag() != 0 {
			return true
		}
	}
	return false
}

// Does N have an ancestor with an unset flag?

func hasUnmarkedAncestor(node NodeT) bool {
	for ; !IsNil(node); node = node.Parent() {
		if node.Flag() == 0 {
			return true
		}
	}
	return false
}

// Is ancestor an ancestor of node?

func isAncestor(node NodeT, ancestor NodeT) bool {
	ancestor.SetFlag(1)
	result := hasMarkedAncestor(node)
	ancestor.SetFlag(0)
	return result
}

// Find the lowest ancestor of N that has a set flag

func markedAncestor(node NodeT) NodeT {
	for ; !IsNil(node); node = node.Parent() {
		if node.Flag() != 0 {
			return node
		}
	}
	return nil
}

// Unmark the ancestors of 'start', stopping when 'end' is reached

func unmarkAncestorsTo(start NodeT, end NodeT) {
	for node := start; node != end; node = node.Parent() {
		node.SetFlag(0)
	}
}

// Return the lowest node that is above all NODES

func leastCommonAncestor(nodes []NodeT) NodeT {
	top := nodes[0]
	markAncestors(top, 1)
	for i := 0; i < len(nodes); i++ {
		newTop := markedAncestor(nodes[i])
		unmarkAncestorsTo(top, newTop)
		top = newTop
	}
	markAncestors(top, 0)
	return top
}

//----------------------------------------------------------------
// Generic code for finding the basic blocks in a procedure.
//
// A basic block starts with a ProcLambda or JumpLambda or with a
// CallExit whose parent has two or more next calls.  It ends
// with the first following call that has other than one next call.

type BasicBlockT interface {
	initialize(start *CallNodeT, end *CallNodeT)
	addNext(next BasicBlockT)
	getEnd() *CallNodeT
}

func FindBasicBlocks[BB BasicBlockT](top *CallNodeT, makeBlock func() BB) []BB {
	blocks := []BB{}
	var findBlock func(start *CallNodeT) BB
	findBlock = func(start *CallNodeT) BB {
		block := makeBlock()
		start.Block = block
		blocks = append(blocks, block)
		end := start
		for len(end.Next) == 1 {
			for _, rawInput := range end.Inputs {
				if IsCallNode(rawInput) {
					input := rawInput.(*CallNodeT)
					if input.CallType == JumpLambda {
						findBlock(input)
					}
				}
			}
			end = end.Next[0]
		}
		for _, next := range end.Next {
			block.addNext(findBlock(next))
		}
		block.initialize(start, end)
		return block
	}
	findBlock(top)
	for _, block := range blocks {
		end := block.getEnd()
		if end.Primop.Name() == "jump" {
			block.addNext(CalledLambda(end).Block)
		}
	}
	return blocks
}

// A basic block struct for when only the block structure is needed.

type BlockT struct {
	Start    *CallNodeT
	End      *CallNodeT
	Next     []*BlockT
	Previous []*BlockT
}

func MakeBlock() *BlockT {
	return &BlockT{}
}

func (block *BlockT) initialize(start *CallNodeT, end *CallNodeT) {
	block.Start = start
	block.End = end
}

func (block *BlockT) addNext(rawNext BasicBlockT) {
	next := rawNext.(*BlockT)
	block.Next = append(block.Next, next)
	next.Previous = append(next.Previous, block)
}

func (block *BlockT) getEnd() *CallNodeT {
	return block.End
}

func ContainingBlock(node NodeT) BasicBlockT {
	var call *CallNodeT
	if IsCallNode(node) {
		call = node.(*CallNodeT)
	} else {
		call = node.Parent()
	}
	for ; call != nil; call = call.parent {
		if call.Block != nil {
			return call.Block
		}
	}
	PpCps(node)
	panic("no basic block")
	return nil
}

//----------------------------------------------------------------
// Simple queues

type QueueT[T any] struct {
	value T
	next  *QueueT[T]
}

func (queue *QueueT[T]) Empty() bool {
	return queue.next == nil
}

func (queue *QueueT[T]) Enqueue(value T) {
	tail := queue.next
	newTail := &QueueT[T]{value: value}
	if tail == nil {
		newTail.next = newTail
	} else {
		newTail.next = tail.next
		tail.next = newTail
	}
	queue.next = newTail
}

func (queue *QueueT[T]) Dequeue() T {
	if queue.next == nil {
		panic("dequeue on empty queue")
	}
	tail := queue.next
	head := tail.next
	if head == tail {
		queue.next = nil
	} else {
		tail.next = head.next
	}
	return head.value
}

//----------------------------------------------------------------
// Array comprehension routines borrowed from Scheme.

func Every[T any](predicate func(T) bool, slice []T) bool {
	for _, x := range slice {
		if !predicate(x) {
			return false
		}
	}
	return true
}

func Any[T any](predicate func(T) bool, slice []T) bool {
	for _, x := range slice {
		if predicate(x) {
			return true
		}
	}
	return false
}

func Filter[T any](predicate func(T) bool, slice []T) []T {
	result := []T{}
	for _, x := range slice {
		if predicate(x) {
			result = append(result, x)
		}
	}
	return result
}

func Map[S any, T any](function func(S) T, slice []S) []T {
	result := make([]T, len(slice))
	for i, x := range slice {
		result[i] = function(x)
	}
	return result
}

func Push[T any](slice *[]T, thing T) {
	*slice = append(*slice, thing)
}

func PushSlice[T any](slice *[]T, things []T) {
	*slice = append(*slice, things...)
}

func Last[T any](slice []T) T {
	return slice[len(slice)-1]
}
