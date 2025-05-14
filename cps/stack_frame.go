// Copyright 2025 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// The goal here is to deallocate stack-allocated objects when on
// procedure returns and loop back edges.  Deallocation is done by
// saving and restoring a stack allocation pointer.
//     frame := pushFrame()
//     ...
//     popFrame(frame)
// pushFrame returns the current stack allocation pointer and popFrame
// sets it.  In order to preserve the ordering of pushes, allocations
// and pops across optimizations the current frame pointer is an
// explicit argument to pushFrame and to all stack allocation
// functions.  Procedures get passed the current frame as an
// additional argument.
//     frameB := pushFrame(frameA)
//     ...
//     x := make(size, frameB)
//     ...
//     popFrame(frameB)
// The frame values need to follow the control flow, which doesn't
// necessarily line up with the lexical scoping, so they are stored in
// cells.  The cells will be elided by the conversion to SSA.

package cps

import (
	"fmt"
	"slices"

	"go/types"

	"github.com/s48/transform/util"
)

// Jumps can only be within a strongly-connected component or to
// another component further down the list.  There are no jumps
// to earlier components.

func AddStackFrames(proc *CallNodeT, frameType types.Type) {
	blocks := FindBasicBlocks[*frameBlockT](proc, makeFrameBlock)
	components := util.StronglyConnectedComponents(
		blocks,
		func(block *frameBlockT) []*frameBlockT { return block.next })
	for _, block := range blocks {
		node := block.start.Parent()
		for ; node != nil; node = node.Parent() {
			if node.Block != nil {
				parent := node.Block.(*frameBlockT)
				block.parent = parent
				break
			}
		}
	}

	contVar := proc.Outputs[0]
	frameVar := MakeVariable("frame", frameType)
	frameVar.Binder = proc
	proc.Outputs = append([]*VariableT{contVar, frameVar}, proc.Outputs[1:]...)

	makeCellCall := proc.Next[0]
	procFrameVar := addFramePush(proc, frameVar)
	insertCall(proc.Next[0], "makeCell", procFrameVar)
	addStackFrameRefs(blocks[0], procFrameVar, procFrameVar)

	for i, component := range components {
		for _, block := range component {
			block.component = i
		}
	}

	for _, component := range components[1:] {
		if len(component) == 1 {
			block := component[0]
			addStackFrameRefs(block, block.parent.frameVar, procFrameVar)
		} else {
			frameVar := addLoopStackFrame(component)
			if frameVar != nil {
				insertCall(makeCellCall, "makeCell", frameVar)
				for _, block := range component {
					addStackFrameRefs(block, frameVar, procFrameVar)
				}
			}
		}
	}

	for _, block := range blocks {
		block.start.Block = nil
	}

	// fmt.Printf("======== frames ========\n")
	// PpCps(proc)
	// fmt.Printf("====== end frames ======\n")
}

// We're looking to see if the loop has a single entry point.  If so,
// we can add a frame stack push there and pop it off on all back
// edges.
// If not, then we have an irreducible loop and it won't get its own
// frame.  Fortunately those are rare and require gotos to create.

func addLoopStackFrame(blocks []*frameBlockT) *VariableT {
	var head *frameBlockT
	for _, block := range blocks {
		for _, prev := range block.previous {
			if prev.component < block.component {
				if head == nil {
					head = block
				} else {
					fmt.Printf("frame lost %s_%d %s_%d",
						head.start.Name, head.start.Id,
						block.start.Name, block.start.Id)
					printFrameBlocks(blocks, head)
					return nil
				}
			}
		}
	}
	if head == nil {
		panic("stack frames: loop has no head")
	}
	head.isHead = true
	frameVar := addFramePush(head.start, head.parent.frameVar)
	for _, block := range blocks {
		block.frameVar = frameVar
	}

	// fmt.Printf("frame %s_%d", head.start.Name, head.start.Id)
	// printFrameBlocks(blocks, head)
	return frameVar
}

type frameBlockT struct {
	start    *CallNodeT
	end      *CallNodeT
	next     []*frameBlockT
	previous []*frameBlockT

	parent    *frameBlockT // lexical parent
	component int
	isHead    bool
	frameVar  *VariableT
}

func makeFrameBlock() *frameBlockT {
	return &frameBlockT{}
}

func (block *frameBlockT) initialize(start *CallNodeT, end *CallNodeT) {
	block.start = start
	block.end = end
}

func (block *frameBlockT) addNext(rawNext BasicBlockT) {
	next := rawNext.(*frameBlockT)
	block.next = append(block.next, next)
	next.previous = append(next.previous, block)
}

func (block *frameBlockT) getEnd() *CallNodeT {
	return block.end
}

func printFrameBlocks(blocks []*frameBlockT, skip *frameBlockT) {
	for _, block := range blocks {
		if block != skip {
			fmt.Printf(" %s_%d", block.start.Name, block.start.Id)
		}
	}
	fmt.Printf("\n")
}

// How primops tell us that they do stack allocation.
type StackAllocator interface {
	IsStackAllocator() bool
}

func IsStackAllocator(primop PrimopT) bool {
	switch primop.(type) {
	case StackAllocator:
		return true
	default:
		return false
	}
}

func addStackFrameRefs(block *frameBlockT, frameVar *VariableT, procFrameVar *VariableT) {
	block.frameVar = frameVar
	for call := block.start; call != block.end; call = call.Next[0] {
		for _, node := range call.Inputs {
			if IsProcLambdaNode(node) {
				AddStackFrames(node.(*CallNodeT), frameVar.Type)
			}
		}
		if IsStackAllocator(call.Primop) {
			addFrameInput(call, frameVar)
		}
	}
	if len(block.end.Next) == 0 {
		call := block.end
		switch call.Primop.Name() {
		case "jump":
			target := CalledLambda(call).Block.(*frameBlockT)
			//			fmt.Printf("jump block %s_%d(%d) %s target %s_%d(%d) %s\n",
			//				block.start.Name, block.start.Id, block.component, block.frameVar,
			//				target.start.Name, target.start.Id, target.component, target.frameVar)
			if target.component < block.component ||
				target.component == block.component && target.isHead {
				addFramePop(call, jumpFrameVar(block, target))
			}
		case "return":
			addFramePop(call, procFrameVar)
		default:
			panic("unexpected no-next call " + call.String())
		}
	}
}

func addFramePush(call *CallNodeT, outerFrameVar *VariableT) *VariableT {
	frameType := outerFrameVar.Type
	_, isCell := outerFrameVar.Flags["cell"]
	if isCell {
		temp := MakeVariable("frame", frameType)
		call = insertCall(call.Next[0], "cellRef", temp, outerFrameVar)
		outerFrameVar = temp
	}
	frameVar := MakeVariable("frame", frameType)
	call = insertCall(call.Next[0], "framePush", frameVar, outerFrameVar)
	cellFrameVar := MakeCellVariable("frame", frameType)
	insertCall(call.Next[0], "cellSet", nil, cellFrameVar, frameVar)
	MarkChanged(call)
	return cellFrameVar
}

// This needs to figure out when you're jumping out of two or frames
// at the same time.  First I need a test that does that.

func jumpFrameVar(from *frameBlockT, to *frameBlockT) *VariableT {
	// fmt.Printf("jump from %s to %s\n", from.frameVar, to.frameVar)
	return from.frameVar
}

func addFramePop(call *CallNodeT, frameVar *VariableT) {
	parent := call.Parent()
	temp := MakeVariable("frame", frameVar.Type)
	insertCall(call, "cellRef", temp, frameVar)
	insertCall(call, "framePop", nil, temp)
	MarkChanged(parent)
}

// 'procCall' gets the frame variable right after the procedures, to
// line up with the procedure's frame argument.  For everything else
// it is put at the end.

func addFrameInput(call *CallNodeT, frameVar *VariableT) {
	temp := MakeVariable("v", frameVar.Type)
	insertCall(call, "cellRef", temp, frameVar)
	inputs := call.Inputs
	index := len(inputs)
	if call.Primop.Name() == "procCall" {
		index = 1
		call.Inputs = slices.Concat(inputs[:1], []NodeT{nil}, inputs[1:])
		for i, input := range call.Inputs[2:] {
			input.SetIndex(i + 2)
		}
	} else {
		call.Inputs = append(inputs, nil)
	}
	AttachInput(call, index, MakeReferenceNode(temp))
}

// Add a call ahead of 'next' that calls 'primop' on 'args' and has
// 'result' as an output, if non-nil.

func insertCall(next *CallNodeT,
	primop string,
	result *VariableT,
	args ...*VariableT) *CallNodeT {

	var results []*VariableT
	if result != nil {
		results = []*VariableT{result}
	}
	argNodes := make([]NodeT, len(args))
	for i, arg := range args {
		argNodes[i] = MakeReferenceNode(arg)
	}
	call := MakeCall(LookupPrimop(primop), results, argNodes...)
	parent := next.Parent()
	index := next.Index()
	DetachNext(next)
	AttachNext(parent, call, index)
	AttachNext(call, next)
	return call
}
