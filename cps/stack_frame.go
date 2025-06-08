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

func AddStackFrames(proc *CallNodeT, frameType types.Type) {
	blocks := FindBasicBlocks[*frameBlockT](proc, makeFrameBlock)
	findDominators(blocks[0],
		func(b *frameBlockT) []*frameBlockT { return b.next },
		func(b *frameBlockT, d *frameBlockT) {
			b.dominator = d
			Push(&d.dominatees, b)
		})

	// Find loop headers by looking for edges whose tail dominates
	// their head.  All blocks on paths upwards from the tail to the
	// head are in the loop.
	loopHeaders := []*frameBlockT{}
	for _, block := range blocks {
		for _, n := range block.next {
			for dom := block.dominator; dom != blocks[0]; dom = dom.dominator {
				if n == dom {
					if len(n.backEdges) == 0 {
						Push(&loopHeaders, n)
					}
					Push(&n.backEdges, block)
					findLoopBlocks(n, block)
					break
				}
			}
		}
	}

	//	for _, block := range blocks[1:] {
	//		block.loopHeader = blocks[0]
	//	}

	// Sort loops from biggest to smallest.
	slices.SortFunc(loopHeaders,
		func(x, y *frameBlockT) int {
			return len(y.loopBlocks) - len(x.loopBlocks)
		})

	// The sorting means that outer loops are processed before inner
	// loops, so that each loop ends up with its proper depth and
	// immediate parent.
	for _, header := range loopHeaders {
		header.loopDepth += 1
		header.loopParent = header.loopHeader
		header.loopHeader = header
		for child := range header.loopBlocks {
			child.loopHeader = header
			child.loopDepth = header.loopDepth
		}
	}

	//	for _, loop := range loopHeaders {
	//		fmt.Printf("loop: %s %d (%s)", loop, loop.loopDepth, loop.loopParent)
	//		for block := range loop.loopBlocks {
	//			fmt.Printf(" %s", block)
	//		}
	//		fmt.Printf("\n")
	//	}

	contVar := proc.Outputs[0]
	frameVar := MakeVariable("frame", frameType)
	frameVar.Binder = proc
	proc.Outputs = append([]*VariableT{contVar, frameVar}, proc.Outputs[1:]...)

	makeCellCall := proc.Next[0]
	procFrameVar := addFramePush(proc, frameVar)
	insertCall(proc.Next[0], "makeCell", procFrameVar)
	blocks[0].frameVar = procFrameVar

	// Add a cell for each loop's saved frame pointer.
	for _, header := range loopHeaders {
		outerFrameVar := procFrameVar
		if header.loopParent != nil {
			outerFrameVar = header.loopParent.frameVar
		}
		header.frameVar = addFramePush(header.start, outerFrameVar)
		insertCall(makeCellCall, "makeCell", header.frameVar)
	}

	for _, block := range blocks {
		addStackFrameRefs(block, procFrameVar)
	}

	for _, block := range blocks {
		block.start.Block = nil
	}

	// fmt.Printf("======== frames ========\n")
	// PpCps(proc)
	// fmt.Printf("====== end frames ======\n")
}

// Walk up the 'previous' links from 'block' until you hit 'header',
// adding everything to 'header's loopBlocks.

func findLoopBlocks(header *frameBlockT, block *frameBlockT) {
	if block == header || header.loopBlocks.Contains(block) {
		return
	}
	header.loopBlocks.Add(block)
	for _, prev := range block.previous {
		findLoopBlocks(header, prev)
	}
}

type frameBlockT struct {
	start    *CallNodeT
	end      *CallNodeT
	next     []*frameBlockT
	previous []*frameBlockT

	dominator  *frameBlockT
	dominatees []*frameBlockT
	loopHeader *frameBlockT // nil if not in a loop
	loopDepth  int

	// Only loop headers have these.
	backEdges  []*frameBlockT
	loopBlocks util.SetT[*frameBlockT] // all blocks in the loop
	loopParent *frameBlockT            // outer loop, if any
	frameVar   *VariableT
}

func makeFrameBlock() *frameBlockT {
	return &frameBlockT{loopBlocks: util.NewSet[*frameBlockT]()}
}

func (block *frameBlockT) initialize(start *CallNodeT, end *CallNodeT) {
	block.start = start
	block.end = end
}

func (block *frameBlockT) addNext(rawNext BasicBlockT) {
	next := rawNext.(*frameBlockT)
	Push(&block.next, next)
	Push(&next.previous, block)
}

func (block *frameBlockT) getEnd() *CallNodeT {
	return block.end
}

func (block *frameBlockT) String() string {
	return fmt.Sprintf("%s_%d", block.start.Name, block.start.Id)
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

func addStackFrameRefs(block *frameBlockT, procFrameVar *VariableT) {
	var frameVar *VariableT
	if block.loopHeader == nil {
		frameVar = procFrameVar
	} else {
		frameVar = block.loopHeader.frameVar
	}
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
	if len(block.end.Next) == 2 {
		for _, next := range block.next {
			if next.loopHeader != block.loopHeader {
				addFramePop(next.start, frameVar)
			}
		}
	} else if len(block.end.Next) == 0 {
		end := block.end
		switch end.Primop.Name() {
		case "return":
			addFramePop(end, procFrameVar)
		case "jump":
			target := block.next[0]
			if target.loopDepth < block.loopDepth || target == block.loopHeader {
				addFramePop(end, jumpFrameVar(block, target))
			}
		default:
			panic("unexpected no-next call " + end.String())
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

func jumpFrameVar(from *frameBlockT, to *frameBlockT) *VariableT {
	// fmt.Printf("jump from %s(%d) to %s(%d)\n", from, from.loopDepth, to, to.loopDepth)
	delta := from.loopDepth - to.loopDepth
	for ; 0 < delta; delta-- {
		from = from.loopHeader.loopParent
	}
	return from.loopHeader.frameVar
}

func addFramePop(call *CallNodeT, frameVar *VariableT) {
	parent := call.Parent()
	temp := MakeVariable("frame", frameVar.Type)
	insertCall(call, "cellRef", temp, frameVar)
	insertCall(call, "framePop", nil, temp)
	MarkChanged(parent)
}

// 'procCall' gets the frame variable right after the procedure, to
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
