// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package cps

import (
	"fmt"
	"math"
)

// Problems this solves (or at least helps with):
// - If a block contains only a jump to another block we want to
//   to jump directly the second block and not generate code for
//   the unnecessary jump.
// - The size of a jump or branch instruction may depend on how far
//   away the target is.  How far away the target is may depend on
//   the size of jump and branch instructions.  What we do is
//   determine the size of each jump or branch based on a conservative
//   estimate of the target's distance.  We then calculate the actual
//   distances based on these sizes.  This can result in a large
//   instruction being used where a small one would have worked, but
//   only rarely.

// 'T' is the type of the instructions.
// The units for instruction sizes are determined by the back end.

type CodeGeneratorT[T any] interface {
	// Does not generate any final jump or branch instruction.
	GenerateCall(call *CallNodeT) ([]T, int)
	// Offsets may be exact or conservative.
	JumpSize(call *CallNodeT, offset int, offsets []int) int
	// Generates the final jump or branch instruction.
	// Offsets are known.  This must add jumpSize instructions.
	GenerateJump(call *CallNodeT, offset int, offsets []int, jumpSize int) []T
}

func Assemble[T any](top *CallNodeT, generator CodeGeneratorT[T]) []*CodeBlockT[T] {
	blocks := FindBasicBlocks[*CodeBlockT[T]](top, makeCodeBlock[T])
	for _, block := range blocks {
		totalSize := 0
		for call := block.start; ; call = call.Next[0] {
			insts, size := generator.GenerateCall(call)
			Push(&block.Instructions, insts)
			totalSize += size
			if call == block.end {
				if call.Primop.Name() == "jump" {
					block.hasJump = true
				} else if 2 <= len(call.Next) {
					block.hasBranch = true
				}
				break
			}
		}
		block.size = totalSize
	}
	// TODO: Figure out a better block order.
	for i, block := range blocks[1:] {
		blocks[i].fallThrough = block
	}
	// Empty blocks that end with a jump can be elided.  Other jumps
	// and branches get a maximum size estimate.
	for _, block := range blocks {
		if block.hasJump &&
			block.size == 0 &&
			block.labelBlock() == block.fallThroughBlock() {

			block.hasJump = false
		} else if block.hasJump || block.hasBranch {
			block.jumpSize = generator.JumpSize(
				block.end,
				0,
				nextOffsets(block, true))
		}
	}
	// Set the offsets based on our upper bound on the sizes of blocks.
	setOffsets(blocks)
	// Get the actual sizes of blocks.
	for _, block := range blocks {
		if block.hasJump || block.hasBranch {
			block.jumpSize = generator.JumpSize(
				block.end,
				block.offset+block.size,
				nextOffsets(block, false))
		}
	}
	// Set the offsets to be their real values.
	setOffsets(blocks)
	// Generate code for jumps now that we know the actual offsets.
	for _, block := range blocks {
		if block.hasJump || block.hasBranch {
			insts := block.Instructions
			moreInsts := generator.GenerateJump(
				block.end,
				block.offset+block.size,
				nextOffsets(block, false),
				block.jumpSize)
			instsLoc := &insts[len(insts)-1]
			*instsLoc = append(*instsLoc, moreInsts...)
		}
	}
	return blocks
}

func nextOffsets[T any](block *CodeBlockT[T], useMax bool) []int {
	call := block.end
	targets := call.Next
	if len(call.Next) == 0 {
		targets = []*CallNodeT{block.next[0].start}
	}
	offsets := make([]int, len(targets))
	fallThrough := block.fallThrough
	for i, next := range targets {
		nextBlock := next.Block.(*CodeBlockT[T]).labelBlock()
		if nextBlock != fallThrough {
			if useMax {
				offsets[i] = math.MaxInt
			} else {
				offsets[i] = nextBlock.offset
			}
		}
	}
	return offsets
}

func setOffsets[T any](blocks []*CodeBlockT[T]) {
	offset := 0
	for _, block := range blocks {
		block.offset = offset
		offset += block.size
		if block.hasJump || block.hasBranch {
			offset += block.jumpSize
		}
	}
}

type CodeBlockT[T any] struct {
	next     []*CodeBlockT[T] // the usual basic block fields
	previous []*CodeBlockT[T]
	start    *CallNodeT
	end      *CallNodeT

	Instructions [][]T
	size         int
	jumpSize     int
	offset       int
	fallThrough  *CodeBlockT[T]
	hasJump      bool
	hasBranch    bool
}

func makeCodeBlock[T any]() *CodeBlockT[T] {
	return &CodeBlockT[T]{}
}

func (block *CodeBlockT[T]) initialize(start *CallNodeT, end *CallNodeT) {
	block.start = start
	block.end = end
}

func (block *CodeBlockT[T]) addNext(rawNext BasicBlockT) {
	next := rawNext.(*CodeBlockT[T])
	Push(&block.next, next)
	Push(&next.previous, block)
}

func (block *CodeBlockT[T]) getEnd() *CallNodeT {
	return block.end
}

func (block *CodeBlockT[T]) Offset() int {
	return block.offset
}

func (block *CodeBlockT[T]) String() string {
	return fmt.Sprintf("%s_%d", block.start.Name, block.start.Id)
}

func (block *CodeBlockT[T]) labelBlock() *CodeBlockT[T] {
	if block.size == 0 && block.hasJump {
		return block.next[0].labelBlock()
	}
	return block
}

func (block *CodeBlockT[T]) fallThroughBlock() *CodeBlockT[T] {
	if block.size == 0 && block.hasJump {
		return block.fallThrough.fallThroughBlock()
	}
	return block
}

func (block *CodeBlockT[T]) LastCall() *CallNodeT {
	return block.end
}
