
package cps

import (
	"fmt"
)

type InstructionT interface {
	SizeInBytes() uint
}

type CodeGeneratorT interface {
	GenerateCall(call *CallNodeT) []InstructionT
	GenerateJump(call *CallNodeT, next *CallNodeT) []InstructionT
}

// Want to find jumps-to-jumps.

func assemble(top *CallNodeT, generator CodeGeneratorT) []*CodeBlockT {
	blocks := FindBasicBlocks[*CodeBlockT](top, makeCodeBlock)
	for _, block := range blocks {
		call := block.start
		for call != block.end {
			Push(&block.Instructions, generator.GenerateCall(call))
			call = call.Next[0]
		}
		if call.Primop.Name() == "jump" || 2 <= len(call.Next) {
			block.hasJump = true
		} else {
			Push(&block.Instructions, generator.GenerateCall(call))
		}
	}
	// TODO: figure out a better block order and annotate jumps to jumps.
	// A block with only a jump that is only jumped to may become empty.
	// A jump lambda may become fall through if it is placed after a
	// jump to it.
	nonempty := make([]*CodeBlockT, 0, len(blocks))
	for _, block := range blocks {
		if 0 < len(block.Instructions) || block.hasJump {
			Push(&nonempty, block)
		}
	}
	last := nonempty[len(nonempty) - 1]
	for i, block := range nonempty {
		if block.hasJump {
			var next *CallNodeT
			if block != last {
				next = nonempty[i + 1].start
			}
			generator.GenerateJump(block.end, next)
		}
	}
	return blocks
}

type CodeBlockT struct {
	next     []*CodeBlockT // the usual basic block fields
	previous []*CodeBlockT
	start    *CallNodeT
	end      *CallNodeT

	Instructions [][]InstructionT
	StartOffset uint
	SizeInBytes uint

	seen bool
	hasJump bool
}

func makeCodeBlock() *CodeBlockT {
	return &CodeBlockT{}
}

func (block *CodeBlockT) initialize(start *CallNodeT, end *CallNodeT) {
	block.start = start
	block.end = end
}

func (block *CodeBlockT) addNext(rawNext BasicBlockT) {
	next := rawNext.(*CodeBlockT)
	Push(&block.next, next)
	Push(&next.previous, block)
}

func (block *CodeBlockT) getEnd() *CallNodeT {
	return block.end
}

func (block *CodeBlockT) String() string {
	return fmt.Sprintf("%s_%d", block.start.Name, block.start.Id)
}
