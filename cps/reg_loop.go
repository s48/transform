// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Liveness and loops for register allocation.  See the description at
// the top of reg_alloc.go.

package cps

import (
	"maps"
	"slices"

	"github.com/s48/transform/util"
)

type regLoopT struct {
	header     *regBlockT
	parent     *regLoopT // next outer loop, if any
	loopDepth  int
	blocks     []*regBlockT          // including those in inner loops
	referenced util.SetT[*VariableT] // variables bound or referenced in the loop

	// Links that cover the entire loop, for variables that are live in
	// the loop but not referenced in it.  Variables that are not
	// referenced in the next outer loop have their links there.
	links map[*VariableT]*linkT
}

// No loop has depth zero.
func (loop *regLoopT) depth() int {
	if loop == nil {
		return 0
	}
	return loop.loopDepth
}

// The link for a variable that is live in this loop and is not referenced
// either in it or in some loop that contains it, or nil if there isn't one.
func (loop *regLoopT) link(vart *VariableT) *linkT {
	for ; loop != nil; loop = loop.parent {
		link := loop.links[vart]
		if link != nil {
			return link
		}
	}
	return nil
}

// The innermost loop containing both blocks, or nil.
func commonLoop(x *regBlockT, y *regBlockT) *regLoopT {
	for loop := x.loop; loop != nil; loop = loop.parent {
		if slices.Contains(loop.blocks, y) {
			return loop
		}
	}
	return nil
}

func (block *regBlockT) calls() []*CallNodeT {
	calls := []*CallNodeT{}
	for call := block.end; len(calls) < block.callCount; call = call.parent {
		Push(&calls, call)
	}
	slices.Reverse(calls)
	return calls
}

// Calls the procedures with every variable that is referenced or bound in
// the block and is in a register, in execution order.
func (block *regBlockT) walkVars(reference func(*VariableT), bind func(*VariableT)) {
	for i, call := range block.calls() {
		for _, input := range getInputs(call, block.inputSpecs[i]) {
			reference(input.variable)
		}
		for j, spec := range block.outputSpecs[i] {
			if spec != nil {
				bind(call.Outputs[j])
			}
		}
	}
}

// Variables live at the end of the block.
func (block *regBlockT) liveOut() util.SetT[*VariableT] {
	result := util.NewSet[*VariableT]()
	for _, next := range block.next {
		result.AddSet(next.liveIn)
	}
	return result
}

// Sets the liveIn field of each block.
func findLiveIn(blocks []*regBlockT) {
	bound := map[*regBlockT]util.SetT[*VariableT]{}
	for _, block := range blocks {
		block.liveIn = util.NewSet[*VariableT]()
		bound[block] = util.NewSet[*VariableT]()
		block.walkVars(
			func(vart *VariableT) {
				if !bound[block].Contains(vart) {
					block.liveIn.Add(vart)
				}
			},
			func(vart *VariableT) { bound[block].Add(vart) })
	}
	// Going backwards only repeats if there are loops.
	for changed := true; changed; {
		changed = false
		for _, block := range slices.Backward(blocks) {
			size := len(block.liveIn)
			for _, next := range block.next {
				for vart := range next.liveIn {
					if !bound[block].Contains(vart) {
						block.liveIn.Add(vart)
					}
				}
			}
			if len(block.liveIn) != size {
				changed = true
			}
		}
	}
}

// Finds the loops and makes the links for variables that are live in a
// loop but not referenced in it.  These are treated as being outside the
// loop, as they are the concern of the code around it.
//
// Any variable that is live in a loop and not bound in it is live at the
// loop's header and throughout the loop.

func makeLoopLinks(blocks []*regBlockT) {
	for _, loop := range findRegLoops(blocks) {
		for _, vart := range sortedVars(maps.Keys(loop.header.liveIn)) {
			if loop.referenced.Contains(vart) || loop.parent.link(vart) != nil {
				continue
			}
			link := &linkT{
				id:        nextLinkId(),
				variable:  vart,
				loopDepth: loop.parent.depth(),
			}
			for _, block := range slices.Backward(loop.blocks) {
				link.liveRange.add(intervalT{block.startIndex, block.endIndex})
			}
			loop.links[vart] = link
		}
	}
}

// Returns the loops with outer loops before inner ones.
func findRegLoops(blocks []*regBlockT) []*regLoopT {
	loops := map[*regBlockT]*regLoopT{}
	parents := map[*regLoopT]*regBlockT{}
	getLoop := func(header *regBlockT) *regLoopT {
		loop := loops[header]
		if loop == nil {
			loop = &regLoopT{
				header:     header,
				referenced: util.NewSet[*VariableT](),
				links:      map[*VariableT]*linkT{},
			}
			loops[header] = loop
		}
		return loop
	}
	headers := FindLoopBlocks(
		blocks,
		func(block *regBlockT) []*regBlockT { return block.next },
		func(block *regBlockT, header *regBlockT, parent *regBlockT, depth int) {
			if header == nil {
				return
			}
			block.loop = getLoop(header)
			if header == block {
				block.loop.loopDepth = depth
				parents[block.loop] = parent
			}
		})
	result := []*regLoopT{}
	for _, header := range headers {
		loop := loops[header]
		loop.parent = loops[parents[loop]] // nil if there is no parent
		Push(&result, loop)
	}
	for _, block := range blocks {
		for loop := block.loop; loop != nil; loop = loop.parent {
			Push(&loop.blocks, block)
			block.walkVars(
				func(vart *VariableT) { loop.referenced.Add(vart) },
				func(vart *VariableT) { loop.referenced.Add(vart) })
		}
	}
	slices.SortStableFunc(result, func(x, y *regLoopT) int { return x.loopDepth - y.loopDepth })
	return result
}
