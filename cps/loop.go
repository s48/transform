// Copyright 2025 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Determining the programs loop structure.  This can't yet handle
// irreducible call graphs.

package cps

import (
	"slices"

	"github.com/s48/transform/util"
)

type loopBlockT struct {
	next     []*loopBlockT // the usual basic block fields
	previous []*loopBlockT

	dominator  *loopBlockT
	loopHeader *loopBlockT // nil if not in a loop
	loopDepth  int

	// Only loop headers have these.
	backEdges  []*loopBlockT
	loopBlocks util.SetT[*loopBlockT] // all blocks in the loop
	loopParent *loopBlockT            // outer loop, if any
}

// This annotates 'theirBlocks' with:
//  - loopHeader: the header block for whatever loop the block is in
//                (for loop headers this points to itself)
//  - loopParent: the next outer loop, only set if this is a header
//  - loopDepth: loop nesting depth
// The return value is a slice containing the loop headers.

func FindLoopBlocks[T any](
	theirBlocks []*T,
	next func(*T) []*T,
	setResult func(block *T, loopHeader *T, loopParent *T, loopDepth int)) []*T {

	blocks := make([]*loopBlockT, len(theirBlocks))
	themToUs := map[*T]*loopBlockT{}
	usToThem := map[*loopBlockT]*T{}
	for i, theirs := range theirBlocks {
		block := &loopBlockT{loopBlocks: util.NewSet[*loopBlockT]()}
		blocks[i] = block
		themToUs[theirs] = block
		usToThem[block] = theirs
	}
	for i, block := range blocks {
		theirNext := next(theirBlocks[i])
		block.next = make([]*loopBlockT, len(theirNext))
		for j, theirs := range theirNext {
			ours := themToUs[theirs]
			block.next[j] = ours
			Push(&ours.previous, block)
		}
	}

	findDominators(
		blocks[0],
		func(b *loopBlockT) []*loopBlockT { return b.next },
		func(b *loopBlockT, d *loopBlockT) {
			b.dominator = d
		})

	// Find loop headers by looking for edges whose tail dominates
	// their head.  All blocks on paths upwards from the tail to the
	// head are in the loop.
	loopHeaders := []*loopBlockT{}
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
		func(x, y *loopBlockT) int {
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

	for i, block := range blocks {
		setResult(
			theirBlocks[i],
			usToThem[block.loopHeader],
			usToThem[block.loopParent],
			block.loopDepth)
	}
	headers := make([]*T, len(loopHeaders))
	for i, header := range loopHeaders {
		headers[i] = usToThem[header]
	}
	return headers
}

// Walk up the 'previous' links from 'block' until you hit 'header',
// adding everything to 'header's loopBlocks.

func findLoopBlocks(header *loopBlockT, block *loopBlockT) {
	if block == header || header.loopBlocks.Contains(block) {
		return
	}
	header.loopBlocks.Add(block)
	for _, prev := range block.previous {
		findLoopBlocks(header, prev)
	}
}
