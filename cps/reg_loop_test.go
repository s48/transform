// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package cps

import (
	"slices"
	"testing"

	"github.com/s48/transform/util"
)

func expectLoopLink(t *testing.T, link *linkT, depth int, start int, end int) {
	t.Helper()
	expectIntervals(t, &link.liveRange, intervals(start, end))
	if link.loopDepth != depth {
		t.Errorf("link has depth %d, expected %d", link.loopDepth, depth)
	}
	if link.chain != nil {
		t.Errorf("link should not be in a chain")
	}
}

// Block 1 is the header of the outer loop, {1, 2, 3, 4}, and block 2 of
// the inner one, {2, 3}.  The loops exit from their headers.  All
// variables are bound in block 0 and used in block 5, and the names say
// where else they are used.
func TestLoopLinks(t *testing.T) {
	next := [][]int{{1}, {2, 5}, {3, 4}, {2}, {1}, {}}
	vars := testVars("none outer inner")
	none, outer, inner := vars[0], vars[1], vars[2]
	blocks := makeTestBlocks(next)
	if !slices.Equal(orderBlocks(blocks[0]), blocks) {
		t.Fatalf("blocks in wrong order")
	}
	for i, block := range blocks {
		switch i {
		case 0:
			block.addTestCall(nil, EarlyRegUse, vars, LateRegUse)
		case 3:
			block.addTestCall([]*VariableT{inner}, EarlyRegUse, nil, LateRegUse)
		case 4:
			block.addTestCall([]*VariableT{outer}, EarlyRegUse, nil, LateRegUse)
		case 5:
			block.addTestCall(vars, EarlyRegUse, nil, LateRegUse)
		default:
			block.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
		}
	}
	index := 0
	for _, block := range blocks {
		block.startIndex = index
		index += 2
		block.endIndex = index
	}
	setTestRegisters(8)
	alloc := &allocatorT{
		allVars:          util.NewSet[*VariableT](),
		allChains:        util.NewSet[*chainT](),
		numProgramPoints: index,
	}
	alloc.makeLinks(blocks)
	checkLinks(t, alloc)

	depths := []int{}
	for _, block := range blocks {
		depths = append(depths, block.loop.depth())
	}
	if !slices.Equal(depths, []int{0, 1, 2, 2, 1, 0}) {
		t.Fatalf("wrong loop depths %v", depths)
	}
	outerLoop := blocks[1].loop
	innerLoop := blocks[2].loop
	if blocks[3].loop != innerLoop || innerLoop.parent != outerLoop || outerLoop.parent != nil {
		t.Fatalf("wrong loops")
	}

	// Not referenced in either, so there is one link for both.
	link := outerLoop.links[none]
	if len(outerLoop.links) != 1 || link == nil {
		t.Fatalf("wrong links in outer loop")
	}
	expectLoopLink(t, link, 0, 2, 10)
	if len(link.starts) != 1 || link.starts[0] != blocks[0].endLinks[none] ||
		len(link.ends) != 1 || link.ends[0] != blocks[5].liveLinks[none].link {
		t.Errorf("outer loop's link is not connected correctly")
	}

	// Not referenced in just the inner loop.  The link belongs to the
	// outer one.
	link = innerLoop.links[outer]
	if len(innerLoop.links) != 1 || link == nil {
		t.Fatalf("wrong links in inner loop")
	}
	expectLoopLink(t, link, 1, 4, 8)
	if len(link.starts) != 1 || link.starts[0] != blocks[1].endLinks[outer] ||
		len(link.ends) != 1 || link.ends[0] != blocks[4].liveLinks[outer].link {
		t.Errorf("inner loop's link is not connected correctly")
	}

	// Referenced in both loops, so it has links in every block.
	for i, depth := range depths[:5] {
		link := blocks[i].endLinks[inner]
		if link == nil || link.loopDepth != depth {
			t.Fatalf("wrong end link in block %d", i)
		}
		ends := []*linkT{}
		for _, j := range next[i] {
			Push(&ends, blocks[j].liveLinks[inner].link)
		}
		if !slices.Equal(link.ends, ends) {
			t.Errorf("end link in block %d has the wrong ends", i)
		}
	}
	starts := blocks[2].liveLinks[inner].link.starts
	if !slices.Equal(starts, []*linkT{blocks[1].endLinks[inner], blocks[3].endLinks[inner]}) {
		t.Errorf("inner header's link has the wrong starts")
	}

	alloc.mergeChains()
	alloc.colorChains(testClass)
	checkAllocation(t, alloc)
	if len(alloc.allChains) != 3 {
		t.Errorf("got %d chains, expected 3", len(alloc.allChains))
	}
}
