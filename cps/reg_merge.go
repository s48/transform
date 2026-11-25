// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Merging and coloring chains.  See the description at the top of
// reg_alloc.go.

package cps

import (
	"maps"
	"slices"

	"github.com/s48/transform/util"
)

// A shortest-first search down from a chain, along links that are not yet
// in chains, for a path to any other chain.  The path may also lead back
// to the same chain, such as along the second side of a conditional after
// the first was added.  Each chain with such links below it has a search.
// Every link has some chain above it, so this reaches all of them.
//
// Constants come after everything else, as they never need to be spilled.
// Links inside loops come before those outside, so that inner loops are
// done before outer ones.  Within a loop, paths that go through a jump from
// an argument to an output come after those that stay within one variable.
// Otherwise an argument that is live after the jump may be merged with the
// output, which keeps it from being merged with the rest of its own
// variable.

type searchT struct {
	id        int
	chain     *chainT // nil if this starts from a link
	root      *linkT  // the link, if there is no chain
	leaves    []*searchLinkT
	seen      util.SetT[*linkT] // every link that is or has been a leaf
	cancelled bool              // may still be in the queue
}

type searchLinkT struct {
	constant bool // the path here has a constant's link
	link     *linkT
	parent   *searchLinkT // nil if the link is next to the chain
	depth    int          // program points in this and all its parents
	jump     bool         // the path here goes from an argument to an output
	loop     int          // minimum loop depth of this and all its parents
}

func (x *searchLinkT) isShorter(y *searchLinkT) bool {
	if x.constant != y.constant {
		return y.constant
	}
	if x.loop != y.loop {
		return y.loop < x.loop // inner loops go first
	}
	if x.jump != y.jump {
		return y.jump
	}
	return x.depth < y.depth
}

var nextSearchIdx = -1

func nextSearchId() int {
	nextSearchIdx += 1
	return nextSearchIdx
}

// Start over, with only the links directly below the chain.
func (search *searchT) restart() {
	search.leaves = nil
	search.seen = util.NewSet[*linkT]()
	if search.chain == nil {
		search.addLeaf(search.root, nil, false)
		return
	}
	for _, link := range search.chain.links {
		search.addLeaves(link, nil)
	}
}

// Add the links that 'from' leads to.
func (search *searchT) addLeaves(from *linkT, parent *searchLinkT) {
	for _, link := range from.ends {
		search.addLeaf(link, parent, from.variable != link.variable)
	}
}

func (search *searchT) addLeaf(link *linkT, parent *searchLinkT, jump bool) {
	if link.chain != nil || link.spilled || search.seen.Contains(link) {
		return
	}
	search.seen.Add(link)
	leaf := &searchLinkT{
		link:     link,
		parent:   parent,
		constant: link.variable.constant() != nil,
		depth:    link.liveRange.size(),
		jump:     jump,
		loop:     link.loopDepth,
	}
	if parent != nil {
		leaf.constant = leaf.constant || parent.constant
		leaf.depth += parent.depth
		leaf.jump = leaf.jump || parent.jump
		leaf.loop = min(leaf.loop, parent.loop)
	}
	Push(&search.leaves, leaf)
}

// The index of the leaf to extend next.
func (search *searchT) shortestLeaf() int {
	best := 0
	for i, leaf := range search.leaves {
		if leaf.isShorter(search.leaves[best]) {
			best = i
		}
	}
	return best
}

// Extends the search along the shortest leaf.  If that reaches a chain
// this returns the path and the chain, otherwise it returns nil.
func (search *searchT) extend() ([]*linkT, *chainT) {
	i := search.shortestLeaf()
	leaf := search.leaves[i]
	search.leaves = slices.Delete(search.leaves, i, i+1)
	path := []*linkT{}
	for branch := leaf; branch != nil; branch = branch.parent {
		if branch.link.chain != nil || branch.link.spilled {
			// Some other search has been using our links.
			search.restart()
			return nil, nil
		}
		Push(&path, branch.link)
	}
	for _, end := range leaf.link.ends {
		lower := end.chain.root()
		if lower != nil && (search.chain == nil || lower.class == search.chain.class) {
			slices.Reverse(path)
			return path, lower
		}
	}
	search.addLeaves(leaf.link, leaf)
	return nil, nil
}

//----------------------------------------------------------------

// Find the initial conflicts and start a search from every chain.
func (alloc *allocatorT) startMerge() {
	// The queue returns the greatest element first.
	alloc.searchQueue = util.MakePriorityQueue(func(x *searchT, y *searchT) bool {
		xLeaf := x.leaves[x.shortestLeaf()]
		yLeaf := y.leaves[y.shortestLeaf()]
		if xLeaf.isShorter(yLeaf) {
			return false
		} else if yLeaf.isShorter(xLeaf) {
			return true
		}
		return y.id < x.id
	})
	alloc.chainPoints = make([]util.SetT[*chainT], alloc.numProgramPoints)
	for i := range alloc.chainPoints {
		alloc.chainPoints[i] = util.NewSet[*chainT]()
	}
	chains := alloc.sortedChains()
	for _, chain := range chains {
		alloc.addConflicts(chain, chain.liveRange)
	}
	for _, chain := range chains {
		alloc.startSearch(chain)
	}
	for _, link := range alloc.rootLinks {
		alloc.startRootSearch(link)
	}
}

func (alloc *allocatorT) mergeChains() {
	alloc.startMerge()
	for !alloc.searchQueue.Empty() {
		search := alloc.searchQueue.Dequeue()
		if search.cancelled {
			continue
		}
		path, lower := search.extend()
		if path != nil {
			alloc.addPath(search.chain, lower, path)
			if search.chain == nil {
				// Does nothing if the link is now in a chain.
				alloc.startRootSearch(search.root)
			}
		} else if len(search.leaves) != 0 {
			alloc.searchQueue.Enqueue(search)
		}
	}
}

func (alloc *allocatorT) sortedChains() []*chainT {
	return sortChains(alloc.allChains)
}

func sortChains(chains util.SetT[*chainT]) []*chainT {
	return slices.SortedFunc(maps.Keys(chains),
		func(x, y *chainT) int { return x.id - y.id })
}

// Update the conflicts for having added 'live' to the chain.
func (alloc *allocatorT) addConflicts(chain *chainT, live *liveRangeT) {
	for other := range alloc.liveChains(live, chain.class) {
		if other != chain {
			other.conflicts.Add(chain)
			chain.conflicts.Add(other)
		}
	}
	alloc.addToPoints(chain, live)
}

func (alloc *allocatorT) addToPoints(chain *chainT, live *liveRangeT) {
	for _, interval := range live.intervals {
		for i := interval.start; i < interval.end; i++ {
			alloc.chainPoints[i].Add(chain)
		}
	}
}

// All chains of the given class that are live anywhere in 'live'.
func (alloc *allocatorT) liveChains(live *liveRangeT, class *RegisterClassT) util.SetT[*chainT] {
	result := util.NewSet[*chainT]()
	for _, interval := range live.intervals {
		for i := interval.start; i < interval.end; i++ {
			for chain := range alloc.chainPoints[i] {
				if chain.class == class {
					result.Add(chain)
				}
			}
		}
	}
	return result
}

// Start or restart the search down from a chain.
func (alloc *allocatorT) startSearch(chain *chainT) {
	chain.cancelSearch()
	search := &searchT{id: nextSearchId(), chain: chain}
	search.restart()
	if len(search.leaves) != 0 {
		chain.search = search
		alloc.searchQueue.Enqueue(search)
	}
}

// Start a search down from, and including, a link.
func (alloc *allocatorT) startRootSearch(link *linkT) {
	search := &searchT{id: nextSearchId(), root: link}
	search.restart()
	if len(search.leaves) != 0 {
		alloc.searchQueue.Enqueue(search)
	}
}

func (chain *chainT) cancelSearch() {
	if chain.search != nil {
		chain.search.cancelled = true
		chain.search = nil
	}
}

// Add the path to a chain.  We merge it with as many of the chains it
// connects as possible.  If it cannot be added as a whole we go up from
// the lower chain, adding links individually, at the cost of some moves.
// If we get to one that can't be added then it is spilled.  Any links
// above that are left for other paths.  If there aren't any then there is
// no reason for them to be in registers.
func (alloc *allocatorT) addPath(upper *chainT, lower *chainT, path []*linkT) {
	if alloc.addLinks(upper, lower, path) != nil {
		return
	}
	for i, link := range slices.Backward(path) {
		above := upper
		if i != 0 {
			above = nil
		}
		lower = alloc.addLinks(above, lower, path[i:i+1])
		if lower == nil {
			link.spilled = true
			break
		}
		upper = upper.root()
	}
	if upper != nil {
		alloc.startSearch(upper)
	}
}

// Add the links to a chain, merged with one or both of 'upper' and 'lower',
// or with neither.  'upper' is nil if the links do not lead down from a
// chain.  Returns the chain, or nil if this can't be done.
func (alloc *allocatorT) addLinks(upper *chainT, lower *chainT, links []*linkT) *chainT {
	live := &liveRangeT{}
	for _, link := range links {
		if live.conflicts(&link.liveRange) {
			// The path goes around a loop, with a different variable each time.
			return nil
		}
		live = live.union(&link.liveRange)
	}
	choices := [][]*chainT{{upper, lower}, {upper}, {lower}, {}}
	if upper == nil || upper == lower {
		choices = [][]*chainT{{lower}, {}}
	}
	if links[0].variable.constant() != nil {
		// Loading it again is as good as a move from a separate chain.
		choices = choices[:len(choices)-1]
	}
	for _, chains := range choices {
		if alloc.canMerge(chains, live, lower.class) {
			chain := alloc.mergePath(chains, links, live, lower.class)
			// The links below these may have changed.  The lower chain is
			// unchanged if it was not merged.
			alloc.startSearch(chain)
			if upper != nil && chain != upper.root() {
				alloc.startSearch(upper.root())
			}
			return chain
		}
	}
	return nil
}

// True if the chains, and a path with the given live range, can be merged
// without keeping the result from being colored.  A neighbor of the
// result is significant if it will have N or more neighbors itself.  Either
// of two tests is sufficient:
//   - Briggs: there are fewer than N significant neighbors.
//   - George: every significant neighbor is already a neighbor of one
//     particular chain.  The result is then no harder to color than that
//     chain was.
func (alloc *allocatorT) canMerge(
	chains []*chainT,
	live *liveRangeT,
	class *RegisterClassT,
) bool {
	if len(live.intervals) == 0 && len(chains) == 1 {
		return true // nothing changes
	}
	for i, chain := range chains {
		if chain.liveRange.conflicts(live) {
			return false
		}
		for _, other := range chains[:i] {
			if chain.conflicts.Contains(other) {
				return false
			}
		}
	}
	neighbors := alloc.liveChains(live, class)
	for _, chain := range chains {
		neighbors.AddSet(chain.conflicts)
	}
	significant := []*chainT{}
	for neighbor := range neighbors {
		degree := len(neighbor.conflicts) + 1
		for _, chain := range chains {
			if neighbor.conflicts.Contains(chain) {
				degree -= 1
			}
		}
		if class.numRegisters() <= degree {
			Push(&significant, neighbor)
		}
	}
	if len(significant) < class.numRegisters() {
		return true
	}
	return slices.ContainsFunc(chains, func(chain *chainT) bool {
		return !slices.ContainsFunc(significant, func(neighbor *chainT) bool {
			return !chain.conflicts.Contains(neighbor)
		})
	})
}

func (alloc *allocatorT) mergePath(
	chains []*chainT,
	path []*linkT,
	live *liveRangeT,
	class *RegisterClassT,
) *chainT {
	var chain *chainT
	if len(chains) == 0 {
		chain = newChain(path[0], class)
		alloc.allChains.Add(chain)
		path = path[1:]
	} else {
		chain = chains[0]
	}
	for _, other := range chains[min(1, len(chains)):] {
		for _, interval := range other.liveRange.intervals {
			for i := interval.start; i < interval.end; i++ {
				alloc.chainPoints[i].Remove(other)
				alloc.chainPoints[i].Add(chain)
			}
		}
		other.cancelSearch()
		chain.merge(other)
		alloc.allChains.Remove(other)
	}
	for _, link := range path {
		chain.addLink(link)
	}
	alloc.addConflicts(chain, live)
	return chain
}

//----------------------------------------------------------------
// The usual graph coloring.  The merging criteria ensure that there
// is always a chain with too few remaining neighbors to matter.

func (alloc *allocatorT) colorChains(class *RegisterClassT) {
	degrees := map[*chainT]int{}
	todo := []*chainT{}
	for _, chain := range alloc.sortedChains() {
		if chain.class == class {
			degrees[chain] = len(chain.conflicts)
			if len(chain.conflicts) < class.numRegisters() {
				Push(&todo, chain)
			}
		}
	}
	for i := 0; i < len(todo); i++ {
		// Sort the chains to get deterministic behavior.
		for _, neighbor := range sortChains(todo[i].conflicts) {
			// This also decrements the degrees of removed chains, which
			// does no harm as they are already below the limit.
			degrees[neighbor] -= 1
			if degrees[neighbor] == class.numRegisters()-1 {
				Push(&todo, neighbor)
			}
		}
	}
	if len(todo) != len(degrees) {
		panic("chains cannot be colored")
	}
	for _, chain := range slices.Backward(todo) {
		available := class.newRegisterSet()
		for neighbor := range chain.conflicts {
			if neighbor.Register != nil {
				available = class.removeRegister(available, neighbor.Register)
			}
		}
		chain.Register = class.firstRegister(available)
	}
}
