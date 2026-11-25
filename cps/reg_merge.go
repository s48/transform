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
	id        int     // used for making sorts deterministic
	chain     *chainT // nil if this starts from a link
	root      *linkT  // the link, if there is no chain
	leaves    []*searchLinkT
	shortest  int               // index of the leaf to extend next
	seen      util.SetT[*linkT] // every link that is or has been a leaf
	cancelled bool              // may still be in the queue
}

type searchLinkT struct {
	constant  bool // the path here has a constant's link
	link      *linkT
	parent    *searchLinkT // nil if the link is next to the chain
	depth     int          // program points in this and all its ancestors
	jump      bool         // the path here goes from an argument to an output
	loopDepth int          // minimum loop depth of this and all its ancestors
}

// True if x is shorter than y, meaning that x should be extended first.
func (x *searchLinkT) isShorter(y *searchLinkT) bool {
	if x.constant != y.constant {
		return y.constant
	}
	if x.loopDepth != y.loopDepth {
		return y.loopDepth < x.loopDepth // inner loops go first
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
	search.shortest = 0
	search.seen = util.NewSet[*linkT]()
	if search.chain == nil {
		search.addLeaf(search.root, nil, false)
	} else {
		for _, link := range search.chain.links {
			search.addLeaves(link, nil)
		}
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
		link:      link,
		parent:    parent,
		constant:  link.variable.constant() != nil,
		depth:     link.liveRange.size(),
		jump:      jump,
		loopDepth: link.loopDepth,
	}
	if parent != nil {
		leaf.constant = leaf.constant || parent.constant
		leaf.depth += parent.depth
		leaf.jump = leaf.jump || parent.jump
		leaf.loopDepth = min(leaf.loopDepth, parent.loopDepth)
	}
	Push(&search.leaves, leaf)
	Push(&link.searches, search)
	if leaf.isShorter(search.leaves[search.shortest]) {
		search.shortest = len(search.leaves) - 1
	}
}

// Remove and return the shortest leaf.
func (search *searchT) removeShortest() *searchLinkT {
	leaves := search.leaves
	leaf := leaves[search.shortest]
	last := len(leaves) - 1
	leaves[search.shortest] = leaves[last]
	search.leaves = leaves[:last]
	search.shortest = 0
	for i, other := range search.leaves {
		if other.isShorter(search.leaves[search.shortest]) {
			search.shortest = i
		}
	}
	return leaf
}

// Extends the search along the shortest leaf.  If that reaches a chain
// this returns the path and the chain.  If it reaches a use in a fixed
// register then it returns the path and nil.  Otherwise it returns nil.
func (search *searchT) extend() ([]*linkT, *chainT) {
	leaf := search.removeShortest()
	for _, end := range leaf.link.ends {
		lower := end.chain.root()
		if lower == nil {
			continue
		}
		if search.chain != nil && lower.class != search.chain.class {
			panic("link between chains with different register classes")
		}
		path := []*linkT{}
		for branch := leaf; branch != nil; branch = branch.parent {
			Push(&path, branch.link)
		}
		slices.Reverse(path)
		return path, lower
	}
	if leaf.link.fixedUse != nil {
		path := []*linkT{}
		for branch := leaf; branch != nil; branch = branch.parent {
			Push(&path, branch.link)
		}
		slices.Reverse(path)
		return path, nil
	}
	search.addLeaves(leaf.link, leaf)
	return nil, nil
}

//----------------------------------------------------------------

// Find the initial conflicts and start a search from every chain.
func (alloc *allocatorT) startMerge() {
	// The queue returns the greatest element first.
	alloc.searchQueue = util.MakePriorityQueue(func(x *searchT, y *searchT) bool {
		xLeaf := x.leaves[x.shortest]
		yLeaf := y.leaves[y.shortest]
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
			search.cancelled = true // a new one is started if needed
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

// These links are no longer available.  Any searches that are using them
// have to start over.
//
// The alternative is to not do this and instead have extend() start over if
// the path it is extending has a link that is no longer available.  That is
// simpler and, on random programs, results in different but equally good
// allocations.  The utility of doing it here should be reexamined when there
// is a more representative sample of code to test it on.
func (alloc *allocatorT) removeFromSearches(links []*linkT) {
	for _, link := range links {
		for _, search := range link.searches {
			if !search.cancelled && search.seen.Contains(link) {
				alloc.restartSearch(search)
			}
		}
		link.searches = nil
	}
}

func (alloc *allocatorT) restartSearch(search *searchT) {
	oldLeaves := search.leaves
	oldShortest := search.shortest
	search.restart()
	if len(search.leaves) == 0 {
		// The queue may still need to be able to compare it with others.
		search.leaves = oldLeaves
		search.shortest = oldShortest
		search.cancelled = true
	} else {
		alloc.searchQueue.Update(search)
	}
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
// above that are left for other paths, if there may be any.
func (alloc *allocatorT) addPath(upper *chainT, lower *chainT, path []*linkT) {
	if alloc.addLinks(upper, lower, path) != nil {
		return
	}
	for i, link := range slices.Backward(path) {
		above := upper
		if i != 0 {
			above = nil
		}
		chain := alloc.addLinks(above, lower, path[i:i+1])
		if chain == nil {
			alloc.spill(link)
			break
		}
		lower = chain
		upper = upper.root()
	}
	if upper != nil {
		alloc.startSearch(upper)
	}
}

// Spill a link and any links above it that only lead to spilled links, as
// there is no reason for those to be in registers.
func (alloc *allocatorT) spill(link *linkT) {
	link.spilled = true
	alloc.removeFromSearches([]*linkT{link})
	for _, start := range link.starts {
		if start.chain == nil && !start.spilled &&
			!slices.ContainsFunc(start.ends, func(end *linkT) bool { return !end.spilled }) {
			alloc.spill(start)
		}
	}
}

// Add the links to a chain, merged with one or both of 'upper' and 'lower',
// or with neither.  'upper' is nil if the links do not lead down from a
// chain and 'lower' is nil if they lead to a fixed register.  Returns the chain, or nil if this can't be done.
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
	if upper == nil && lower == nil {
		choices = [][]*chainT{{}}
	} else if lower == nil {
		choices = [][]*chainT{{upper}, {}}
	} else if upper == nil || upper == lower {
		choices = [][]*chainT{{lower}, {}}
	}
	class := links[len(links)-1].fixedUse
	if lower != nil {
		class = lower.class
	}
	if links[0].variable.constant() != nil {
		// Loading it again is as good as a move from a separate chain.
		choices = choices[:len(choices)-1]
	}
	for _, chains := range choices {
		if alloc.canMerge(chains, live, class) {
			chain := alloc.mergePath(chains, links, live, class)
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
// without keeping the result from being colored.  Each chain has its own
// set of allowed registers, as values that are live across calls cannot
// be in registers that the calls change.  A chain with fewer neighbors
// than allowed registers can always be colored.  A neighbor of the result
// is significant if it will have at least as many neighbors as it has
// allowed registers.  Either of two tests is sufficient:
//   - Briggs: the result has fewer significant neighbors than allowed
//     registers.
//   - George: every significant neighbor is already a neighbor of one
//     particular chain, which has the same allowed registers as the
//     result.  The result is then no harder to color than that chain was.
func (alloc *allocatorT) canMerge(
	chains []*chainT,
	live *liveRangeT,
	class *RegisterClassT,
) bool {
	if len(live.intervals) == 0 && len(chains) == 1 {
		return true // nothing changes
	}
	allowed := alloc.mergedAllowed(chains, live, class)
	if allowed == 0 {
		return false
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
		if neighbor.allowed.size() <= degree {
			Push(&significant, neighbor)
		}
	}
	if len(significant) < allowed.size() {
		return true
	}
	return slices.ContainsFunc(chains, func(chain *chainT) bool {
		return chain.allowed == allowed &&
			!slices.ContainsFunc(significant, func(neighbor *chainT) bool {
				return !chain.conflicts.Contains(neighbor)
			})
	})
}

// The registers allowed for the result of merging the chains and a path
// with the given live range.
func (alloc *allocatorT) mergedAllowed(
	chains []*chainT,
	live *liveRangeT,
	class *RegisterClassT,
) registerSetT {
	allowed := alloc.allowedRegisters(live, class)
	for _, chain := range chains {
		allowed &= chain.allowed
	}
	return allowed
}

// Merge the chains and the path into a single chain, which is returned.  If
// there are no chains then a new one is made for the path.  'live' is the
// live range of the path.
func (alloc *allocatorT) mergePath(
	chains []*chainT,
	path []*linkT,
	live *liveRangeT,
	class *RegisterClassT,
) *chainT {
	allowed := alloc.mergedAllowed(chains, live, class)
	var chain *chainT
	unadded := path
	if len(chains) == 0 {
		chain = newChain(path[0], class)
		alloc.allChains.Add(chain)
		unadded = path[1:]
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
	for _, link := range unadded {
		chain.addLink(link)
	}
	chain.allowed = allowed
	alloc.addConflicts(chain, live)
	alloc.removeFromSearches(path)
	return chain
}

//----------------------------------------------------------------
// The usual graph coloring.  The merging criteria ensure that there
// is always a chain with fewer remaining neighbors than allowed registers.

func (alloc *allocatorT) colorChains(class *RegisterClassT) {
	degrees := map[*chainT]int{}
	todo := []*chainT{}
	for _, chain := range alloc.sortedChains() {
		if chain.class == class {
			degrees[chain] = len(chain.conflicts)
			if len(chain.conflicts) < chain.allowed.size() {
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
			if degrees[neighbor] == neighbor.allowed.size()-1 {
				Push(&todo, neighbor)
			}
		}
	}
	if len(todo) != len(degrees) {
		panic("chains cannot be colored")
	}
	preferences := alloc.chainPreferences(class)
	for _, chain := range slices.Backward(todo) {
		available := chain.allowed
		for neighbor := range chain.conflicts {
			if neighbor.Register != nil {
				available = class.removeRegister(available, neighbor.Register)
			}
		}
		chain.Register = chooseRegister(chain, available, preferences)
	}
}

// For each chain, the weight of each register that it would prefer.  The
// weights for links in the same chain and register are added together.
func (alloc *allocatorT) chainPreferences(class *RegisterClassT) map[*chainT]map[RegisterT]int {
	result := map[*chainT]map[RegisterT]int{}
	for _, preference := range alloc.preferences {
		chain := preference.link.chain.root()
		_, inClass := class.registerIndex[preference.register]
		if chain == nil || chain.class != class || !inClass {
			continue
		}
		if result[chain] == nil {
			result[chain] = map[RegisterT]int{}
		}
		result[chain][preference.register] += preference.weight
	}
	return result
}

// Choose one of the available registers for the chain.  It gets the one it
// prefers most, unless some neighbor that has not yet been assigned a
// register prefers it more.  Otherwise it gets the first one that no such
// neighbor prefers, if there is one.
func chooseRegister(
	chain *chainT,
	available registerSetT,
	preferences map[*chainT]map[RegisterT]int,
) RegisterT {
	class := chain.class
	// The most any unassigned neighbor wants each register.
	wanted := map[RegisterT]int{}
	for neighbor := range chain.conflicts {
		if neighbor.Register == nil {
			for register, weight := range preferences[neighbor] {
				wanted[register] = max(wanted[register], weight)
			}
		}
	}
	var best RegisterT
	bestWeight := 0
	for register, weight := range preferences[chain] {
		index, found := class.registerIndex[register]
		if !found || (uint64(available)>>index)&1 == 0 || weight < wanted[register] {
			continue
		}
		// Ties go to the lowest-numbered register, for determinism.
		if bestWeight < weight || (weight == bestWeight && index < class.registerIndex[best]) {
			best = register
			bestWeight = weight
		}
	}
	if best != nil {
		return best
	}
	unwanted := available
	for register := range wanted {
		_, found := class.registerIndex[register]
		if found {
			unwanted = class.removeRegister(unwanted, register)
		}
	}
	if unwanted != 0 {
		return class.firstRegister(unwanted)
	}
	return class.firstRegister(available)
}
