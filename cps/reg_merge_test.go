// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package cps

import (
	"fmt"
	"math/rand"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/s48/transform/util"
)

type testRegisterT struct {
	class  *RegisterClassT
	number int
}

func (reg *testRegisterT) SetClass(class *RegisterClassT) { reg.class = class }
func (reg *testRegisterT) Class() *RegisterClassT         { return reg.class }
func (reg *testRegisterT) String() string                 { return "r" + strconv.Itoa(reg.number) }
func (reg *testRegisterT) Number() int                    { return reg.number }

func setTestRegisters(count int) {
	regs := []RegisterT{}
	for i := range count {
		regs = append(regs, &testRegisterT{number: i})
	}
	testClass.SetRegisters(regs, uint64(1)<<count-1)
}

// The blocks must be in reverse postorder.
func allocateTestBlocks(blocks []*regBlockT) *allocatorT {
	alloc := &allocatorT{
		allVars:   util.NewSet[*VariableT](),
		allChains: util.NewSet[*chainT](),
	}
	index := 0
	for _, block := range blocks {
		block.startIndex = index
		index += block.callCount * 2
		block.endIndex = index
	}
	alloc.numProgramPoints = index
	for _, block := range slices.Backward(blocks) {
		alloc.findLiveRanges(block.start)
	}
	for _, block := range blocks {
		block.connectJump()
	}
	alloc.mergeChains()
	alloc.colorChains(testClass)
	return alloc
}

func makeTestBlocks(next [][]int) []*regBlockT {
	blocks := []*regBlockT{}
	for range next {
		blocks = append(blocks, makeRegBlock())
	}
	for i, nexts := range next {
		for _, j := range nexts {
			blocks[i].addNext(blocks[j])
		}
	}
	return blocks
}

// Checks the results against the live ranges of the links.
func checkAllocation(t *testing.T, alloc *allocatorT) {
	t.Helper()
	chains := alloc.sortedChains()
	for _, chain := range chains {
		if chain.peer != nil || chain.Register == nil {
			t.Fatalf("chain %d is merged or has no register", chain.id)
		}
		points := map[int]bool{}
		for _, link := range chain.links {
			if link.chain.root() != chain {
				t.Fatalf("link %d has the wrong chain", link.id)
			}
			for _, interval := range link.liveRange.intervals {
				for i := interval.start; i < interval.end; i++ {
					if points[i] {
						t.Fatalf("chain %d has overlapping links", chain.id)
					}
					points[i] = true
				}
			}
		}
		if len(points) != chain.liveRange.size() {
			t.Fatalf("chain %d has the wrong live range", chain.id)
		}
		for i, set := range alloc.chainPoints {
			if set.Contains(chain) != points[i] {
				t.Fatalf("chainPoints is wrong for chain %d at point %d", chain.id, i)
			}
		}
	}
	for i, x := range chains {
		for _, y := range chains[:i] {
			overlap := x.liveRange.conflicts(y.liveRange)
			if x.conflicts.Contains(y) != overlap || y.conflicts.Contains(x) != overlap {
				t.Fatalf("conflicts are wrong for chains %d and %d", x.id, y.id)
			}
			if overlap && x.Register == y.Register {
				t.Fatalf("chains %d and %d overlap and share a register", x.id, y.id)
			}
		}
	}
}

func testVars(names string) []*VariableT {
	result := []*VariableT{}
	for i, name := range strings.Fields(names) {
		result = append(result, &VariableT{Name: name, Id: i})
	}
	return result
}

// With plenty of registers every variable should end up in one chain.
func TestMergeBranches(t *testing.T) {
	tests := []struct {
		name string
		next [][]int
		uses []int
	}{
		{"line", [][]int{{1}, {2}, {}}, []int{0, 1, 2}},
		{"diamond", [][]int{{1, 2}, {3}, {3}, {}}, []int{3}},
		{"two diamonds", [][]int{{1, 2}, {3}, {3}, {4, 5}, {6}, {6}, {}}, []int{6}},
		{"use on one side", [][]int{{1, 2}, {3}, {3}, {}}, []int{1, 3}},
		{"different uses", [][]int{{1, 2}, {}, {}}, []int{1, 2}},
		{"crossed", [][]int{{1, 2}, {3, 4}, {3, 4}, {}, {}}, []int{3, 4}},
	}
	setTestRegisters(8)
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			vars := testVars("x y")
			blocks := makeTestBlocks(test.next)
			for i, block := range blocks {
				if i == 0 {
					block.addTestCall(nil, EarlyRegUse, vars, LateRegUse)
				} else {
					block.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
				}
				if slices.Contains(test.uses, i) {
					block.addTestCall(vars, EarlyRegUse, nil, LateRegUse)
				}
			}
			alloc := allocateTestBlocks(blocks)
			checkAllocation(t, alloc)
			if len(alloc.allChains) != 2 {
				t.Errorf("got %d chains, expected 2", len(alloc.allChains))
			}
			if len(alloc.findMoves()) != 0 {
				t.Errorf("unexpected moves")
			}
		})
	}
}

// The number of paths is exponential in the number of diamonds.
func TestMergeManyDiamonds(t *testing.T) {
	setTestRegisters(8)
	next := [][]int{}
	for i := range 40 {
		next = append(next, []int{3*i + 1, 3*i + 2}, []int{3*i + 3}, []int{3*i + 3})
	}
	next = append(next, []int{})
	vars := testVars("a b c d")
	blocks := makeTestBlocks(next)
	for i, block := range blocks {
		if i == 0 {
			block.addTestCall(nil, EarlyRegUse, vars, LateRegUse)
		} else {
			block.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
		}
	}
	blocks[len(blocks)-1].addTestCall(vars, EarlyRegUse, nil, LateRegUse)
	alloc := allocateTestBlocks(blocks)
	checkAllocation(t, alloc)
	if len(alloc.allChains) != len(vars) {
		t.Errorf("got %d chains, expected %d", len(alloc.allChains), len(vars))
	}
}

// A jump argument that is not used again is merged with the output,
// while one that is live after the jump cannot be.
func TestMergeJump(t *testing.T) {
	setTestRegisters(8)
	vars := testVars("a b p q")
	a, b, p, q := vars[0], vars[1], vars[2], vars[3]
	entry := makeRegBlock()
	entry.addTestCall(nil, EarlyRegUse, []*VariableT{a, b}, LateRegUse)
	entry.addTestCall([]*VariableT{a, b}, EarlyRegUse, nil, LateRegUse)
	target := makeRegBlock()
	target.addTestCall(nil, EarlyRegUse, []*VariableT{p, q}, LateRegUse)
	target.addTestCall([]*VariableT{p, q, b}, EarlyRegUse, nil, LateRegUse)
	entry.makeTestJump(target)
	alloc := allocateTestBlocks([]*regBlockT{entry, target})
	checkAllocation(t, alloc)
	if a.Register() != p.Register() {
		t.Errorf("a and p are in different registers")
	}
	if b.Register() == q.Register() {
		t.Errorf("b and q are in the same register")
	}
	if len(alloc.findMoves()) != 0 {
		t.Errorf("unexpected moves")
	}
}

// Random loop-free programs.  Blocks can only go to later blocks.
func randomTestBlocks(random *rand.Rand, maxLive int) []*regBlockT {
	count := 1 + random.Intn(8)
	next := make([][]int, count)
	jumpTarget := make([]bool, count) // all predecessors have just one next
	for i := range count {
		if i < count-1 {
			next[i] = []int{i + 1} // makes everything reachable
			other := i + 1 + random.Intn(count-i-1)
			if other != i+1 && random.Intn(2) == 0 {
				next[i] = append(next[i], other)
			}
		}
		jumpTarget[i] = 0 < i && random.Intn(2) == 0
	}
	for _, nexts := range next {
		if len(nexts) != 1 {
			for _, j := range nexts {
				jumpTarget[j] = false
			}
		}
	}

	blocks := make([]*regBlockT, count)
	available := make([]util.SetT[*VariableT], count) // at the block's end
	previous := make([][]int, count)
	nextId := 0
	newVars := func(n int) []*VariableT {
		vars := []*VariableT{}
		for range n {
			vars = append(vars, &VariableT{Name: "v", Id: nextId})
			nextId += 1
		}
		return vars
	}
	parameters := make([][]*VariableT, count)
	for i := range count {
		block := makeRegBlock()
		blocks[i] = block
		for _, j := range next[i] {
			previous[j] = append(previous[j], i)
		}
		vars := util.NewSet[*VariableT]()
		for k, j := range previous[i] {
			if k == 0 {
				vars = available[j].Union(vars)
			} else {
				vars = vars.Intersection(available[j])
			}
		}
		if jumpTarget[i] {
			parameters[i] = newVars(1 + random.Intn(2))
		}
		block.addTestCall(nil, EarlyRegUse, parameters[i], LateRegUse)
		vars.Add(parameters[i]...)
		pick := func(n int) []*VariableT {
			members := vars.Members()
			slices.SortFunc(members, func(x, y *VariableT) int { return x.Id - y.Id })
			result := []*VariableT{}
			for range n {
				if 0 < len(members) {
					// Often the same one twice.
					result = append(result, members[random.Intn(len(members))])
				}
			}
			return result
		}
		for range random.Intn(4) {
			outputs := newVars(random.Intn(2))
			if maxLive <= len(vars) {
				outputs = nil
			}
			block.addTestCall(pick(random.Intn(3)), -random.Intn(2), outputs, -random.Intn(2))
			vars.Add(outputs...)
		}
		if len(next[i]) == 1 && jumpTarget[next[i][0]] {
			// Filled in below, when the target's parameters are known.
			available[i] = vars
			continue
		}
		block.addTestCall(pick(2), EarlyRegUse, nil, LateRegUse)
		available[i] = vars
	}
	for i, block := range blocks {
		if len(next[i]) == 1 && jumpTarget[next[i][0]] {
			j := next[i][0]
			members := available[i].Members()
			slices.SortFunc(members, func(x, y *VariableT) int { return x.Id - y.Id })
			arguments := []*VariableT{}
			for range parameters[j] {
				if 0 < len(members) {
					arguments = append(arguments, members[random.Intn(len(members))])
				}
			}
			block.addTestCall(arguments, EarlyRegUse, nil, LateRegUse)
			if len(arguments) == len(parameters[j]) {
				block.makeTestJump(blocks[j])
				continue
			}
		}
		for _, j := range next[i] {
			block.addNext(blocks[j])
		}
	}
	return blocks
}

// Allocating the same program twice gives identical links and registers.
func TestMergeDeterministic(t *testing.T) {
	describe := func(seed int) string {
		setTestRegisters(5 + seed%4)
		blocks := randomTestBlocks(rand.New(rand.NewSource(int64(seed))), 5)
		firstLink := nextLinkIdx
		result := ""
		alloc := (*allocatorT)(nil)
		func() {
			defer func() {
				problem := recover()
				if problem != nil {
					result = fmt.Sprint(problem)
				}
			}()
			alloc = allocateTestBlocks(blocks)
		}()
		if alloc == nil {
			return result
		}
		for _, chain := range alloc.sortedChains() {
			result += fmt.Sprintf("%s:", chain.Register)
			for _, link := range chain.links {
				result += fmt.Sprintf(" %d%v", link.id-firstLink, link.liveRange.intervals)
			}
			result += "\n"
		}
		return result
	}
	for seed := range 300 {
		first := describe(seed)
		for range 5 {
			again := describe(seed)
			if again != first {
				t.Fatalf("seed %d: got\n%sand then\n%s", seed, first, again)
			}
		}
	}
}

func TestMergeRandom(t *testing.T) {
	results := map[string]int{}
	for seed := range 4000 {
		registers := 3 + seed%6
		setTestRegisters(registers)
		random := rand.New(rand.NewSource(int64(seed)))
		blocks := randomTestBlocks(random, registers)
		var problem any
		var alloc *allocatorT
		func() {
			defer func() { problem = recover() }()
			alloc = allocateTestBlocks(blocks)
		}()
		if problem != nil {
			message := fmt.Sprint(problem)
			if strings.Contains(message, "spilling") {
				results[fmt.Sprintf("%d spill", registers)] += 1
				continue
			}
			t.Fatalf("seed %d: %s", seed, message)
		}
		checkAllocation(t, alloc)
		if len(alloc.findMoves()) == 0 {
			results[fmt.Sprintf("%d no moves", registers)] += 1
		} else {
			results[fmt.Sprintf("%d moves", registers)] += 1
		}
	}
	t.Logf("%v", results)
}

// No search may be left running for a chain that has been merged into
// another, and no chain may have more than one.
func TestMergeCancelsSearches(t *testing.T) {
	setTestRegisters(8)
	// Two uses, so that the merged lower chain has a search of its own.
	vars := testVars("x")
	block := makeRegBlock()
	block.addTestCall(nil, EarlyRegUse, vars, LateRegUse)
	block.addTestCall(vars, EarlyRegUse, nil, LateRegUse)
	firstUse := block.end.Inputs[0]
	block.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	block.addTestCall(vars, EarlyRegUse, nil, LateRegUse)
	alloc := &allocatorT{
		allVars:          util.NewSet[*VariableT](),
		allChains:        util.NewSet[*chainT](),
		numProgramPoints: block.endIndex,
	}
	alloc.findLiveRanges(block.start)
	alloc.startMerge()
	upper := vars[0].definition.chain
	lower := vars[0].uses[firstUse].chain
	upperSearch := upper.search
	lowerSearch := lower.search
	if upperSearch == nil || lowerSearch == nil {
		t.Fatalf("searches not started")
	}
	// The two calls are adjacent, so this is the shortest.
	if alloc.searchQueue.Dequeue() != upperSearch {
		t.Fatalf("wrong search is first")
	}
	path, found := upperSearch.extend()
	if found != lower {
		t.Fatalf("search found the wrong chain")
	}
	alloc.addPath(upper, lower, path)
	if lower.root() != upper {
		t.Fatalf("chains were not merged")
	}
	if !upperSearch.cancelled || !lowerSearch.cancelled {
		t.Errorf("old searches were not cancelled")
	}
	if upper.search == nil || upper.search.cancelled || lower.search != nil {
		t.Errorf("merged chain should have the only search")
	}
}
