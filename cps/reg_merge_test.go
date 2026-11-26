// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package cps

import (
	"fmt"
	"maps"
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
func newTestAllocator(blocks []*regBlockT) *allocatorT {
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
	return alloc
}

func allocateTestBlocks(blocks []*regBlockT) *allocatorT {
	alloc := newTestAllocator(blocks)
	alloc.makeLinks(blocks)
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
		for point, registers := range alloc.clobbers {
			if points[point] && slices.Contains(registers, chain.Register) {
				t.Fatalf("chain %d is live across a call that changes %s", chain.id, chain.Register)
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
			moves, _ := alloc.findMoves(blocks)
			if len(moves) != 0 {
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
	if blockRegister(entry, a) != blockRegister(target, p) {
		t.Errorf("a and p are in different registers")
	}
	if blockRegister(entry, b) == blockRegister(target, q) {
		t.Errorf("b and q are in the same register")
	}
	// The other is copied.
	moves, _ := alloc.findMoves([]*regBlockT{entry, target})
	if len(moves) != 1 || len(moves[entry.end].Before) != 0 || len(moves[entry.end].At) != 1 {
		t.Errorf("wrong moves")
	}
}

// The register of the link at the end of a block or for an output at the start.
func blockRegister(block *regBlockT, vart *VariableT) RegisterT {
	link := block.endLinks[vart]
	if link == nil {
		link = block.liveLinks[vart].link
	}
	return link.chain.root().Register
}

// Make a random block go back to an earlier one, which must dominate it.
func addTestLoop(random *rand.Rand, next [][]int) {
	if len(next) < 4 {
		return
	}
	latch := 2 + random.Intn(len(next)-3)
	header := 1 + random.Intn(latch-1)
	if next[latch][0] <= latch || next[latch-1][0] < latch {
		return // already in use
	}
	oldLatch := next[latch]
	oldPrevious := next[latch-1]
	next[latch-1] = []int{latch, latch + 1}
	next[latch] = []int{header}
	if !isTestReducible(next) {
		next[latch] = oldLatch
		next[latch-1] = oldPrevious
	}
}

// True if everything is reachable and back edges go to dominators.
func isTestReducible(next [][]int) bool {
	reachable := func(without int) []bool {
		seen := make([]bool, len(next))
		var visit func(i int)
		visit = func(i int) {
			if i != without && !seen[i] {
				seen[i] = true
				for _, j := range next[i] {
					visit(j)
				}
			}
		}
		visit(0)
		return seen
	}
	if slices.Contains(reachable(-1), false) {
		return false
	}
	for i, nexts := range next {
		for _, j := range nexts {
			if j <= i && reachable(j)[i] {
				return false
			}
		}
	}
	return true
}

// A block with a single next block jumps to it.  Add blocks as needed
// so that the next blocks of conditionals have no other predecessors.
// The result is in reverse postorder.
func addTestJumps(next [][]int) [][]int {
	previous := make([]int, len(next))
	for _, nexts := range next {
		for _, j := range nexts {
			previous[j] += 1
		}
	}
	for i, nexts := range slices.Clone(next) {
		if 1 < len(nexts) {
			next[i] = slices.Clone(nexts)
			for k, j := range nexts {
				if previous[j] != 1 {
					next[i][k] = len(next)
					next = append(next, []int{j})
				}
			}
		}
	}
	blocks := makeTestBlocks(next)
	ordered := orderBlocks(blocks[0])
	result := [][]int{}
	for _, block := range ordered {
		nexts := []int{}
		for _, other := range block.next {
			nexts = append(nexts, slices.Index(ordered, other))
		}
		result = append(result, nexts)
	}
	return result
}

// A call that changes the fixed registers and the even-numbered ones.
type testCallPrimopT struct {
	PrimopT
}

func (primop testCallPrimopT) Name() string { return "call" }

func (primop testCallPrimopT) ClobberedRegisters(call *CallNodeT) []RegisterT {
	result := slices.Clone(testFixedRegisters)
	for i, register := range testClass.registers {
		if i%2 == 0 && !slices.Contains(result, register) {
			Push(&result, register)
		}
	}
	return result
}

// Registers that the allocator does not assign.
var unallocatedTestRegisters = []RegisterT{
	&testRegisterT{number: 100}, &testRegisterT{number: 101}, &testRegisterT{number: 102},
}

// The registers used as fixed registers in tests.  These are either ones
// the allocator does not assign or, as on most machines, ones it does.
var testFixedRegisters = unallocatedTestRegisters

func useAllocatedFixed(allocated bool) {
	testFixedRegisters = unallocatedTestRegisters
	if allocated {
		testFixedRegisters = testClass.registers[len(testClass.registers)-3:]
	}
}

func setTestFixed(specs []*RegUseSpecT) {
	for i, spec := range specs {
		specs[i] = &RegUseSpecT{PhaseOffset: spec.PhaseOffset, Class: spec.Class, Fixed: testFixedRegisters[i]}
	}
}

// Without 'loops' blocks can only go to later blocks.
func randomTestBlocks(random *rand.Rand, size int, maxLive int, loops bool) []*regBlockT {
	count := 1 + random.Intn(size)
	next := make([][]int, count)
	for i := range count {
		if i < count-1 {
			next[i] = []int{i + 1} // makes everything reachable
			other := i + 1 + random.Intn(count-i-1)
			if other != i+1 && random.Intn(2) == 0 {
				next[i] = append(next[i], other)
			}
		}
	}
	if loops {
		for range 1 + random.Intn(3) {
			addTestLoop(random, next)
		}
	}
	next = addTestJumps(next)
	count = len(next)
	jumpTarget := make([]bool, count)
	for _, nexts := range next {
		if len(nexts) == 1 {
			jumpTarget[nexts[0]] = true
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
			parameters[i] = newVars(random.Intn(3))
		} else if i == 0 {
			parameters[i] = newVars(2)
		}
		block.addTestCall(nil, EarlyRegUse, parameters[i], LateRegUse)
		if i == 0 && random.Intn(2) == 0 {
			// Procedure parameters.
			setTestFixed(block.outputSpecs[0])
		}
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
			if len(outputs) == 1 && random.Intn(3) == 0 {
				block.addTestConstant(outputs[0])
				vars.Add(outputs...)
				continue
			}
			block.addTestCall(pick(random.Intn(3)), -random.Intn(2), outputs, -random.Intn(2))
			if random.Intn(4) == 0 {
				// A procedure call.
				setTestFixed(block.inputSpecs[block.callCount-1])
				setTestFixed(block.outputSpecs[block.callCount-1])
				block.end.Primop = testCallPrimopT{}
			}
			vars.Add(outputs...)
		}
		if len(next[i]) == 1 {
			// Filled in below, when the target's parameters are known.
			available[i] = vars
			continue
		}
		block.addTestCall(pick(2), EarlyRegUse, nil, LateRegUse)
		available[i] = vars
	}
	for i, block := range blocks {
		if len(next[i]) == 1 {
			j := next[i][0]
			members := available[i].Members()
			slices.SortFunc(members, func(x, y *VariableT) int { return x.Id - y.Id })
			arguments := []*VariableT{}
			for range parameters[j] {
				arguments = append(arguments, members[random.Intn(len(members))])
			}
			block.addTestCall(arguments, EarlyRegUse, nil, LateRegUse)
			block.makeTestJump(blocks[j])
			continue
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
		blocks := randomTestBlocks(rand.New(rand.NewSource(int64(seed))), 10, 5, seed%2 == 0)
		firstLink := nextLinkIdx
		result := ""
		alloc := allocateTestBlocks(blocks)
		for _, chain := range alloc.sortedChains() {
			result += fmt.Sprintf("%s:", chain.Register)
			for _, link := range chain.links {
				result += fmt.Sprintf(" %d%v", link.id-firstLink, link.liveRange.intervals)
			}
			result += "\n"
		}
		regMoves, _ := alloc.findMoves(blocks)
		for _, block := range blocks {
			for _, call := range block.calls {
				moves := regMoves[call]
				if moves != nil {
					result += fmt.Sprintf("%v\n", *moves)
				}
			}
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

// Run a program, checking that every register that is read contains the
// right value.  Values are just distinct integers.
func simulate(
	t *testing.T,
	random *rand.Rand,
	start *regBlockT,
	moves map[*CallNodeT]*RegMovesT,
	maxBlocks int,
) {
	t.Helper()
	locations := map[RegLocationT]int{} // registers and slots
	values := map[*VariableT]int{}
	nextValue := 1
	read := func(call *CallNodeT, i int) int {
		vart := call.Inputs[i].(*ReferenceNodeT).Variable
		value := locations[RegLocationT{Register: vart.ReferenceRegister(call.Inputs[i])}]
		if value != values[vart] {
			t.Fatalf("%s_%d has the wrong value", vart.Name, vart.Id)
		}
		return value
	}
	write := func(vart *VariableT, value int) {
		constant := vart.constant()
		if constant != nil {
			// The value is always the same and can be loaded at any point.
			location := RegLocationT{Constant: constant}
			if locations[location] == 0 {
				locations[location] = value
			}
			value = locations[location]
		}
		// Constants and unused values may not have registers.
		if vart.Register() != nil {
			locations[RegLocationT{Register: vart.Register()}] = value
		}
		values[vart] = value
	}
	doMoves := func(moves []RegMoveT) {
		moved := map[RegLocationT]int{}
		for _, move := range moves {
			if move.To.Constant != nil {
				t.Fatalf("move to a constant")
			}
			_, found := moved[move.To]
			if found {
				t.Fatalf("two moves to the same location")
			}
			moved[move.To] = locations[move.From]
		}
		maps.Copy(locations, moved)
	}
	arguments := []int{} // from the previous block's jump
	block := start
	for range maxBlocks {
		for i, call := range block.calls {
			isJump := call.Primop.Name() == "jump"
			callMoves := moves[call]
			if callMoves != nil {
				doMoves(callMoves.Before)
				doMoves(callMoves.At)
			}
			for j, spec := range block.inputSpecs[i] {
				if spec != nil && spec.Fixed != nil && !isJump {
					vart := call.Inputs[j].(*ReferenceNodeT).Variable
					if locations[RegLocationT{Register: spec.Fixed}] != values[vart] {
						t.Fatalf("%s_%d is not in its fixed register", vart.Name, vart.Id)
					}
				}
			}
			primop, ok := call.Primop.(ClobbersRegistersT)
			if ok {
				for _, register := range primop.ClobberedRegisters(call) {
					delete(locations, RegLocationT{Register: register})
				}
			}
			jumpArguments := arguments
			arguments = []int{}
			for _, phase := range []int{EarlyRegUse, LateRegUse} {
				for j, spec := range block.inputSpecs[i] {
					if spec != nil && spec.PhaseOffset == phase && spec.Fixed == nil {
						if isJump {
							// These may not be in registers.
							vart := call.Inputs[j].(*ReferenceNodeT).Variable
							Push(&arguments, values[vart])
						} else {
							read(call, j)
						}
					}
				}
				for j, spec := range block.outputSpecs[i] {
					if spec.PhaseOffset != phase {
						continue
					} else if len(jumpArguments) != 0 {
						values[call.Outputs[j]] = jumpArguments[j] // moved by the jump
					} else if spec.Fixed != nil {
						locations[RegLocationT{Register: spec.Fixed}] = nextValue
						values[call.Outputs[j]] = nextValue
						nextValue += 1
					} else {
						write(call.Outputs[j], nextValue)
						nextValue += 1
					}
				}
			}
		}
		if len(block.next) == 0 {
			return
		}
		block = block.next[random.Intn(len(block.next))]
	}
}

// No variable may have two links at a program point.
func checkLinks(t *testing.T, alloc *allocatorT) {
	t.Helper()
	type pointT struct {
		vart  *VariableT
		point int
	}
	points := util.NewSet[pointT]()
	for _, link := range alloc.allLinks() {
		for _, interval := range link.liveRange.intervals {
			for i := interval.start; i < interval.end; i++ {
				point := pointT{link.variable, i}
				if points.Contains(point) {
					t.Fatalf("parallel links for %s_%d at %d", link.variable.Name, link.variable.Id, i)
				}
				points.Add(point)
			}
		}
	}
}

func TestMergeRandom(t *testing.T) {
	results := map[string]int{}
	for seed := range 4000 {
		registers := 3 + seed%6
		setTestRegisters(registers)
		useAllocatedFixed(seed%3 == 1)
		random := rand.New(rand.NewSource(int64(seed)))
		loops := seed%4 != 0
		blocks := orderBlocks(randomTestBlocks(random, 12, registers-1, loops)[0])
		alloc := allocateTestBlocks(blocks)
		kind := "straight"
		for _, block := range blocks {
			if block.loop != nil {
				kind = "loop"
				if len(block.loop.links) != 0 {
					kind = "loop with links"
					break
				}
			}
		}
		checkLinks(t, alloc)
		checkAllocation(t, alloc)
		regMoves, frame := alloc.findMoves(blocks)
		results[kind] += 1
		if 0 < frame.NumSlots {
			results[kind+" with spills"] += 1
		}
		for range 10 {
			simulate(t, random, blocks[0], regMoves, 60)
		}
	}
	useAllocatedFixed(false)
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
	// Anchors in adjacent calls would be merged before the searches start.
	block.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	block.addTestCall(vars, EarlyRegUse, nil, LateRegUse)
	firstUse := block.end.Inputs[0]
	block.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	block.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
	block.addTestCall(vars, EarlyRegUse, nil, LateRegUse)
	alloc := &allocatorT{
		allVars:          util.NewSet[*VariableT](),
		allChains:        util.NewSet[*chainT](),
		numProgramPoints: block.endIndex,
	}
	alloc.makeLinks([]*regBlockT{block})
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

func TestCanMerge(t *testing.T) {
	setTestRegisters(2)
	makeChain := func(conflicts ...*chainT) *chainT {
		chain := newChain(&linkT{}, testClass)
		for _, other := range conflicts {
			chain.conflicts.Add(other)
			other.conflicts.Add(chain)
		}
		return chain
	}
	a := makeChain()
	n1 := makeChain(a)
	n2 := makeChain(a, n1) // n1 and n2 each have two neighbors
	n3 := makeChain(n1, n2)
	minor := makeChain()
	alloc := &allocatorT{chainPoints: []util.SetT[*chainT]{
		util.NewSet(n1),
		util.NewSet(n3),
		util.NewSet(minor),
	}}
	tests := []struct {
		name     string
		chains   []*chainT
		live     *liveRangeT
		expected bool
	}{
		// Two significant neighbors, n1 and n2, so this fails Briggs.
		{"George", []*chainT{a}, liveRange(0, 1), true},
		// Adds n3, which is not a neighbor of 'a'.
		{"neither", []*chainT{a}, liveRange(1, 2), false},
		// 'minor' is not a neighbor of 'a', but it is not significant.
		{"George with insignificant neighbor", []*chainT{a}, liveRange(2, 3), true},
		{"Briggs", nil, liveRange(0, 1), true},
		{"merged neighbors", []*chainT{a, n3}, liveRange(2, 3), true},
		{"conflicting chains", []*chainT{a, n1}, liveRange(2, 3), false},
		{"nothing added", []*chainT{a}, liveRange(), true},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if alloc.canMerge(test.chains, test.live, testClass) != test.expected {
				t.Errorf("canMerge is not %v", test.expected)
			}
		})
	}
}
