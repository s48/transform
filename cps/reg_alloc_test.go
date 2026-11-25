// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package cps

import (
	"slices"
	"testing"

	"github.com/s48/transform/util"
)

func TestOrderBlocks(t *testing.T) {
	tests := []struct {
		name     string
		next     [][]int // indexes of each block's next blocks
		expected []int
	}{
		{"single", [][]int{{}}, []int{0}},
		{"line", [][]int{{1}, {2}, {}}, []int{0, 1, 2}},
		{"diamond", [][]int{{1, 2}, {3}, {3}, {}}, []int{0, 1, 2, 3}},
		{"uneven diamond", [][]int{{1, 3}, {2}, {3}, {}}, []int{0, 1, 2, 3}},
		{"uneven diamond swapped", [][]int{{3, 1}, {2}, {3}, {}}, []int{0, 1, 2, 3}},
		{"two diamonds", [][]int{{1, 2}, {3}, {3}, {4, 5}, {6}, {6}, {}},
			[]int{0, 1, 2, 3, 4, 5, 6}},
		{"loop", [][]int{{1}, {2, 3}, {1}, {}}, []int{0, 1, 2, 3}},
		{"self loop", [][]int{{0, 1}, {}}, []int{0, 1}},
		{"unreachable", [][]int{{2}, {2}, {}}, []int{0, 2}},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			blocks := []*regBlockT{}
			for range test.next {
				blocks = append(blocks, makeRegBlock())
			}
			for i, nexts := range test.next {
				for _, next := range nexts {
					blocks[i].addNext(blocks[next])
				}
			}
			order := []int{}
			for _, block := range orderBlocks(blocks[0]) {
				order = append(order, slices.Index(blocks, block))
			}
			if !slices.Equal(order, test.expected) {
				t.Errorf("got order %v, expected %v", order, test.expected)
			}
		})
	}
}

//----------------------------------------------------------------
// Testing findLiveRanges() on hand-built blocks.

type testPrimopT struct {
	PrimopT // for the methods that are not used here
	name    string
}

func (primop testPrimopT) Name() string { return primop.name }

var testClass = &RegisterClassT{Name: "test"}

// All inputs have the same phase, as do all outputs.
func (block *regBlockT) addTestCall(
	inputs []*VariableT,
	inputPhase int,
	outputs []*VariableT,
	outputPhase int,
) {
	class := testClass
	call := &CallNodeT{Primop: testPrimopT{name: "test"}, Outputs: outputs}
	var inputSpecs, outputSpecs []*RegUseSpecT
	for _, vart := range inputs {
		call.Inputs = append(call.Inputs, &ReferenceNodeT{Variable: vart})
		inputSpecs = append(inputSpecs, &RegUseSpecT{PhaseOffset: inputPhase, Class: class})
	}
	for range outputs {
		outputSpecs = append(outputSpecs, &RegUseSpecT{PhaseOffset: outputPhase, Class: class})
	}
	if block.start == nil {
		block.start = call
		call.Block = block
	} else {
		call.parent = block.end
	}
	block.end = call
	block.inputSpecs = append(block.inputSpecs, inputSpecs)
	block.outputSpecs = append(block.outputSpecs, outputSpecs)
	block.callCount += 1
	block.endIndex = block.startIndex + 2*block.callCount
}

// The program points of all links of a variable, which must not overlap.
func variablePoints(t *testing.T, vart *VariableT) []intervalT {
	t.Helper()
	result := &liveRangeT{}
	seen := map[*linkT]bool{}
	var visit func(link *linkT)
	visit = func(link *linkT) {
		if seen[link] {
			return
		}
		seen[link] = true
		for _, interval := range link.liveRange.intervals {
			if interval.end <= interval.start {
				t.Errorf("bad interval %v", interval)
			}
		}
		result = result.union(&link.liveRange)
		for _, end := range link.ends {
			visit(end)
		}
	}
	visit(vart.definition)
	return result.intervals
}

// X is defined by the last call in the first block and used in the
// first call in the second.  Y is defined by the first call in the
// first block and used in both last calls.
func TestFindLiveRangesBoundary(t *testing.T) {
	for _, inputPhase := range []int{EarlyRegUse, LateRegUse} {
		for _, outputPhase := range []int{EarlyRegUse, LateRegUse} {
			x := &VariableT{Name: "x", Id: 1}
			y := &VariableT{Name: "y", Id: 2}
			xs := []*VariableT{x}
			ys := []*VariableT{y}

			first := makeRegBlock()
			first.addTestCall(nil, inputPhase, ys, outputPhase) // 0, 1
			first.addTestCall(ys, inputPhase, xs, outputPhase)  // 2, 3
			second := makeRegBlock()
			second.startIndex = first.endIndex
			second.addTestCall(xs, inputPhase, nil, outputPhase) // 4, 5
			second.addTestCall(ys, inputPhase, nil, outputPhase) // 6, 7
			first.addNext(second)

			alloc := &allocatorT{
				allVars:   util.NewSet[*VariableT](),
				allChains: util.NewSet[*chainT](),
			}
			alloc.makeLinks([]*regBlockT{first, second})

			xExpected := intervals(3+outputPhase, 5+inputPhase+1)
			xPoints := variablePoints(t, x)
			if !slices.Equal(xPoints, xExpected) {
				t.Errorf("x is %v, expected %v", xPoints, xExpected)
			}
			yExpected := intervals(1+outputPhase, 7+inputPhase+1)
			yPoints := variablePoints(t, y)
			if !slices.Equal(yPoints, yExpected) {
				t.Errorf("y is %v, expected %v", yPoints, yExpected)
			}
		}
	}
}

// Variable X is defined in the first block and used, early, in the
// last call of some of the others.  Every block has two calls.
// Block indexes are already in reverse postorder.
func TestFindLiveRangesBranches(t *testing.T) {
	tests := []struct {
		name     string
		next     [][]int // indexes of each block's next blocks
		uses     []int   // blocks that use X
		expected []intervalT
		// The length of 'ends' for X's connecting links, by program point.
		ends map[int]int
	}{
		{"same use", [][]int{{1, 2}, {3}, {3}, {}}, []int{3},
			intervals(1, 15), map[int]int{2: 2, 4: 1, 8: 1, 12: 1}},
		{"same use, one side empty", [][]int{{1, 2}, {2}, {}}, []int{2},
			intervals(1, 11), map[int]int{2: 2, 4: 1, 8: 1}},
		{"different uses", [][]int{{1, 2}, {}, {}}, []int{1, 2},
			intervals(8, 11, 1, 7), map[int]int{2: 2, 4: 1, 8: 1}},
		{"one side unused", [][]int{{1, 2}, {}, {}}, []int{1},
			intervals(1, 7), map[int]int{2: 1, 4: 1}},
		{"use on one side and after", [][]int{{1, 2}, {3}, {3}, {}}, []int{1, 3},
			intervals(1, 15), map[int]int{2: 2, 4: 1, 8: 1, 12: 1}},
		{"uses on both sides and after", [][]int{{1, 2}, {3}, {3}, {}}, []int{1, 2, 3},
			intervals(1, 15), map[int]int{2: 2, 4: 1, 8: 1, 12: 1}},
		{"crossed", [][]int{{1, 2}, {3, 4}, {3, 4}, {}, {}}, []int{3, 4},
			intervals(16, 19, 1, 15), map[int]int{2: 2, 4: 2, 8: 2, 12: 1, 16: 1}},
		{"partly crossed", [][]int{{1, 2}, {3, 4}, {3}, {}, {}}, []int{3, 4},
			intervals(16, 19, 1, 15), map[int]int{2: 2, 4: 2, 8: 1, 12: 1, 16: 1}},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			x := &VariableT{Name: "x", Id: 1}
			xs := []*VariableT{x}
			blocks := []*regBlockT{}
			for i := range test.next {
				block := makeRegBlock()
				block.startIndex = 4 * i
				if i == 0 {
					block.addTestCall(nil, EarlyRegUse, xs, LateRegUse)
				} else {
					block.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
				}
				if slices.Contains(test.uses, i) {
					block.addTestCall(xs, EarlyRegUse, nil, LateRegUse)
				} else {
					block.addTestCall(nil, EarlyRegUse, nil, LateRegUse)
				}
				blocks = append(blocks, block)
			}
			for i, nexts := range test.next {
				for _, next := range nexts {
					blocks[i].addNext(blocks[next])
				}
			}
			alloc := &allocatorT{
				allVars:   util.NewSet[*VariableT](),
				allChains: util.NewSet[*chainT](),
			}
			alloc.makeLinks(blocks)

			points := variablePoints(t, x)
			if !slices.Equal(points, test.expected) {
				t.Errorf("x is %v, expected %v", points, test.expected)
			}

			links := []*linkT{}
			var collect func(link *linkT)
			collect = func(link *linkT) {
				if slices.Contains(links, link) {
					return
				}
				links = append(links, link)
				for _, end := range link.ends {
					if !slices.Contains(end.starts, link) {
						t.Errorf("link %d missing start %d", end.id, link.id)
					}
					collect(end)
				}
			}
			collect(x.definition)

			previous := make([]int, len(blocks)) // number of previous blocks
			for _, nexts := range test.next {
				for _, next := range nexts {
					previous[next] += 1
				}
			}

			for _, link := range links {
				if link.chain != nil {
					continue
				}
				if 1 < len(link.liveRange.intervals) {
					t.Errorf("link %d has several intervals %v", link.id, link.liveRange.intervals)
				}
				for _, interval := range link.liveRange.intervals {
					i := interval.start / 4
					if i != (interval.end-1)/4 {
						t.Errorf("link %d crosses a block boundary: %v", link.id, interval)
					}
					// X is live at the end of every previous block.
					if interval.start == blocks[i].startIndex &&
						len(link.starts) != previous[i] {
						t.Errorf("link at %d has %d starts, expected %d",
							interval.start, len(link.starts), previous[i])
					}
				}
			}
			for point, count := range test.ends {
				index := slices.IndexFunc(links, func(link *linkT) bool {
					return link.chain == nil &&
						link.liveRange.intervalConflicts(intervalT{point, point + 1})
				})
				if index < 0 {
					t.Errorf("no connecting link at %d", point)
				} else if len(links[index].ends) != count {
					t.Errorf("link at %d has %d ends, expected %d",
						point, len(links[index].ends), count)
				}
			}
		})
	}
}

// Make the last call added to the block be a jump to the target block.
func (block *regBlockT) makeTestJump(target *regBlockT) {
	block.end.Primop = testPrimopT{name: "jump"}
	block.end.Inputs = append([]NodeT{target.start}, block.end.Inputs...)
	specs := &block.inputSpecs[block.callCount-1]
	*specs = append([]*RegUseSpecT{nil}, *specs...)
	block.jumpLinks = make([]*linkT, len(*specs)-1)
	block.addNext(target)
}

// Check that the variables' jump argument links are connected to 'output'.
func expectJumpStarts(t *testing.T, output *VariableT, arguments ...*linkT) {
	t.Helper()
	starts := []*linkT{}
	for _, connect := range output.definition.starts {
		if connect.chain != nil || len(connect.liveRange.intervals) != 0 ||
			len(connect.starts) != 1 || len(connect.ends) != 1 ||
			connect.ends[0] != output.definition {
			t.Errorf("bad connecting link for %s", output.Name)
			continue
		}
		argument := connect.starts[0]
		if connect.variable != argument.variable || !slices.Contains(argument.ends, connect) {
			t.Errorf("bad argument link for %s", output.Name)
		}
		starts = append(starts, argument)
	}
	if !slices.Equal(starts, arguments) {
		t.Errorf("wrong arguments for %s", output.Name)
	}
}

// The first block jumps to the second, which loops back to itself via
// the third.  Output Q of the second block is passed the same variable
// as P on entry, and the two are swapped by the loop.
func TestConnectJump(t *testing.T) {
	a := &VariableT{Name: "a", Id: 1}
	p := &VariableT{Name: "p", Id: 2}
	q := &VariableT{Name: "q", Id: 3}
	unused := &VariableT{Name: "unused", Id: 4}

	entry := makeRegBlock()
	entry.addTestCall(nil, EarlyRegUse, []*VariableT{a}, LateRegUse)       // 0, 1
	entry.addTestCall([]*VariableT{a, a, a}, EarlyRegUse, nil, LateRegUse) // 2, 3
	loop := makeRegBlock()
	loop.startIndex = entry.endIndex
	loop.addTestCall(nil, EarlyRegUse, []*VariableT{p, q, unused}, EarlyRegUse) // 4, 5
	loop.addTestCall([]*VariableT{p}, EarlyRegUse, nil, LateRegUse)             // 6, 7
	back := makeRegBlock()
	back.startIndex = loop.endIndex
	back.addTestCall([]*VariableT{q, p, p}, EarlyRegUse, nil, LateRegUse) // 8, 9
	// The last argument is not in a register.
	back.inputSpecs[0][2] = nil
	exit := makeRegBlock()
	exit.startIndex = back.endIndex
	exit.addTestCall([]*VariableT{q}, EarlyRegUse, nil, LateRegUse) // 10, 11

	loop.addNext(back)
	loop.addNext(exit)
	entry.makeTestJump(loop)
	back.makeTestJump(loop)

	blocks := orderBlocks(entry)
	if !slices.Equal(blocks, []*regBlockT{entry, loop, back, exit}) {
		t.Fatalf("blocks in wrong order")
	}
	alloc := &allocatorT{
		allVars:   util.NewSet[*VariableT](),
		allChains: util.NewSet[*chainT](),
	}
	alloc.makeLinks(blocks)

	aLink := a.uses[entry.end.Inputs[1]]
	pLink := p.uses[back.end.Inputs[2]]
	qLink := q.uses[back.end.Inputs[1]]
	expectJumpStarts(t, p, aLink, qLink)
	expectJumpStarts(t, q, aLink, pLink)
	expectJumpStarts(t, unused, aLink)
	if len(exit.start.Inputs) != 1 || len(q.uses[exit.start.Inputs[0]].ends) != 0 {
		t.Errorf("exit use should have no ends")
	}
}

func TestJumpRegisterUsage(t *testing.T) {
	call := MakeCall(&JumpPrimopT{}, nil,
		MakeReferenceNode(MakeVariable("target", nil)),
		MakeReferenceNode(MakeVariable("x", nil)))
	inputs, _ := call.Primop.RegisterUsage(call)
	if len(inputs) != 2 || inputs[0] != nil || inputs[1] != jumpRegUseSpec {
		t.Errorf("wrong jump input specs %v", inputs)
	}
}
