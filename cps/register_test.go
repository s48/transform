// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package cps

import (
	"math/rand"
	"slices"
	"testing"
)

// Shorthand for a list of intervals, given as start, end pairs.
func intervals(points ...int) []intervalT {
	var result []intervalT
	for i := 0; i < len(points); i += 2 {
		result = append(result, intervalT{points[i], points[i+1]})
	}
	return result
}

// Built directly, to not depend on add().
func liveRange(points ...int) *liveRangeT {
	return &liveRangeT{intervals(points...)}
}

func expectIntervals(t *testing.T, live *liveRangeT, expected []intervalT) {
	t.Helper()
	if !slices.Equal(live.intervals, expected) {
		t.Errorf("got intervals %v, expected %v", live.intervals, expected)
	}
}

func expectPanic(t *testing.T, thunk func()) {
	t.Helper()
	defer func() {
		t.Helper()
		if recover() == nil {
			t.Errorf("expected a panic")
		}
	}()
	thunk()
}

func TestLiveRangeAdd(t *testing.T) {
	tests := []struct {
		name     string
		add      []intervalT
		expected []intervalT
	}{
		{"none", nil, nil},
		{"one", intervals(4, 6), intervals(4, 6)},
		{"gap", intervals(4, 6, 1, 3), intervals(4, 6, 1, 3)},
		{"adjacent", intervals(4, 6, 1, 4), intervals(1, 6)},
		{"chain", intervals(6, 8, 4, 6, 1, 4), intervals(1, 8)},
		{"gap then adjacent", intervals(8, 9, 4, 6, 1, 4), intervals(8, 9, 1, 6)},
		{"adjacent then gap", intervals(6, 8, 4, 6, 1, 3), intervals(4, 8, 1, 3)},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			live := &liveRangeT{}
			for _, interval := range test.add {
				live.add(interval)
			}
			expectIntervals(t, live, test.expected)
		})
	}
}

func TestLiveRangeAddPanics(t *testing.T) {
	tests := []struct {
		name     string
		live     *liveRangeT
		interval intervalT
	}{
		{"above", liveRange(4, 6), intervalT{8, 9}},
		{"adjacent above", liveRange(4, 6), intervalT{6, 9}},
		{"overlaps start", liveRange(4, 6), intervalT{2, 5}},
		{"overlaps end", liveRange(4, 6), intervalT{5, 8}},
		{"identical", liveRange(4, 6), intervalT{4, 6}},
		{"contains", liveRange(4, 6), intervalT{3, 7}},
		{"in earlier gap", liveRange(8, 9, 2, 4), intervalT{5, 7}},
		{"empty", liveRange(), intervalT{3, 3}},
		{"inverted", liveRange(), intervalT{4, 3}},
		{"adjacent but empty", liveRange(4, 6), intervalT{4, 4}},
		{"adjacent but inverted", liveRange(4, 6), intervalT{5, 4}},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			before := slices.Clone(test.live.intervals)
			expectPanic(t, func() { test.live.add(test.interval) })
			expectIntervals(t, test.live, before)
		})
	}
}

func TestLiveRangeClone(t *testing.T) {
	expectIntervals(t, liveRange().clone(), nil)

	original := liveRange(8, 9, 4, 6)
	clone := original.clone()
	expectIntervals(t, clone, intervals(8, 9, 4, 6))
	clone.add(intervalT{3, 4}) // modifies the last interval
	clone.add(intervalT{0, 1})
	expectIntervals(t, clone, intervals(8, 9, 3, 6, 0, 1))
	expectIntervals(t, original, intervals(8, 9, 4, 6))
}

func TestLiveRangeConflicts(t *testing.T) {
	tests := []struct {
		name     string
		x        *liveRangeT
		y        *liveRangeT
		expected bool
	}{
		{"both empty", liveRange(), liveRange(), false},
		{"one empty", liveRange(4, 6), liveRange(), false},
		{"disjoint", liveRange(4, 6), liveRange(1, 3), false},
		{"touching", liveRange(4, 6), liveRange(1, 4), false},
		{"interleaved", liveRange(8, 9, 4, 5), liveRange(6, 7, 2, 3), false},
		{"interleaved touching", liveRange(6, 8, 2, 4), liveRange(4, 6, 0, 2), false},
		{"several in gap", liveRange(20, 22, 0, 2), liveRange(12, 14, 8, 10, 4, 6), false},
		{"overlap", liveRange(4, 6), liveRange(2, 5), true},
		{"nested", liveRange(1, 9), liveRange(4, 5), true},
		{"identical", liveRange(4, 6), liveRange(4, 6), true},
		{"first overlap", liveRange(20, 22, 4, 5), liveRange(21, 23, 1, 2), true},
		{"last overlap", liveRange(20, 22, 4, 8), liveRange(12, 14, 9, 10, 1, 5), true},
		{"spans gap", liveRange(8, 10, 2, 4), liveRange(3, 9), true},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if test.x.conflicts(test.y) != test.expected {
				t.Errorf("x.conflicts(y) is not %v", test.expected)
			}
			if test.y.conflicts(test.x) != test.expected {
				t.Errorf("y.conflicts(x) is not %v", test.expected)
			}
		})
	}
}

func TestLiveRangeIntervalConflicts(t *testing.T) {
	live := liveRange(16, 20, 8, 12)
	tests := []struct {
		name     string
		live     *liveRangeT
		interval intervalT
		expected bool
	}{
		{"empty live range", liveRange(), intervalT{1, 3}, false},
		{"above", live, intervalT{22, 24}, false},
		{"touching top", live, intervalT{20, 24}, false},
		{"in gap", live, intervalT{13, 15}, false},
		{"fills gap", live, intervalT{12, 16}, false},
		{"touching bottom", live, intervalT{6, 8}, false},
		{"below", live, intervalT{2, 4}, false},
		{"overlaps top", live, intervalT{19, 24}, true},
		{"inside first", live, intervalT{17, 18}, true},
		{"first from gap", live, intervalT{14, 17}, true},
		{"second from gap", live, intervalT{11, 14}, true},
		{"inside second", live, intervalT{9, 10}, true},
		{"overlaps bottom", live, intervalT{6, 9}, true},
		{"spans gap", live, intervalT{11, 17}, true},
		{"contains all", live, intervalT{0, 30}, true},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if test.live.intervalConflicts(test.interval) != test.expected {
				t.Errorf("intervalConflicts is not %v", test.expected)
			}
		})
	}
}

func TestLiveRangeUnion(t *testing.T) {
	tests := []struct {
		name     string
		x        *liveRangeT
		y        *liveRangeT
		expected []intervalT
	}{
		{"both empty", liveRange(), liveRange(), nil},
		{"one empty", liveRange(8, 9, 4, 6), liveRange(), intervals(8, 9, 4, 6)},
		{"disjoint", liveRange(4, 6), liveRange(1, 3), intervals(4, 6, 1, 3)},
		{"adjacent", liveRange(4, 6), liveRange(1, 4), intervals(1, 6)},
		{"interleaved", liveRange(8, 9, 4, 5), liveRange(6, 7, 2, 3),
			intervals(8, 9, 6, 7, 4, 5, 2, 3)},
		{"fills gap", liveRange(8, 10, 2, 4), liveRange(4, 8), intervals(2, 10)},
		{"all adjacent", liveRange(6, 8, 2, 4), liveRange(4, 6, 0, 2), intervals(0, 8)},
		{"several left over", liveRange(20, 22), liveRange(12, 14, 8, 10, 4, 6),
			intervals(20, 22, 12, 14, 8, 10, 4, 6)},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			x := test.x.clone()
			y := test.y.clone()
			expectIntervals(t, x.union(y), test.expected)
			expectIntervals(t, y.union(x), test.expected)
			expectIntervals(t, x, test.x.intervals)
			expectIntervals(t, y, test.y.intervals)
		})
	}
}

func TestLiveRangeUnionPanics(t *testing.T) {
	x := liveRange(8, 10, 2, 4)
	y := liveRange(6, 7, 3, 5)
	expectPanic(t, func() { x.union(y) })
	expectPanic(t, func() { y.union(x) })
}

// Compare against sets of program points represented as bit masks.

const numTestPoints = 24

func maskLiveRange(mask uint32) *liveRangeT {
	live := &liveRangeT{}
	for i := numTestPoints - 1; 0 <= i; i-- {
		if (mask>>i)&1 == 1 {
			live.add(intervalT{i, i + 1})
		}
	}
	return live
}

func liveRangeMask(live *liveRangeT) uint32 {
	mask := uint32(0)
	for _, interval := range live.intervals {
		for i := interval.start; i < interval.end; i++ {
			mask |= 1 << i
		}
	}
	return mask
}

// Intervals must be nonempty, in descending order, and not touching.
func checkLiveRange(t *testing.T, live *liveRangeT) {
	t.Helper()
	for i, interval := range live.intervals {
		if interval.end <= interval.start {
			t.Fatalf("bad interval in %v", live.intervals)
		}
		if 0 < i && live.intervals[i-1].start <= interval.end {
			t.Fatalf("intervals out of order or not combined in %v", live.intervals)
		}
	}
}

func TestLiveRangeRandom(t *testing.T) {
	random := rand.New(rand.NewSource(1))
	randomMask := func() uint32 {
		mask := random.Uint32() & (1<<numTestPoints - 1)
		for i := random.Intn(4); 0 < i; i-- {
			mask &= random.Uint32() // fewer points, so fewer conflicts
		}
		return mask
	}
	for range 20000 {
		xMask := randomMask()
		yMask := randomMask()
		if random.Intn(2) == 0 {
			yMask &= ^xMask
		}
		x := maskLiveRange(xMask)
		y := maskLiveRange(yMask)
		checkLiveRange(t, x)
		checkLiveRange(t, y)
		if liveRangeMask(x) != xMask {
			t.Fatalf("%v does not match mask %x", x.intervals, xMask)
		}

		conflict := xMask&yMask != 0
		if x.conflicts(y) != conflict {
			t.Fatalf("%v conflicts %v is not %v", x.intervals, y.intervals, conflict)
		}
		if !conflict {
			union := x.union(y)
			checkLiveRange(t, union)
			if liveRangeMask(union) != xMask|yMask {
				t.Fatalf("%v union %v is %v", x.intervals, y.intervals, union.intervals)
			}
		}

		start := random.Intn(numTestPoints)
		interval := intervalT{start, start + 1 + random.Intn(numTestPoints-start)}
		conflict = xMask&liveRangeMask(&liveRangeT{[]intervalT{interval}}) != 0
		if x.intervalConflicts(interval) != conflict {
			t.Fatalf("%v intervalConflicts %v is not %v", x.intervals, interval, conflict)
		}
	}
}

func (live *liveRangeT) clone() *liveRangeT {
	return &liveRangeT{slices.Clone(live.intervals)}
}
