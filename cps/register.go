// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package cps

import (
	"fmt"
	"math/bits"
	"slices"
)

const (
	EarlyRegUse = -1
	LateRegUse  = 0
)

// How a primop uses a register for one of a call's inputs or outputs.
type RegUseSpecT struct {
	PhaseOffset int // EarlyRegUse or LateRegUse
	Class       *RegisterClassT
	// If non-nil the value has to be in this register, which is not one
	// that the allocator assigns.  The value is moved there, or from there,
	// as part of the call.  Used for passing arguments and return values.
	Fixed RegisterT
}

// Used by the generic primops in primop.go for values passed by jumps and
// procedure calls.  These primops are for evaluating code, and back ends
// supply their own register usage.
var jumpRegisterClass = &RegisterClassT{Name: "jump", registers: nil}
var jumpRegUseSpec = &RegUseSpecT{Class: jumpRegisterClass, PhaseOffset: EarlyRegUse}

// A set of registers.
type RegisterClassT struct {
	Name string
	// These are initialized by SetRegisters.
	registers     []RegisterT // only those registers that can be allocated
	registerIndex map[RegisterT]int
}

func (class *RegisterClassT) SetRegisters(allRegisters []RegisterT, usableMask uint64) {
	registerIndex := map[RegisterT]int{}
	usable := []RegisterT{}
	for i, reg := range allRegisters {
		reg.SetClass(class)
		if (usableMask>>i)&1 == 1 {
			registerIndex[reg] = len(usable)
			usable = append(usable, reg)
		}
	}
	class.registers = usable
	class.registerIndex = registerIndex
}

func (class *RegisterClassT) numRegisters() int {
	return len(class.registers)
}

// Use masks for register sets, as is traditional.
type registerSetT uint64

func (set registerSetT) size() int {
	return bits.OnesCount64(uint64(set))
}

// Primops whose calls change the values of some registers, other than
// those for their outputs, implement this.  Values that are live across
// such a call cannot be in those registers.
type ClobbersRegistersT interface {
	ClobberedRegisters(call *CallNodeT) []RegisterT
}

// All of the class's registers.
func (class *RegisterClassT) newRegisterSet() registerSetT {
	return registerSetT((uint64(1) << len(class.registers)) - 1)
}

func (class *RegisterClassT) removeRegister(
	set registerSetT,
	reg RegisterT,
) registerSetT {
	return set & ^(1 << class.registerIndex[reg])
}

// Return the lowest-numbered register in the set.
func (class *RegisterClassT) firstRegister(set registerSetT) RegisterT {
	mask := uint64(set)
	if mask == 0 {
		panic("no register available")
	}
	index := bits.TrailingZeros64(mask)
	reg := class.registers[index]
	if reg == nil {
		panic(fmt.Sprintf("no register %d in class %s", index, class.Name))
	}
	return reg
}

//----------------------------------------------------------------

type RegisterT interface {
	SetClass(*RegisterClassT) // for initialization
	Class() *RegisterClassT
	String() string
	Number() int
}

type liveRangeT struct {
	intervals []intervalT // nonoverlapping, sorted from highest to lowest
}

type intervalT struct {
	start int // index of call, inclusive
	end   int // ditto, exclusive
}

func (live *liveRangeT) clone() *liveRangeT {
	return &liveRangeT{slices.Clone(live.intervals)}
}

// Intervals must be nonempty and added from highest to lowest.
func (live *liveRangeT) add(interval intervalT) {
	if interval.end <= interval.start {
		panic(fmt.Sprintf("adding bad interval [%d, %d) to live range",
			interval.start, interval.end))
	}
	intervals := live.intervals
	if len(intervals) != 0 {
		last := &intervals[len(intervals)-1]
		if last.start < interval.end {
			panic(fmt.Sprintf("adding interval [%d, %d) that is not below [%d, %d)",
				interval.start, interval.end, last.start, last.end))
		}
		if interval.end == last.start {
			last.start = interval.start
			return
		}
	}
	live.intervals = append(live.intervals, interval)
}

// The number of program points in the live range.
func (live *liveRangeT) size() int {
	size := 0
	for _, interval := range live.intervals {
		size += interval.end - interval.start
	}
	return size
}

func (live *liveRangeT) conflicts(other *liveRangeT) bool {
	x := live.intervals
	y := other.intervals
	i := 0
	j := 0
	for i < len(x) && j < len(y) {
		if x[i].end <= y[j].start {
			j += 1
		} else if y[j].end <= x[i].start {
			i += 1
		} else {
			return true
		}
	}
	return false
}

func (live *liveRangeT) intervalConflicts(y intervalT) bool {
	for _, x := range live.intervals {
		if y.end <= x.start {
			continue
		} else if x.end <= y.start {
			break
		} else {
			return true
		}
	}
	return false
}

func (live *liveRangeT) union(other *liveRangeT) *liveRangeT {
	if live.conflicts(other) {
		panic("union of conflicting live ranges")
	}
	x := live.intervals
	y := other.intervals
	i := 0
	j := 0
	result := &liveRangeT{}
	for i < len(x) && j < len(y) {
		if y[j].start <= x[i].start {
			result.add(x[i])
			i += 1
		} else {
			result.add(y[j])
			j += 1
		}
	}
	for ; i < len(x); i++ {
		result.add(x[i])
	}
	for ; j < len(y); j++ {
		result.add(y[j])
	}
	return result
}
