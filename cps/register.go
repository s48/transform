// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Register allocation.
// This uses a simplified version of Cranelift's register allocator.
//   https://cfallin.org/blog/2022/06/09/cranelift-regalloc2/
// One of the simplifications is that it doesn't handle spills (yet).

package cps

import (
	"fmt"
	"math/bits"
	"slices"
	"sort"

	"github.com/s48/transform/util"
)

// Variable fields used for register allocation.

type varRegAllocT struct {
	bundle   *bundleT  // register allocation data
	Register RegisterT // the register that eventually gets assigned
}

// We start with one bundle per variable and one regAlloc per bundle.
// The initial regAlloc has the variable's liveRange.  In the bundling
// phase bundles can be merged, resulting in bundles that have more
// than one variable but still just one regAlloc whose live range is
// the union of the variables' liveRanges.  Then during allocation
// regAllocs can be split, resulting in bundles with multiple regAllocs.

type bundleT struct {
	vars      util.SetT[*VariableT]
	regAlloc  *regAllocT            // the original regAlloc for this bundle
	regAllocs util.SetT[*regAllocT] // splits
	uses      []regUseT             // specs for the various reg uses
	// memAlloc // overflow location in memory
}

func (vart *VariableT) getBundle() *bundleT {
	if vart.bundle == nil {
		bundle := &bundleT{vars: util.NewSet(vart), regAllocs: util.NewSet[*regAllocT]()}
		bundle.regAlloc = &regAllocT{bundle: bundle}
		vart.bundle = bundle
	}
	return vart.bundle
}

// One use of a variable
type regUseT struct {
	callIndex int         // the index of the call containing the use
	spillCost int         // for future use
	isWrite   bool        // true for outputs, false for inputs
	spec      RegUseSpecT // register constraints
}

type RegUseSpecT struct {
	IsEarly      bool // true if the register during the call
	Class        *RegisterClassT
	RegisterMask uint64 // which registers can be used here
}

// A set of registers.  The same register may be in more than one
// class.
type RegisterClassT struct {
	Name      string
	Registers []RegisterT
}

type RegisterT interface {
	Class() *RegisterClassT
	String() string
}

// A single register allocation with the liveRange for which the
// allocation is valid.  If a regAlloc is split during allocation
// the new regAlloc is added to the bundle.
type regAllocT struct {
	bundle          *bundleT
	Class           *RegisterClassT
	allowedRegsMask uint64 // all the RegUseSpecT masks &'ed together
	liveRange       liveRangeT
	Register        RegisterT // what gets assigned to this
}

type liveRangeT struct {
	intervals []intervalT
}

type intervalT struct {
	start int // index of call, inclusive
	end   int // ditto, exclusive
}

func (live *liveRangeT) add(interval intervalT) {
	intervals := live.intervals
	if len(intervals) != 0 {
		last := &intervals[len(intervals)-1]
		if interval.start == last.end {
			last.end = interval.end
			return
		}
	}
	live.intervals = append(live.intervals, interval)
}

func (live *liveRangeT) conflicts(other *liveRangeT) bool {
	x := live.intervals
	y := other.intervals
	i := 0
	j := 0
	for i < len(x) && j < len(y) {
		if x[i].end <= y[j].start {
			i += 1
		} else if y[j].end <= x[i].start {
			j += 1
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
		if x[i].start <= y[j].start {
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

//----------------------------------------------------------------
// bundle methods

// Merge 'other' into this bundle.
func (bundle *bundleT) join(other *bundleT) {
	for _, vart := range other.vars.Members() {
		bundle.vars.Add(vart)
		vart.bundle = bundle
	}
	bundle.regAlloc.liveRange = *bundle.regAlloc.liveRange.union(&other.regAlloc.liveRange)
	other.regAlloc = nil // mark it as empty
}

// These will need spill costs as well, which means they need the loop depth.
func (bundle *bundleT) addDefinition(index int, spec *RegUseSpecT) {
	regUse := regUseT{callIndex: index, isWrite: true, spec: *spec}
	bundle.uses = append(bundle.uses, regUse)
}

func (bundle *bundleT) addUse(index int, spec *RegUseSpecT) {
	regUse := regUseT{callIndex: index, spec: *spec}
	bundle.uses = append(bundle.uses, regUse)
}

func (bundle *bundleT) addInterval(start int, end int) {
	vart := bundle.vars.Members()[0] // there is only one at this point
	if end == 0 {
		panic(fmt.Sprintf("%s_%d has an interval ending at zero", vart.Name, vart.Id))
	}
	// can's use liveRange.add because the intervals are in
	// reverse order at this point
	intervals := bundle.regAlloc.liveRange.intervals
	if len(intervals) != 0 {
		last := &intervals[len(intervals)-1]
		if end == last.start {
			last.start = start
			return
		}
	}
	bundle.regAlloc.liveRange.intervals = append(intervals, intervalT{start, end})
}

// - Reverses slices to go from bottom-up to top-down.
// - Goes through the uses to find the register class and
//   for the bundle's initial regAlloc allowedRegsMask
// Returns false if no register needs to be allocated.

func (bundle *bundleT) initialize() bool {
	slices.Reverse(bundle.uses)
	slices.Reverse(bundle.regAlloc.liveRange.intervals)
	vart := bundle.vars.Members()[0]
	if len(bundle.uses) == 0 {
		return false
	}
	var class *RegisterClassT
	mask := ^uint64(0)
	for _, use := range bundle.uses {
		if use.spec.Class == jumpRegUseSpec.Class {
			continue
		}
		if class == nil {
			class = use.spec.Class
		} else if use.spec.Class != class {
			panic(fmt.Sprintf("bundle %s_%d has two register classes %s and %s", vart.Name, vart.Id,
				use.spec.Class.Name, class.Name))
		}
		mask &= use.spec.RegisterMask
	}
	if class == nil {
		return false
	}
	// fmt.Printf("bundle class %s", class.Name)
	// for vart, _ := range bundle.vars {
	//		fmt.Printf(" %s_%v", vart.Name, vart.Id)
	// }
	// fmt.Printf("\n")
	bundle.regAlloc.Class = class
	bundle.regAlloc.allowedRegsMask = mask
	if mask == 0 {
		panic(fmt.Sprintf("bundle %s_%d has no allowable registers", vart.Name, vart.Id))
	}
	return true
}

// Variable ranges are found bottom up.  If the block ends with a
// jump we need to create ranges for its inputs but we do not have
// any immediate way of determining their register specs.  This
// class is used as a stand-in and is later ignored in favor of
// the actual class given by a primitive.

var jumpRegisterClass = &RegisterClassT{Name: "jump", Registers: nil}
var jumpRegUseSpec = &RegUseSpecT{Class: jumpRegisterClass, IsEarly: true}

//----------------------------------------------------------------

type regBlockT struct {
	start      *CallNodeT
	end        *CallNodeT
	startIndex int // index of 'start' within the total call ordering
	callCount  int // number of calls in the block
	next       []*regBlockT
	previous   []*regBlockT
	isJump     bool

	bound util.SetT[*VariableT] // bound within the block
	live  util.SetT[*VariableT] // live at block.start
}

func makeRegBlock() *regBlockT {
	return &regBlockT{bound: util.SetT[*VariableT]{}, live: util.SetT[*VariableT]{}}
}

// Finds the bound and live variables in the block.

func (block *regBlockT) initialize(start *CallNodeT, end *CallNodeT) {
	block.start = start
	block.end = end
	block.isJump = start.CallType != CallExit
	call := start
	count := 1
	for {
		for _, vart := range call.Outputs {
			block.bound.Add(vart)
		}
		for i := 0; i < len(call.Inputs); i++ {
			vart := call.InputVariable(i)
			if vart != nil {
				block.live.Add(vart)
			}
		}
		if call == end {
			break
		}
		count += 1
		call = call.Next[0]
	}
	for vart, _ := range block.bound {
		block.live.Remove(vart)
	}
	block.callCount = count
}

func (block *regBlockT) addNext(rawNext BasicBlockT) {
	next := rawNext.(*regBlockT)
	block.next = append(block.next, next)
	next.previous = append(next.previous, block)
}

func (block *regBlockT) getEnd() *CallNodeT {
	return block.end
}

func AllocateRegisters(top *CallNodeT) {
	makeVarsForLiterals()
	blocks := FindBasicBlocks[*regBlockT](top, makeRegBlock)
	index := 0
	for _, block := range blocks {
		block.startIndex = index
		index += block.callCount
	}

	// Transitive closure of live variables.
	change := true
	for change {
		change = false
		for _, block := range blocks {
			for _, next := range block.next {
				for vart, _ := range next.live {
					if !block.bound.Contains(vart) && !block.live.Contains(vart) {
						block.live.Add(vart)
						change = true
					}
				}
			}
		}
	}
	/*
	   for _, block := range blocks {
	       fmt.Printf("block %s_%d live", block.start.Name, block.start.Id)
	       for _, vart := range block.live.Members() {
	           fmt.Printf(" %s_%d", vart.Name, vart.Id)
	       }
	       fmt.Printf("\n")
	   }
	*/

	allVars := util.NewSet[*VariableT]()
	for i := len(blocks) - 1; 0 <= i; i-- {
		findLiveRanges(blocks[i].start, &allVars)
	}
	vars := allVars.Members()
	// Sort the variables to get deterministic behavior.
	sort.Slice(vars, func(i int, j int) bool {
		return vars[i].Id < vars[j].Id
	})

	bundleQueue := QueueT[*bundleT]{}
	for _, vart := range vars {
		if vart.bundle.initialize() {
			bundleQueue.Enqueue(vart.bundle)
		}
		/*
			fmt.Printf("ranges %s_%d", vart.Name, vart.Id)
			for _, interval := range vart.bundle.regAlloc.liveRange.intervals {
				fmt.Printf(" %d:%d", interval.start, interval.end)
			}
			fmt.Printf("\n")
		*/
	}

	// Merge bundles across jumps where possible.
	for _, block := range blocks {
		if block.isJump {
			findJumpConnections(block)
		}
	}

	// Get the regAllocs
	regAllocQueue := QueueT[*regAllocT]{}
	for !bundleQueue.Empty() {
		bundle := bundleQueue.Dequeue()
		if bundle.regAlloc != nil {
			regAllocQueue.Enqueue(bundle.regAlloc)
		}
	}

	regLiveRanges := map[RegisterT]*liveRangeT{}
	for !regAllocQueue.Empty() {
		regAlloc := regAllocQueue.Dequeue()
		okay := false
		mask := regAlloc.allowedRegsMask
		for mask != 0 {
			i := bits.TrailingZeros64(mask)
			if i == 64 {
				break
			}
			reg := regAlloc.Class.Registers[i]
			regLiveRange := regLiveRanges[reg]
			if regLiveRange == nil || !regLiveRange.conflicts(&regAlloc.liveRange) {
				if regLiveRange == nil {
					regLiveRange = &liveRangeT{}
				}
				regAlloc.Register = reg
				regLiveRanges[reg] = regLiveRange.union(&regAlloc.liveRange)
				okay = true
				break
			}
			mask ^= 1 << i
		}
		if !okay {
			// splitting will go here
			panic("failed to allocate register")
		}
	}

	// Once we are splitting each regAlloc will need to be its own
	// variable.  All but the first will be the output of a move
	// instruction.  Alternatively we could generate code directly
	// without reifying the register allocation and moves in the
	// node program.
	// Instead of adding a lot of separate move calls, have a generic
	// 'move' primop that has any number of inputs and outputs as well
	// as a literal input, or closed-over data, that says which moves
	// to make.
	for _, vart := range vars {
		vart.Register = vart.bundle.regAlloc.Register
	}
}

func findLiveRanges(top *CallNodeT, allVars *util.SetT[*VariableT]) {
	ends := map[*VariableT]int{}
	block := top.Block.(*regBlockT)
	startIndex := block.startIndex * 2             // early block.start
	endIndex := startIndex + block.callCount*2 - 1 // late block.end
	/*
		fmt.Printf("findLiveRanges %d start %d end %d\n", top.Id, startIndex, endIndex)
		for _, next := range block.next {
			fmt.Printf("   next %d", next.start.Id)
			for vart, _ := range next.live {
				fmt.Printf(" %s_%d", vart.Name, vart.Id)
			}
			fmt.Printf("\n")
		}
	*/
	for _, next := range block.next {
		for vart, _ := range next.live {
			ends[vart] = endIndex
			allVars.Add(vart)
		}
	}
	lateIndex := endIndex
	for call := block.end; call != top.parent; call = call.parent {
		inputs, outputs := call.Primop.RegisterUsage(call)
		// fmt.Printf("call %d(%s) %d lateIndex %d\n",
		//     call.Id, call.Primop.Name(), len(call.Outputs), lateIndex)
		if outputs != nil {
			if len(outputs) != len(call.Outputs) {
				panic(fmt.Sprintf("Primop %s returned %d output registers but has %d outputs.",
					call.Primop.Name(), len(outputs), len(call.Outputs)))
			}
			for i, vart := range call.Outputs {
				if outputs[i] != nil {
					index := lateIndex
					if outputs[i].IsEarly {
						index -= 1
					}
					// fmt.Printf("  %s_%d index %d\n", vart.Name, vart.Id, index)
					vart.getBundle().addDefinition(index, outputs[i])
					// +1 for inclusive -> exclusive
					vart.getBundle().addInterval(index, ends[vart]+1)
				}
			}
		}
		if inputs != nil {
			if len(inputs) != len(call.Inputs) {
				panic(fmt.Sprintf("Primop %s returned %d input registers but has %d inputs.",
					call.Primop.Name(), len(inputs), len(call.Inputs)))
			}
			for i, input := range call.Inputs {
				if inputs[i] == nil || input == nil {
					continue
				}
				if IsReferenceNode(input) {
					vart := input.(*ReferenceNodeT).Variable
					index := lateIndex
					if inputs[i].IsEarly {
						index -= 1
					}
					vart.getBundle().addUse(index, inputs[i])
					_, found := ends[vart]
					if !found {
						ends[vart] = index
						allVars.Add(vart)
					}
				} else {
					panic("got register spec for literal " + CallString(call))
				}
			}
		}
		lateIndex -= 2
	}
	for _, vart := range block.live.Members() {
		// +1 for inclusive -> exclusive
		vart.getBundle().addInterval(startIndex, ends[vart]+1)
	}
}

// Merge bundles across jumps where possible.

func findJumpConnections(block *regBlockT) {
	vars := block.start.Outputs
	for _, prev := range block.previous {
		jump := prev.end
		for i, vart := range vars {
			if !IsReferenceNode(jump.Inputs[i+1]) {
				continue
			}
			other := jump.Inputs[i+1].(*ReferenceNodeT).Variable
			if vart.bundle != other.bundle {
				checkJumpConnection(vart, other)
			}
		}
	}
}

// 'vart' is passed the value of 'other' at a jump.  Merge there
// bundles if they do not conflict.

func checkJumpConnection(vart *VariableT, other *VariableT) {
	if other.bundle == nil {
		panic(fmt.Sprintf("jump connection has no bundle %s_%d", other.Name, other.Id))
	}
	if other.bundle.regAlloc == nil {
		panic(fmt.Sprintf("jump connection bundle has no regAlloc %s_%d", other.Name, other.Id))
	}
	if !(vart.bundle.regAlloc.Class == nil ||
		other.bundle.regAlloc.Class == nil ||
		vart.bundle.regAlloc.Class == other.bundle.regAlloc.Class) {

		panic(fmt.Sprintf("jump connection bundle regAlloc has no class %s_%d", other.Name, other.Id))
	}
	if !vart.bundle.regAlloc.liveRange.conflicts(&other.bundle.regAlloc.liveRange) {
		// fmt.Printf("jump connect %s_%d %s_%d\n", vart.Name, vart.Id, other.Name, other.Id)
		vart.bundle.join(other.bundle)
	}
}
