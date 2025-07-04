// Copyright 2025 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Register allocation.
// This uses a simplified version of Cranelift's register allocator.
//   https://cfallin.org/blog/2022/06/09/cranelift-regalloc2/
//   https://github.com/bytecodealliance/regalloc2/blob/main/doc/ION.md
// One of the simplifications is that it doesn't handle spills (yet).
// The code is in place for determining what, when, and where to spill.
//
// There is one minor added complication.  Cranelift has early and
// late register use points at each instruction while we have early,
// middle, and late.  'Middle' uses don't conflict with either early
// or late and are used for doing interprocedural register allocation.

// Note to self: see the Handling Reused Inputs section in ION.md for
// an important caveat about merging and input and output for an
// instruction that clobbers one of its inputs.  All of the inputs
// (of the same register type) need to be extended to the 'after' slot
// so that they will conflict with the output register.  Othewise
// the move inserted to put the clobbered input in the output register
// will clobber the other input.  We could use middleUse for this,
// having both the inputs and modified output extended to there.

package cps

import (
	"fmt"
	"math"
	"math/bits"
	"math/rand"
	"slices"
	"sort"

	"github.com/s48/transform/util"
)

// Variable fields used for register allocation.

type varRegAllocT struct {
	value    *valueT   // register allocation data
	Register RegisterT // the register that eventually gets assigned
}

// We start with one value per variable and one bundle per value.
// The initial bundle has the variable's bundle.  In the bundling
// phase values can be merged, resulting in values that have more
// than one variable but still just one bundle whose live range is
// the union of the variables' bundles.  Then during allocation
// bundles can be split, resulting in values with multiple bundles.

// The orignal calls this a "spill set".
type valueT struct {
	vars    util.SetT[*VariableT]
	bundle  *bundleT            // the original bundle for this value
	bundles util.SetT[*bundleT] // splits
	// memAlloc // overflow location in memory
}

func (vart *VariableT) getValue() *valueT {
	if vart.value == nil {
		value := &valueT{vars: util.NewSet(vart), bundles: util.NewSet[*bundleT]()}
		value.bundle = &bundleT{value: value}
		vart.value = value
	}
	return vart.value
}

// One use of a variable
type regUseT struct {
	callIndex int         // the index of the call containing the use
	spillCost int         // cost heuristic for spilling this use
	isWrite   bool        // true for outputs, false for inputs
	spec      RegUseSpecT // register constraints
}

const (
	EarlyRegUse  = -2
	MiddleRegUse = -1
	LateRegUse   = 0
)

type RegUseSpecT struct {
	PhaseOffset  int // -2, -1, 0 for early, middle, and late use
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

// A single register allocation with the live range for which the
// allocation is valid.
type bundleT struct {
	value           *valueT
	Class           *RegisterClassT
	allowedRegsMask uint64    // all the RegUseSpecT masks &'ed together
	uses            []regUseT // needed for computing the cost
	liveRange       liveRangeT
	totalLength     int       // sum of interval lengths
	spillCost       int       // sum of use weights
	Register        RegisterT // what gets assigned to this
}

type liveRangeT struct {
	intervals []intervalT // nonoverlapping, sorted by start
}

type intervalT struct {
	start  int // index of call, inclusive
	end    int // ditto, exclusive
	bundle *bundleT
}

func (live *liveRangeT) add(interval intervalT) {
	intervals := live.intervals
	if len(intervals) != 0 {
		last := &intervals[len(intervals)-1]
		if interval.start == last.end && last.bundle == interval.bundle {
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

func (live *liveRangeT) conflicting(other *liveRangeT) *intervalT {
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
			return &x[i]
		}
	}
	return nil
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

func (bundle *bundleT) addIntervals(other *bundleT) {
	if bundle.liveRange.conflicts(&other.liveRange) {
		panic("union of conflicting bundle ranges")
	}
	bundle.uses = append(bundle.uses, other.uses...)
	other.uses = nil
	bundle.spillCost =
		(bundle.spillCost*bundle.totalLength +
			other.spillCost*other.totalLength) /
			(bundle.totalLength + other.totalLength)
	bundle.liveRange = *bundle.liveRange.union(&other.liveRange)
}

//----------------------------------------------------------------
// value methods

// Merge 'other' into this value.
func (value *valueT) join(other *valueT) {
	for _, vart := range other.vars.Members() {
		value.vars.Add(vart)
		vart.value = value
	}
	value.bundle.addIntervals(other.bundle)
	other.bundle = nil // mark it as empty
}

// The spill cost formula is from Cranelift's allocator.

func (value *valueT) addDefinition(index int, spec *RegUseSpecT, loopDepth int) {
	weight := (1<<(min(loopDepth, 10)*2))*1000 + 2000
	regUse := regUseT{callIndex: index, isWrite: true, spec: *spec, spillCost: weight}
	value.bundle.uses = append(value.bundle.uses, regUse)
}

func (value *valueT) addUse(index int, spec *RegUseSpecT, loopDepth int) {
	weight := (1 << (min(loopDepth, 10) * 2)) * 1000
	regUse := regUseT{callIndex: index, spec: *spec, spillCost: weight}
	value.bundle.uses = append(value.bundle.uses, regUse)
}

func (value *valueT) addInterval(start int, end int) {
	if end < start {
		panic("addInterval: end is before start")
	}
	vart := value.vars.Members()[0] // there is only one at this point
	if end == 0 {
		panic(fmt.Sprintf("%s_%d has an interval ending at zero", vart.Name, vart.Id))
	}
	value.bundle.totalLength += end - start
	// can't use bundle.add because the intervals are in
	// reverse order at this point
	intervals := value.bundle.liveRange.intervals
	if len(intervals) != 0 {
		last := &intervals[len(intervals)-1]
		if end == last.start {
			last.start = start
			return
		}
	}
	value.bundle.liveRange.intervals =
		append(intervals, intervalT{start, end, value.bundle})
}

// - Reverses slices to go from bottom-up to top-down.
// - Goes through the uses to find the register class and
//   for the value's initial bundle allowedRegsMask
// Returns false if no register needs to be allocated.

func (value *valueT) initialize() bool {
	bundle := value.bundle
	slices.Reverse(bundle.liveRange.intervals)
	vart := value.vars.Members()[0]
	if len(bundle.uses) == 0 {
		return false
	}
	var class *RegisterClassT
	mask := ^uint64(0)
	spillCost := 0
	for _, use := range bundle.uses {
		spillCost += use.spillCost
		if use.spec.Class == jumpRegUseSpec.Class {
			continue
		}
		if class == nil {
			class = use.spec.Class
		} else if use.spec.Class != class {
			panic(fmt.Sprintf("value %s_%d has two register classes %s and %s", vart.Name, vart.Id,
				use.spec.Class.Name, class.Name))
		}
		mask &= use.spec.RegisterMask
	}
	if class == nil {
		return false
	}
	// fmt.Printf("value class %s", class.Name)
	// for vart, _ := range value.vars {
	//		fmt.Printf(" %s_%v", vart.Name, vart.Id)
	// }
	// fmt.Printf("\n")
	bundle.Class = class
	bundle.allowedRegsMask = mask
	bundle.spillCost = spillCost / bundle.totalLength
	if mask == 0 {
		panic(fmt.Sprintf("value %s_%d has no allowable registers", vart.Name, vart.Id))
	}
	return true
}

// Variable ranges are found bottom up.  If the block ends with a
// jump we need to create ranges for its inputs but we do not have
// any immediate way of determining their register specs.  This
// class is used as a stand-in and is later ignored in favor of
// the actual class given by a primitive.

// This is an 'I don't know' register spec that allows a use to
// be recorded without specifying what its register class is.
// Used for jump inputs outputs, hence the name.
var jumpRegisterClass = &RegisterClassT{Name: "jump", Registers: nil}
var jumpRegUseSpec = &RegUseSpecT{Class: jumpRegisterClass, PhaseOffset: EarlyRegUse}

//----------------------------------------------------------------

type regBlockT struct {
	start      *CallNodeT
	end        *CallNodeT
	startIndex int // index of 'start' within the total call ordering
	callCount  int // number of calls in the block
	next       []*regBlockT
	previous   []*regBlockT
	isJump     bool
	loopDepth  int

	bound util.SetT[*VariableT] // bound within the block
	live  util.SetT[*VariableT] // live at block.start

	// Only in the blocks of procedure nodes.
	blocks     []*regBlockT // all the blocks in this procedure
	callsTo    util.SetT[*CallNodeT]
	calledFrom util.SetT[*CallNodeT]
	// All variables bound at some point in this procedure including
	// those bound in procedures it calls.
	boundDuring util.SetT[*VariableT]
}

func makeRegBlock() *regBlockT {
	return &regBlockT{bound: util.SetT[*VariableT]{}, live: util.SetT[*VariableT]{}}
}

// Finds the bound and live variables in the block.

func (block *regBlockT) initialize(start *CallNodeT, end *CallNodeT) {
	block.start = start
	block.end = end
	block.isJump = start.CallType != CallExit
	if start.CallType == ProcLambda {
		block.callsTo = util.NewSet[*CallNodeT]()
		block.calledFrom = util.NewSet[*CallNodeT]()
		block.boundDuring = util.NewSet[*VariableT]()
	}
	call := start
	count := 1
	for {
		inputs, outputs := call.Primop.RegisterUsage(call)
		if outputs != nil {
			if len(outputs) != len(call.Outputs) {
				panic(fmt.Sprintf("Primop %s returned %d output registers but has %d outputs.",
					call.Primop.Name(), len(outputs), len(call.Outputs)))
			}
			for i, vart := range call.Outputs {
				if outputs[i] != nil {
					block.bound.Add(vart)
				} else if 0 < len(vart.Refs) {
					panic(fmt.Sprintf("output %d of %s has nil register spec\n", i, call))
				}
			}
		}
		if inputs != nil {
			if len(inputs) != len(call.Inputs) {
				panic(fmt.Sprintf("Primop %s returned %d input registers but has %d inputs.",
					call.Primop.Name(), len(inputs), len(call.Inputs)))
			}
			for i, input := range inputs {
				vart := call.InputVariable(i)
				if input != nil && vart != nil {
					block.live.Add(vart)
				}
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
	random = rand.New(rand.NewSource(0))
	makeVarsForLiterals()
	procs := []*CallNodeT{}
	top.SetFlag(1)
	for lambda := range Lambdas {
		if lambda.CallType == ProcLambda && markedAncestor(lambda) != nil {
			Push(&procs, lambda)
			lambda.SetFlag(1)
			bbs := FindBasicBlocks[*regBlockT](lambda, makeRegBlock)
			lambda.Block.(*regBlockT).blocks = bbs
		}
	}
	sort.Slice(procs, func(i int, j int) bool {
		return procs[i].Id < procs[j].Id
	})

	// Find which proc calls which others.
	for _, lambda := range procs {
		if lambda != top {
			for _, ref := range lambdaBinding(lambda).Refs {
				caller := markedAncestor(ref).(*CallNodeT)
				caller.Block.(*regBlockT).callsTo.Add(lambda)
				lambda.Block.(*regBlockT).calledFrom.Add(caller)
			}
		}
	}
	for _, lambda := range procs {
		lambda.SetFlag(0)
		findBoundDuring(lambda)
	}

	// Recursion requires dividing registers into caller saves and
	// callee saves.  A problem for another day.
	components := util.StronglyConnectedComponents(procs,
		func(proc *CallNodeT) []*CallNodeT { return proc.Block.(*regBlockT).callsTo.Members() })
	// Taking the components in order means that a procedure's call sites
	// will be processed before the procedure is.
	for _, comp := range components {
		if len(comp) != 1 {
			panic("Register allocation found recursion - time to write more code.")
		}
		setLoopDepths(comp[0])
	}

	blocks := []*regBlockT{}
	for _, proc := range procs {
		blocks = append(blocks, proc.Block.(*regBlockT).blocks...)
	}

	/*
		fmt.Printf("procs")
		for _, comp := range components {
			sep := "["
			for _, lambda := range comp {
				fmt.Printf("%s%s_%d", sep, lambda.Name, lambda.Id)
				sep = " "
			}
			fmt.Printf("]")
		}
		fmt.Printf("\n")
	*/

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
	procIndex := len(procs) - 1
	for i := len(blocks) - 1; 0 <= i; i-- {
		//fmt.Printf(" %s_%d block %d\n", procs[procIndex].Name, procs[procIndex].Id, i)
		findLiveRanges(blocks[i].start, &allVars)
		if blocks[i].start == procs[procIndex] {
			procIndex -= 1
		}
	}
	vars := allVars.Members()
	// Sort the variables to get deterministic behavior.
	sort.Slice(vars, func(i int, j int) bool {
		return vars[i].Id < vars[j].Id
	})

	valueQueue := QueueT[*valueT]{}
	for _, vart := range vars {
		if vart.value.initialize() {
			valueQueue.Enqueue(vart.value)
		}
		/*
			fmt.Printf("ranges %s_%d", vart.Name, vart.Id)
			for _, interval := range vart.value.bundle.intervals {
				fmt.Printf(" %d:%d", interval.start, interval.end)
			}
			fmt.Printf("\n")
		*/
	}

	// Merge values across jumps where possible.
	for _, block := range blocks {
		if block.isJump {
			findJumpConnections(block)
		}
	}

	// Get the bundles
	bundleQueue := util.MakePriorityQueue[*bundleT](
		func(x, y *bundleT) bool { return x.totalLength < y.totalLength })
	for !valueQueue.Empty() {
		value := valueQueue.Dequeue()
		if value.bundle != nil {
			bundleQueue.Enqueue(value.bundle)
		}
	}

	regLiveRanges := map[RegisterT]*liveRangeT{}
	for !bundleQueue.Empty() {
		bundle := bundleQueue.Dequeue()
		mask := bundle.allowedRegsMask
		if mask == 0 {
			panic("no allowed registers")
		}
		i := startBit(mask)
		conflictPoint := 0
		var conflictBundles util.SetT[*bundleT]
		minMaxSpillCost := math.MaxInt
		var spillReg RegisterT
		for {
			reg := bundle.Class.Registers[i]
			regLiveRange := regLiveRanges[reg]
			if regLiveRange == nil {
				regLiveRange = &liveRangeT{}
			}
			point, bundles, maxSpillCost := findConflict(regLiveRange, &bundle.liveRange, minMaxSpillCost)
			if point == -1 { // no conflict
				bundle.Register = reg
				regLiveRanges[reg] = regLiveRange.union(&bundle.liveRange)
				break
			} else if 0 < maxSpillCost { // smaller maxSpillCost
				conflictPoint = point
				conflictBundles = bundles
				minMaxSpillCost = maxSpillCost
				spillReg = reg
			}
			mask ^= 1 << i
			if mask == 0 {
				break
			}
			i = nextBit(mask, i)
		}
		if mask == 0 {
			// While traversing we want to keep track of the best spill options:
			// Evict: reg, conflicting bundles, max spill cost of conflicting bundles
			// Split: reg, first conflicting use, max spill cost of conflicting bundles
			// mask := bundle.allowedRegsMask
			fmt.Printf("failed to allocate register for")
			for _, vart := range bundle.value.vars.Members() {
				fmt.Printf(" %s", vart)
			}
			fmt.Printf("\n")
			for _, interval := range bundle.liveRange.intervals {
				fmt.Printf(" %d-%d", interval.start, interval.end)
			}
			fmt.Printf("\n")
			fmt.Printf("conflict point %d bundle count %d spill cost %d our cost %d\n",
				conflictPoint, len(conflictBundles), minMaxSpillCost, bundle.spillCost)
			if minMaxSpillCost < bundle.spillCost {
				regLiveRange := regLiveRanges[spillReg]
				slices.DeleteFunc(
					regLiveRange.intervals,
					func(interval intervalT) bool {
						return conflictBundles.Contains(interval.bundle)
					})
				for bundle := range conflictBundles {
					bundleQueue.Enqueue(bundle)
				}
				bundle.Register = spillReg
				regLiveRanges[spillReg] = regLiveRange.union(&bundle.liveRange)
			} else {
				/*
					for i := range 64 {
						if ((1 << i) & mask) != 0 {
							reg := bundle.Class.Registers[i]
							regLiveRange := regLiveRanges[reg]
							conflict := regLiveRange.conflicting(&bundle.liveRange)
							fmt.Printf("  %s: %s %d-%d\n", reg, conflict.bundle.value.vars.Members()[0], conflict.start, conflict.end)
						}
					}
				*/
				// Splitting
				// Make a new bundle that is everything after the split point.
				// Partition the uses.
				// Is that it?

				// splitting will go here
				panic(fmt.Sprintf("failed to allocate register for %s", bundle.value.vars.Members()[0]))
			}
		}
	}

	for _, vart := range vars {
		vart.Register = vart.value.bundle.Register
	}
}

// Check if bundleRange conflicts with regRange.  If not, then the bundle
// can be assigned the register.  If there is a conflict this returns:
//  - the index of the location of the first conflict
//  - the set of conflicting bundles that use the register
//  - the maximum spill cost of the conflicting bundles
// If a conflicting bundle is found whose spill cost is greater than
// 'minMaxSpillCost' this quits early, as a register with a cheaper
// spill cost has already been found.

func findConflict(
	regRange *liveRangeT,
	bundleRange *liveRangeT,
	minMaxSpillCost int) (int, util.SetT[*bundleT], int) {

	reg := regRange.intervals
	bundle := bundleRange.intervals
	firstConflict := -1
	bundles := util.NewSet[*bundleT]()
	maxSpillCost := 0
	i := 0
	j := 0
	for i < len(reg) && j < len(bundle) {
		if reg[i].end <= bundle[j].start {
			i += 1
		} else if bundle[j].end <= reg[i].start {
			j += 1
		} else {
			if firstConflict == -1 {
				firstConflict = max(reg[i].start, bundle[j].start)
			}
			conflictBundle := reg[i].bundle
			bundleSpillCost := conflictBundle.spillCost
			if maxSpillCost < bundleSpillCost {
				if minMaxSpillCost < bundleSpillCost {
					return 1, nil, 0 // we can't beat the current best
				}
				maxSpillCost = bundleSpillCost
			}
			bundles.Add(conflictBundle)
			if reg[i].end <= bundle[j].end {
				i += 1
			} else {
				j += 1
			}
		}
	}
	return firstConflict, bundles, maxSpillCost
}

// Start each register search with a register chosen at random.
var random = rand.New(rand.NewSource(0))

func startBit(mask uint64) int {
	index := random.Intn(bits.OnesCount64(mask))
	bit := 0
	for {
		if mask&1 == 1 {
			if index == 0 {
				break
			}
			index -= 1
		}
		mask >>= 1
		bit += 1
	}
	return bit
}

func nextBit(mask uint64, bit int) int {
	bit += 1
	temp := mask >> bit
	for {
		if temp == 0 {
			temp = mask
			bit = 0
		}
		if temp&1 == 1 {
			break
		}
		temp >>= 1
		bit += 1
	}
	return bit
}

// 1. Collect all variables bound within the procedure.
// 2. Propagate the boundDuring set up the calledBy links.

func findBoundDuring(proc *CallNodeT) {
	block := proc.Block.(*regBlockT)
	bound := block.boundDuring
	for _, bb := range block.blocks {
		bound = bound.Union(bb.bound)
	}
	block.boundDuring = bound
	propagateBoundDuring(proc)
}

func propagateBoundDuring(proc *CallNodeT) {
	block := proc.Block.(*regBlockT)
	bound := block.boundDuring
	for caller := range block.calledFrom {
		callerBlock := caller.Block.(*regBlockT)
		before := callerBlock.boundDuring
		after := before.Union(bound)
		if len(before) < len(after) {
			callerBlock.boundDuring = after
			propagateBoundDuring(caller)
		}
	}
}

// First find the maximum loop depth of any call to 'lambda', then
// find its own loop structure, adding the call-site depth to all of
// its blocks.  The lambdas are processed top-down in the call tree,
// so all call sites will already have loop depths.

func setLoopDepths(lambda *CallNodeT) {
	callLoopDepth := 0
	if lambda.parent != nil {
		for _, ref := range lambdaBinding(lambda).Refs {
			block := ContainingBlock(ref).(*regBlockT)
			if callLoopDepth < block.loopDepth {
				callLoopDepth = block.loopDepth
			}
		}
	}
	block := lambda.Block.(*regBlockT)
	block.loopDepth = callLoopDepth
	FindLoopBlocks(
		block.blocks,
		func(block *regBlockT) []*regBlockT { return block.next },
		func(
			block *regBlockT,
			loopHeader *regBlockT,
			loopParent *regBlockT,
			loopDepth int) {

			block.loopDepth = callLoopDepth + loopDepth
		})
}

func findLiveRanges(top *CallNodeT, allVars *util.SetT[*VariableT]) {
	ends := map[*VariableT]int{}
	block := top.Block.(*regBlockT)
	startIndex := block.startIndex * 3             // early block.start
	endIndex := startIndex + block.callCount*3 - 1 // late block.end
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
		}
	}
	lateIndex := endIndex
	for call := block.end; ; call = call.parent {
		inputs, outputs := call.Primop.RegisterUsage(call)
		/*
			if outputs == nil {
				for i, vart := range call.Outputs {
					if vart != nil && 0 < len(vart.Refs) {
						fmt.Printf("output %d of %s has no register spec\n", i, call)
					}
				}
			}
		*/
		// fmt.Printf("call %d(%s) %d lateIndex %d\n",
		//     call.Id, call.Primop.Name(), len(call.Outputs), lateIndex)
		if outputs != nil {
			for i, vart := range call.Outputs {
				if outputs[i] != nil {
					end, found := ends[vart]
					if found {
						index := lateIndex + outputs[i].PhaseOffset
						vart.getValue().addDefinition(index, outputs[i], block.loopDepth)
						allVars.Add(vart)
						// +1 for inclusive -> exclusive
						vart.getValue().addInterval(index, end+1)
					}
				}
			}
		}
		if inputs != nil {
			for i, input := range call.Inputs {
				if inputs[i] == nil || input == nil {
					if false && input.NodeType() == ReferenceNode {
						fmt.Printf("input %d of %s has nil register spec\n", i, call)
					}
					continue
				}
				if IsReferenceNode(input) {
					vart := input.(*ReferenceNodeT).Variable
					index := lateIndex + inputs[i].PhaseOffset
					vart.getValue().addUse(index, inputs[i], block.loopDepth)
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
		calledProc := getCalledProc(call)
		if calledProc != nil {
			bound := calledProc.Block.(*regBlockT).boundDuring
			for vart := range bound {
				vart.getValue().addInterval(lateIndex+MiddleRegUse, lateIndex+MiddleRegUse)
			}
		}
		lateIndex -= 3
		if call == block.start {
			break
		}
	}
	for _, vart := range block.live.Members() {
		end, found := ends[vart]
		if found {
			// +1 for inclusive -> exclusive
			vart.getValue().addInterval(startIndex, end+1)
		} else {
			panic(fmt.Sprintf("live variable has no end point %s\n", vart))
		}
	}
}

func getCalledProc(call *CallNodeT) *CallNodeT {
	switch primop := call.Primop.(type) {
	case CallsProcPrimopT:
		return primop.CalledProc(call)
	default:
		return nil
	}
}

// Merge values across jumps where possible.

func findJumpConnections(block *regBlockT) {
	vars := block.start.Outputs
	for _, prev := range block.previous {
		jump := prev.end
		for i, vart := range vars {
			if !IsReferenceNode(jump.Inputs[i+1]) {
				continue
			}
			other := jump.Inputs[i+1].(*ReferenceNodeT).Variable
			if vart.value != other.value {
				checkJumpConnection(vart, other)
			}
		}
	}
}

// 'vart' is passed the value of 'other' at a jump.  Merge there
// values if they do not conflict.

func checkJumpConnection(vart *VariableT, other *VariableT) {
	if other.value == nil {
		panic(fmt.Sprintf("jump connection has no value %s_%d", other.Name, other.Id))
	}
	if other.value.bundle == nil {
		panic(fmt.Sprintf("jump connection value has no bundle %s_%d", other.Name, other.Id))
	}
	if !(vart.value.bundle.Class == nil ||
		other.value.bundle.Class == nil ||
		vart.value.bundle.Class == other.value.bundle.Class) {

		panic(fmt.Sprintf("jump connection value bundle has no class %s_%d", other.Name, other.Id))
	}
	if !vart.value.bundle.liveRange.conflicts(&other.value.bundle.liveRange) {
		// fmt.Printf("jump connect %s_%d %s_%d\n", vart.Name, vart.Id, other.Name, other.Id)
		vart.value.join(other.value)
	}
}
