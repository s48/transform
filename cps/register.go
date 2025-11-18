// Copyright 2025 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Register allocation version 2.
// This uses a typical graph-coloring algorithm.
//
// Register spilling is not yet implemented.
//
// Helpful papers:
// - Register Allocation for Programs in SSA-Form; Sebastian Hack,
//   Daniel Grund, and Gerhard Goos.
// - An Optimal Linear-Time Algorithm for Interprocedural Register
//   Allocation in High Level Synthesis Using SSA Form; Philip Brisk,
//   Ajay K. Verma, and Paolo Ienne
//
// Each procedure gets allocated separately, with callees done before
// callers.  Registers are allocated from lowest to highest and we
// record the number of registers needed for each procedure.  A value
// that is live across a procedure call has to be allocated a register
// number greater than the number used by the called procedure.
//
// The live-range code is based on Cranelift's register allocator.
//   https://cfallin.org/blog/2022/06/09/cranelift-regalloc2/
//   https://github.com/bytecodealliance/regalloc2/blob/main/doc/ION.md
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
	"math/big"
	"slices"
	"sort"
	"strings"

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
// the union of the variables' bundles.

// The orignal calls this a "spill set".
type valueT struct {
	vars   util.SetT[*VariableT]
	bundle *bundleT
}

func (vart *VariableT) getValue() *valueT {
	if vart.value == nil {
		value := &valueT{vars: util.NewSet(vart)}
		value.bundle = &bundleT{
			value:     value,
			conflicts: util.NewSet[*bundleT]()}
		vart.value = value
	}
	return vart.value
}

// One use of a variable
type regUseT struct {
	spillCost int         // cost heuristic for spilling this use
	isWrite   bool        // true for outputs, false for inputs
	spec      RegUseSpecT // register constraints
	bundle    *bundleT    // the bundle this is in
}

const (
	EarlyRegUse  = -2
	MiddleRegUse = -1
	LateRegUse   = 0
)

type RegUseSpecT struct {
	PhaseOffset int // -2, -1, 0 for early, middle, and late use
	Class       *RegisterClassT
}

// A set of registers.
type RegisterClassT struct {
	Name string
	// These are initialized by SetRegisters.
	registers     []RegisterT // only those registers that can be allocated
	registerIndex map[RegisterT]int
}

func (class *RegisterClassT) SetRegisters(allRegisters []RegisterT, usableMask *big.Int) {
	registerIndex := map[RegisterT]int{}
	usable := []RegisterT{}
	for i, reg := range allRegisters {
		reg.SetClass(class)
		if usableMask.Bit(i) == 1 {
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

type RegisterT interface {
	SetClass(*RegisterClassT) // for initialization
	Class() *RegisterClassT
	String() string
	Number() int
}

// A single register allocation with the live range for which the
// allocation is valid.
type bundleT struct {
	value     *valueT
	class     *RegisterClassT
	uses      []*regUseT
	liveRange liveRangeT

	conflicts    util.SetT[*bundleT]
	numConflicts int       // number of uncolored conflicts
	minReg       int       // number of registers reserved for calls made during liveRange
	Register     RegisterT // what gets assigned to this
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
	for _, use := range other.uses {
		use.bundle = bundle
	}
	other.uses = nil
	bundle.liveRange = *bundle.liveRange.union(&other.liveRange)
}

func (bundle *bundleT) initialize() bool {
	vart := bundle.value.vars.Members()[0] // for error messages
	var class *RegisterClassT
	for _, use := range bundle.uses {
		use.bundle = bundle
		if use.spec.Class == jumpRegUseSpec.Class {
			continue
		}
		if use.spec.Class == nil {
			panic("use has no class")
		}
		if class == nil {
			class = use.spec.Class
		} else if use.spec.Class != class {
			panic(fmt.Sprintf("value %s has two register classes %s and %s (from call %s)",
				vart, use.spec.Class.Name, class.Name, vart.Binder))
		}
	}
	if class == nil {
		return false
	}
	// fmt.Printf("value class %s", class.Name)
	// for vart, _ := range value.vars {
	//		fmt.Printf(" %s_%v", vart.Name, vart.Id)
	// }
	// fmt.Printf("\n")
	bundle.class = class
	return true
}

// Returns the vector of live bundle sets for the bundle's register class.
func (bundle *bundleT) liveBundles() []util.SetT[*bundleT] {
	result := liveBundles[bundle.class]
	if result == nil {
		result = make([]util.SetT[*bundleT], numProgramPoints)
		for i := range result {
			result[i] = util.NewSet[*bundleT]()
		}
		liveBundles[bundle.class] = result
	}
	return result
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

func (value *valueT) addDefinition(vart *VariableT, index int, spec *RegUseSpecT, block *regBlockT) {
	regUse := value.makeUse(index, spec)
	regUse.isWrite = true
	regUse.spillCost = 1<<(min(block.loopDepth, 10)*2)*1000 + 2000
	outputRegUses[vart] = regUse
}

func (value *valueT) addUse(node *ReferenceNodeT, index int, spec *RegUseSpecT, block *regBlockT) {
	regUse := value.makeUse(index, spec)
	regUse.spillCost = (1 << (min(block.loopDepth, 10) * 2)) * 1000
	inputRegUses[node] = regUse
}

func (value *valueT) makeUse(index int, spec *RegUseSpecT) *regUseT {
	regUse := &regUseT{
		spec:   *spec,
		bundle: value.bundle}
	value.bundle.uses = append(value.bundle.uses, regUse)
	return regUse
}

func (value *valueT) addInterval(start int, end int) {
	if end < start {
		panic("addInterval: end is before start")
	}
	vart := value.vars.Members()[0] // there is only one at this point
	if end == 0 {
		panic(fmt.Sprintf("%s_%d has an interval ending at zero", vart.Name, vart.Id))
	}
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
// Returns false if no register needs to be allocated.

func (value *valueT) initialize() bool {
	bundle := value.bundle
	slices.Reverse(bundle.liveRange.intervals)
	if len(bundle.uses) == 0 {
		return false
	}
	return bundle.initialize()
}

// Variable ranges are found bottom up.  If the block ends with a
// jump we need to create ranges for its inputs but we do not have
// any immediate way of determining their register specs.  This
// class is used as a stand-in and is later ignored in favor of
// the actual class given by a primitive.
var jumpRegisterClass = &RegisterClassT{Name: "jump", registers: nil}
var jumpRegUseSpec = &RegUseSpecT{Class: jumpRegisterClass, PhaseOffset: EarlyRegUse}

//----------------------------------------------------------------

type regBlockT struct {
	start      *CallNodeT
	end        *CallNodeT
	startIndex int // index of 'start' within the total call ordering
	callCount  int // number of calls in the block
	next       []*regBlockT
	previous   []*regBlockT
	loopDepth  int
	callDepth  int
	seen       bool

	bound util.SetT[*VariableT] // bound within the block
	live  util.SetT[*VariableT] // live at block.start

	inputSpecs  [][]*RegUseSpecT // cached for each call in the block
	outputSpecs [][]*RegUseSpecT

	// Only in the blocks of procedure nodes.
	blocks     []*regBlockT // all the blocks in this procedure
	callsTo    util.SetT[*CallNodeT]
	calledFrom util.SetT[*CallNodeT]
	// How many registers of each class are used in this procedure.
	regCounts map[*RegisterClassT]int
}

func makeRegBlock() *regBlockT {
	return &regBlockT{
		bound: util.SetT[*VariableT]{},
		live:  util.SetT[*VariableT]{}}
}

// Finds the bound and live variables in the block.

func (block *regBlockT) initialize(start *CallNodeT, end *CallNodeT) {
	block.start = start
	block.end = end
	if start.CallType == ProcLambda {
		block.callsTo = util.NewSet[*CallNodeT]()
		block.calledFrom = util.NewSet[*CallNodeT]()
		block.regCounts = map[*RegisterClassT]int{}
	}
	for call := start; ; call = call.Next[0] {
		inputs, outputs := call.Primop.RegisterUsage(call)
		block.inputSpecs = append(block.inputSpecs, inputs)
		block.outputSpecs = append(block.outputSpecs, outputs)

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
	}
	for vart, _ := range block.bound {
		block.live.Remove(vart)
	}
	block.callCount = len(block.inputSpecs)
}

func (block *regBlockT) addNext(rawNext BasicBlockT) {
	next := rawNext.(*regBlockT)
	block.next = append(block.next, next)
	next.previous = append(next.previous, block)
}

func (block *regBlockT) getEnd() *CallNodeT {
	return block.end
}

// This includes early, middle, and late points for each CPS call in
// the program.  Equal to three times the number of CPS calls.
var numProgramPoints int

// For each register class this has the set of live bundles at each
// program point.
var liveBundles map[*RegisterClassT][]util.SetT[*bundleT]

// The procedure called, if any, at each program point.
var procCalls []*regBlockT

func AllocateRegisters(top *CallNodeT) {
	makeVarsForLiterals()
	regLinkInit()
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

	// Recursion requires dividing registers into caller saves and
	// callee saves.  A problem for another day.
	components := util.StronglyConnectedComponents(procs,
		func(proc *CallNodeT) []*CallNodeT { return proc.Block.(*regBlockT).callsTo.Members() })
	// Taking the components in reverse order means that a procedure's
	// call sites will be processed after the procedure is.
	slices.Reverse(components)

	for i, comp := range components {
		// fmt.Printf("component %s\n", comp[0].Block.(*regBlockT).start)
		if len(comp) != 1 {
			panic("Register allocation found recursion - time to write more code.")
		}
		setLoopDepths(comp[0], i)
	}

	blocks := []*regBlockT{}
	for _, proc := range procs {
		todo := util.StackT[*regBlockT]{}
		todo.Push(proc.Block.(*regBlockT))
		for 0 < todo.Len() {
			block := todo.Pop()
			if !block.seen {
				block.seen = true
				blocks = append(blocks, block)
				temp := slices.Clone(block.next)
				// Use stable sort to stay deterministic.
				sort.SliceStable(temp, func(i int, j int) bool {
					return temp[i].loopDepth < temp[j].loopDepth
				})
				for _, next := range temp {
					todo.Push(next)
				}
			}
		}
	}

	index := 0
	for _, block := range blocks {
		block.startIndex = index
		index += block.callCount
	}

	liveBundles = map[*RegisterClassT][]util.SetT[*bundleT]{}
	numProgramPoints = index * 3
	procCalls = make([]*regBlockT, numProgramPoints)

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

	count := 0
	valueQueue := QueueT[*valueT]{}
	for _, vart := range vars {
		if vart.value.initialize() {
			valueQueue.Enqueue(vart.value)
			count += 1
		}
		/*
			fmt.Printf("ranges %s_%d", vart.Name, vart.Id)
			for _, interval := range vart.value.bundle.liveRange.intervals {
				fmt.Printf(" %d:%d", interval.start, interval.end)
			}
			fmt.Printf("\n")
		*/
	}

	checkLinks()

	bundles := []*bundleT{}

	// Add bundles to the liveBundle sets where they are live.
	for !valueQueue.Empty() {
		value := valueQueue.Dequeue()
		if value.bundle != nil {
			bundle := value.bundle
			bundles = append(bundles, bundle)
			liveBundles := bundle.liveBundles()
			for _, interval := range bundle.liveRange.intervals {
				for i := interval.start; i < interval.end; i++ {
					liveBundles[i].Add(bundle)
				}
			}
		}
	}

	// Get the conflicts for each bundle.
	for _, bundle := range bundles {
		liveBundles := bundle.liveBundles()
		for _, interval := range bundle.liveRange.intervals {
			for i := interval.start; i < interval.end; i++ {
				bundle.conflicts = bundle.conflicts.Union(liveBundles[i])
			}
		}
		bundle.conflicts.Remove(bundle)
	}

	// Determine the number of registers of each class that procedures require.
	for regClass, bundles := range liveBundles {
		regCount := len(regClass.registers)
		for _, comp := range components {
			maxClique := 0
			procBlock := comp[0].Block.(*regBlockT)
			for _, block := range procBlock.blocks {
				start := block.startIndex * 3
				for i := range block.callCount * 3 {
					index := start + i
					cliqueSize := len(bundles[index])
					if procCalls[index] != nil {
						callerSaves := procCalls[index].regCounts[regClass]
						cliqueSize += callerSaves
						for bundle, _ := range bundles[index] {
							bundle.minReg = max(bundle.minReg, callerSaves)
						}
					}
					maxClique = max(maxClique, cliqueSize)
					if regCount <= cliqueSize {
						fmt.Printf("call %d has %d %s registers and %d bundles\n",
							index, regCount, regClass.Name, cliqueSize)
						for bundle, _ := range bundles[index] {
							fmt.Printf(" %s", bundle.value.vars.Members()[0])
						}
						fmt.Printf("\n")
						panic("ran out of registers")
					}
				}
			}
			procBlock.regCounts[regClass] = maxClique
		}
	}

	fmt.Printf("Register use:\n")
	maxName := 0
	for _, comp := range components {
		maxName = max(maxName, len(comp[0].Block.(*regBlockT).start.Name))
	}
	for _, comp := range components {
		block := comp[0].Block.(*regBlockT)
		padding := strings.Repeat(" ", maxName-len(block.start.Name))
		fmt.Printf("  %s %s", block.start.Name, padding)
		uses := []string{}
		for class, count := range block.regCounts {
			Push(&uses, fmt.Sprintf("%s:%d   ", class.Name, count)[:5])
		}
		slices.Sort(uses)
		fmt.Printf("%s\n", strings.Join(uses, " "))
	}

	coloringQueue := util.MakePriorityQueue[*bundleT](
		func(x, y *bundleT) bool { return y.numConflicts+y.minReg < x.numConflicts+x.minReg })

	for _, bundle := range bundles {
		liveBundles := bundle.liveBundles()
		for _, interval := range bundle.liveRange.intervals {
			for i := interval.start + 1; i < interval.end; i++ {
				bundle.conflicts = bundle.conflicts.Union(liveBundles[i])
			}
		}
		bundle.conflicts.Remove(bundle)
		bundle.numConflicts = len(bundle.conflicts)
		coloringQueue.Enqueue(bundle)
	}

	colorable := util.StackT[*bundleT]{}

	for !coloringQueue.Empty() {
		bundle := coloringQueue.Dequeue()
		if len(bundle.class.registers) <= bundle.numConflicts+bundle.minReg {
			panic(fmt.Sprintf("%s ran out of registers", bundle.value.vars.Members()[0]))
		}
		colorable.Push(bundle)
		for _, conflict := range bundle.conflicts.Members() {
			conflict.numConflicts -= 1
			coloringQueue.Update(bundle)
		}
	}

	for 0 < colorable.Len() {
		bundle := colorable.Pop()
		regClass := bundle.class
		// mask = (1 << bundle.minReg) - 1
		var mask big.Int
		mask.Sub(mask.Lsh(big.NewInt(1), uint(bundle.minReg)), big.NewInt(1))
		for _, conflict := range bundle.conflicts.Members() {
			reg := conflict.Register
			if reg != nil {
				mask.SetBit(&mask, regClass.registerIndex[reg], 1)
			}
		}
		mask.Not(&mask)
		if mask.BitLen() == 0 {
			panic("no register available")
		}
		regIndex := trailingZeros(&mask)
		bundle.Register = regClass.registers[regIndex]
		if bundle.Register == nil {
			panic(fmt.Sprintf("no register %d in class %s", regIndex, regClass.Name))
		}
	}

	for _, vart := range vars {
		vart.Register = vart.value.bundle.Register
	}
	regLinkInit() // we're done with this data
}

func trailingZeros(n *big.Int) int {
	for i := 0; i < n.BitLen(); i++ {
		if n.Bit(i) == 1 {
			return i
		}
	}
	return -1
}

// First find the maximum loop depth of any call to 'lambda', then
// find its own loop structure, adding the call-site depth to all of
// its blocks.  The lambdas are processed top-down in the call tree,
// so all call sites will already have loop depths.

func setLoopDepths(lambda *CallNodeT, callDepth int) {
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
	block.callDepth = callDepth
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
	i := block.callCount
	for call := block.end; ; call = call.parent {
		i -= 1
		inputs := block.inputSpecs[i]
		outputs := block.outputSpecs[i]
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
						vart.getValue().addDefinition(vart, index, outputs[i], block)
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
					node := input.(*ReferenceNodeT)
					vart := node.Variable
					index := lateIndex + inputs[i].PhaseOffset
					vart.getValue().addUse(node, index, inputs[i], block)
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
			procCalls[lateIndex-1] = calledProc.Block.(*regBlockT)
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

//----------------------------------------------------------------
// This mechanism allows primops to indicate that putting a pair of
// bundles in the same register would eliminate a move instruction.
// The linking happens before all bundles are created so we cache the
// linked node and variable and only connect the bundles once they
// have all been created.

type regLinkT struct {
	from      *ReferenceNodeT
	to        *VariableT
	spillCost int
}

var inputRegUses map[*ReferenceNodeT]*regUseT
var outputRegUses map[*VariableT]*regUseT
var regLinks []*regLinkT

func regLinkInit() {
	inputRegUses = map[*ReferenceNodeT]*regUseT{}
	outputRegUses = map[*VariableT]*regUseT{}
	regLinks = nil
}

// Primops can implement this.
type RegisterLinkerT interface {
	LinkRegisters(call *CallNodeT)
}

func AddRegisterLink(vart *VariableT, rawNode NodeT) {
	switch node := rawNode.(type) {
	case *ReferenceNodeT:
		// fmt.Printf("linking %s and %s\n", node.Variable, vart)
		regLinks = append(regLinks, &regLinkT{node, vart, 0})
	}
}

func checkLinks() {
	missing := 0
	for _, regLink := range regLinks {
		refUse := inputRegUses[regLink.from]
		if refUse != nil {
			regLink.spillCost = refUse.spillCost
		} else {
			missing += 1
		}
	}
	sort.SliceStable(regLinks, func(i, j int) bool {
		// Process higher spill costs first and otherwise use tiebreakers
		// to keep everything deterministic.
		x := regLinks[i]
		y := regLinks[j]
		if x.spillCost != y.spillCost {
			return y.spillCost < x.spillCost
		} else if x.to.Id != y.to.Id {
			return x.to.Id < y.to.Id
		} else {
			return x.from.Variable.Id < y.from.Variable.Id
		}
	})
	for _, regLink := range regLinks {
		node := regLink.from
		vart := regLink.to
		refUse := inputRegUses[node]
		defUse := outputRegUses[vart]
		if defUse == nil || refUse == nil {
			continue
		}
		if !(defUse.bundle.class == nil ||
			refUse.bundle.class == nil ||
			defUse.bundle.class == refUse.bundle.class) {

			panic(fmt.Sprintf("linking registers with different classes: %s and %s",
				vart, node.Variable))
		}
		bundleA := refUse.bundle
		bundleB := defUse.bundle
		if !bundleA.liveRange.conflicts(&bundleB.liveRange) {
			// fmt.Printf("linking %s and %s\n", vart, node.Variable)
			bundleA.value.join(bundleB.value)
		}
	}
}

// Called by the jump primop's RegisterUsage method.
func LinkJumpRegisters(call *CallNodeT) {
	target := CalledLambda(call)
	for i, vart := range target.Outputs {
		AddRegisterLink(vart, call.Inputs[i+1])
	}
}

// Ditto for procedure calls.  Disabled until we figure out how to
// use this.
func LinkCallRegisters(call *CallNodeT) {
	return
	target := CalledLambda(call)
	for i, vart := range target.Outputs[2:] {
		AddRegisterLink(vart, call.Inputs[i+2])
	}
}
