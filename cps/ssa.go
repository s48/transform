// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Remove cells by converting to SSA form.

package cps

import (
	"fmt"
	"slices"

	"github.com/s48/transform/util"
)

// This relies on all lambdas being bound at the least common
// ancestor of their references.

type cellBlockT struct {
	start    *CallNodeT
	end      *CallNodeT
	next     []*cellBlockT
	previous []*cellBlockT
	children []*cellBlockT // lexical children

	// variables bound to cells
	written util.SetT[*VariableT] // any cellSet
	read    util.SetT[*VariableT] // cellRef found before cellSet in this block
	live    util.SetT[*VariableT] // cellRef found before cellSet here or later

	// classic SSA values
	dominator  *cellBlockT
	dominatees []*cellBlockT
	frontier   util.SetT[*cellBlockT]
	phiVars    []*VariableT // cell vars whose values will be passed in

	lastVar *VariableT // phase marker that we don't have to clear
	queued  bool       // todo-queue flag
}

func SimplifyCells(top *CallNodeT) {
	blocks := FindBasicBlocks[*cellBlockT](top, makeCellBlock)

	// The blocks containing the setVars for each cellVar.
	varSetBlocks := map[*VariableT][]*cellBlockT{}

	// Set the .read and .written fields of each block and initialize
	// the .live fields to be the same as .read.
	for _, block := range blocks {
		findCellVars(block, varSetBlocks)
	}
	propagateLive(blocks) // transitive closure of the .live sets
	findDominators(blocks[0],
		func(b *cellBlockT) []*cellBlockT { return b.next },
		func(b *cellBlockT, d *cellBlockT) {
			b.dominator = d
			Push(&d.dominatees, b)
		})
	findDominanceFrontiers(blocks,
		func(b *cellBlockT) []*cellBlockT { return b.previous },
		func(b *cellBlockT) *cellBlockT { return b.dominator },
		func(b *cellBlockT) *util.SetT[*cellBlockT] { return &b.frontier })
	for vart, blocks := range varSetBlocks {
		findPhiLocations(vart, blocks)
	}
	// Move all jump bindings to the end of their dominators.
	for _, block := range blocks {
		bindDominatees(block)
	}
	// for _, block := range blocks {
	//    printBlockVars(block)
	// }
	simplifyBlockCells(blocks[0], nil)
}

func findCellVars(block *cellBlockT, varSetBlocks map[*VariableT][]*cellBlockT) {
	call := block.start
	for {
		if call.Primop.Name() == "cellSet" {
			cellVar := call.Inputs[0].(*ReferenceNodeT).Variable
			if !block.written.Contains(cellVar) {
				block.written.Add(cellVar)
				varSetBlocks[cellVar] = append(varSetBlocks[cellVar], block)
			}
		} else if call.Primop.Name() == "cellRef" {
			cellVar := call.Inputs[0].(*ReferenceNodeT).Variable
			if !block.written.Contains(cellVar) {
				block.read.Add(cellVar)
				block.live.Add(cellVar)
			}
		}
		if call == block.end {
			break
		} else {
			call = call.Next[0]
		}
	}
}

// Transitive closure of the .live fields.
func propagateLive(blocks []*cellBlockT) {
	todo := &QueueT[*cellBlockT]{}
	for _, block := range blocks {
		todo.Enqueue(block)
		block.queued = true
	}
	for !todo.Empty() {
		block := todo.Dequeue()
		block.queued = false
		for _, prev := range block.previous {
			before := len(prev.live)
			// If we had a separate 'add' set we could delay the 'Difference'
			// call util 'prev' is dequeued.
			prev.live = prev.live.Union(block.live.Difference(prev.written))
			if !prev.queued && before < len(prev.live) {
				todo.Enqueue(prev)
				prev.queued = true
			}
		}
	}
}

// Transitively find all of the blocks where 'cellVar' is live
// and the block is in the dominance frontier of a block that
// either sets 'cellvar' or receives it as phi value.

func findPhiLocations(cellVar *VariableT, setBlocks []*cellBlockT) {
	todo := QueueT[*cellBlockT]{}
	for _, block := range setBlocks {
		todo.Enqueue(block)
		block.queued = true
	}
	for !todo.Empty() {
		block := todo.Dequeue()
		block.queued = false
		for _, front := range block.frontier.Members() {
			if front.live.Contains(cellVar) && front.lastVar != cellVar {
				Push(&front.phiVars, cellVar)
				front.lastVar = cellVar
				if !front.queued {
					todo.Enqueue(front)
				}
			}
		}
	}
}

//----------------------------------------------------------------
// Move the bindings of jump lambdas to the end of the block
// that dominates them.  This makes everything in the dominator
// lexically visible in the jump lambda.  The contents of cells
// in the dominator can be accessed in the jump lambda without
// needing to be passed in as a phi argument.

func bindDominatees(block *cellBlockT) {
	vars := []*VariableT{}
	vals := []*CallNodeT{}
	for _, child := range block.dominatees {
		if child.start.CallType == JumpLambda {
			Push(&vals, child.start)
			Push(&vars, lambdaBinding(child.start))
		}
	}
	if len(vars) == 0 {
		return
	}
	call := block.end.parent
	if !(call.Primop.Name() == "let" || call.Primop.Name() == "letrec") {
		call = MakeCall(LookupPrimop("letrec"), []*VariableT{})
		InsertCallParent(block.end, call)
	}
	for i, vart := range vars {
		if vart.Binder == call {
			continue // already bound in the right place
		}
		val := vals[i]
		unbindLambda(val)
		Push(&call.Inputs, nil)
		AttachInput(call, len(call.Outputs), val)
		Push(&call.Outputs, vart)
		vart.Binder = call
	}
}

//----------------------------------------------------------------
// Remove all CellSet calls, replace CellRef calls with values, and
// add phi variables and arguments.

type CellValuesT struct {
	parent *CellValuesT
	values map[*VariableT]*VariableT
}

func makeCellValues(parent *CellValuesT) *CellValuesT {
	return &CellValuesT{parent: parent, values: map[*VariableT]*VariableT{}}
}

func (env *CellValuesT) lookup(cellVar *VariableT) *VariableT {
	for ; env != nil; env = env.parent {
		value := env.values[cellVar]
		if value != nil {
			return value
		}
	}
	panic(fmt.Sprintf("no value for cell variable %s_%d", cellVar.Name, cellVar.Id))
}

func (env *CellValuesT) setValue(cellVar *VariableT, value *VariableT) {
	env.values[cellVar] = value
}

func simplifyBlockCells(block *cellBlockT, values *CellValuesT) {
	values = makeCellValues(values)

	start := block.start
	for _, cellVar := range block.phiVars {
		phiVar := MakeVariable(cellVar.Name, cellVar.Type)
		phiVar.Binder = start
		start.Outputs = append(start.Outputs, phiVar)
		values.setValue(cellVar, phiVar)
	}

	// Add new vars for phiVars to the start, adding to map
	call := start
	for {
		if call.Primop.Name() == "cellSet" {
			cellVar := call.Inputs[0].(*ReferenceNodeT).Variable
			values.setValue(cellVar, replaceCellSet(call))
		} else if call.Primop.Name() == "cellRef" {
			cellVar := call.Inputs[0].(*ReferenceNodeT).Variable
			replaceCellRef(call, values.lookup(cellVar))
		}
		if call == block.end {
			break
		} else {
			call = call.Next[0]
		}
	}
	if call.Primop.Name() == "jump" {
		phiVars := block.next[0].phiVars // there can be only one next block
		start := len(call.Inputs)
		call.Inputs = append(call.Inputs, make([]NodeT, len(phiVars))...)
		for i, phiVar := range phiVars {
			AttachInput(call, start+i, MakeReferenceNode(values.lookup(phiVar)))
		}
		MarkChanged(call)
	}
	for _, child := range block.dominatees {
		if child != block {
			simplifyBlockCells(child, values)
		}
	}
}

//----------------------------------------------------------------
// Cooper, Keith D.; Harvey, Timothy J; Kennedy, Ken (2001).
// "A Simple, Fast Dominance Algorithm"

func findDominators[T comparable](rootNode T, succ func(T) []T, setResult func(T, T)) {
	nodes := []T{}
	indexes := map[T]int{}
	var findNodes func(node T)
	findNodes = func(node T) {
		Push(&nodes, node)
		indexes[node] = 1 // just a placeholder
		for _, child := range succ(node) {
			if indexes[child] == 0 {
				findNodes(child)
			}
		}
	}
	findNodes(rootNode)
	slices.Reverse(nodes) // preorder -> postorder
	for i, node := range nodes {
		indexes[node] = i
	}
	predecessors := map[int][]int{}
	// Walk the nodes in preorder so that the predecessors are
	// in the right order for the algorithm (a node's first predecessor
	// must be before it the preorder).
	for i := len(nodes) - 1; 0 <= i; i-- {
		node := nodes[i]
		for _, successor := range succ(node) {
			index := indexes[successor]
			predecessors[index] = append(predecessors[index], i)
		}
	}
	// Nodes are indexed postorder, so the start node has the highest index.
	root := len(nodes) - 1
	doms := make([]int, len(nodes))
	for i := range doms {
		doms[i] = -1
	}
	doms[root] = root
	changed := true
	for changed {
		changed = false
		for i := root - 1; 0 <= i; i-- {
			newIdom := predecessors[i][0]
			for _, other := range predecessors[i][1:] {
				if doms[other] != -1 {
					for other != newIdom {
						for other < newIdom {
							other = doms[other]
						}
						for newIdom < other {
							newIdom = doms[newIdom]
						}
					}
				}
			}
			if doms[i] != newIdom {
				doms[i] = newIdom
				changed = true
			}
		}
	}
	for i, node := range nodes {
		setResult(node, nodes[doms[i]])
	}
}

func findDominanceFrontiers[T comparable](blocks []T,
	preds func(T) []T,
	dom func(T) T,

	frontier func(T) *util.SetT[T]) {
	for _, block := range blocks {
		if len(preds(block)) < 2 {
			continue
		}
		for _, pred := range preds(block) {
			runner := pred
			for runner != dom(block) {
				frontier(runner).Add(block)
				runner = dom(runner)
			}
		}
	}
}

//----------------------------------------------------------------
// cellBlockT methods

func makeCellBlock() *cellBlockT {
	return &cellBlockT{frontier: util.SetT[*cellBlockT]{},
		read:    util.SetT[*VariableT]{},
		written: util.SetT[*VariableT]{},
		live:    util.SetT[*VariableT]{}}
}

func (block *cellBlockT) initialize(start *CallNodeT, end *CallNodeT) {
	block.start = start
	block.end = end
	if start.parent != nil {
		call := start.parent
		for call.Block == nil {
			call = call.parent
		}
		Push(&call.Block.(*cellBlockT).children, block)
	}
}

func (block *cellBlockT) addNext(rawNext BasicBlockT) {
	next := rawNext.(*cellBlockT)
	block.next = append(block.next, next)
	next.previous = append(next.previous, block)
}

func (block *cellBlockT) getEnd() *CallNodeT {
	return block.end
}

func printBlockVars(block *cellBlockT) {
	fmt.Printf("%s_%d: dom %s_%d frontier",
		block.start.Name, block.start.Id,
		block.dominator.start.Name, block.dominator.start.Id)
	for block, _ := range block.frontier {
		fmt.Printf(" %s_%d", block.start.Name, block.start.Id)
	}
	fmt.Printf("\n")
	printVarSet := func(tag string, vars util.SetT[*VariableT]) {
		fmt.Printf("  %s:", tag)
		for vart, _ := range vars {
			fmt.Printf(" %s_%d", vart.Name, vart.Id)
		}
		fmt.Printf("\n")
	}
	printVarSet("read", block.read)
	printVarSet("written", block.written)
	printVarSet("live", block.live)
	fmt.Printf("  phi:")
	for _, vart := range block.phiVars {
		fmt.Printf(" %s_%d", vart.Name, vart.Id)
	}
	fmt.Printf("\n")
}

func printVars(tag string, vars *util.SetT[*VariableT]) {
	fmt.Printf("%s", tag)
	for _, vart := range vars.Members() {
		fmt.Printf(" %s_%d", vart.Name, vart.Id)
	}
	fmt.Printf("\n")
}
