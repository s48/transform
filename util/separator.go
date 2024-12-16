// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Find the separators of a graph, which are the nodes that, if
// removed, separate the graph into two or parts.

package util

import (
	"fmt"
)

// inputs: nodes in some graph
// edges: returns the nodes that a node has an edge to
// Returns the graph separators and the separable component.
// Each component slice starts with the separator that
// seperates it (which is not really part of the component).

func GraphSeparators[K comparable](inputs []K, edges func(K) []K) ([]K, [][]K) {
	if len(inputs) == 0 {
		return nil, nil
	}
	if len(inputs) == 1 {
		return []K{inputs[0]}, [][]K{[]K{inputs[0]}}
	}
	nodes := make([]*sepNodeT, len(inputs))
	lookup := map[K]*sepNodeT{}
	for i, input := range inputs {
		nodes[i] = &sepNodeT{dataIndex: i, unusedEdges: NewSet[*sepNodeT]()}
		lookup[input] = nodes[i]
	}
	for i, parent := range inputs {
		from := nodes[i]
		for _, other := range edges(parent) {
			to := lookup[other]
			if from != to && !from.unusedEdges.Contains(to) {
				from.unusedEdges.Add(to)
				to.unusedEdges.Add(from)
			}
		}
	}

	intSeparators, intComponents := findSeparators(nodes[0])

	lookupSlice := func(indexes []int) []K {
		res := make([]K, len(indexes))
		for i, index := range indexes {
			res[i] = inputs[index]
		}
		return res
	}
	components := make([][]K, len(intComponents))
	for i, indexes := range intComponents {
		components[i] = lookupSlice(indexes)
	}
	return lookupSlice(intSeparators.Members()), components
}

// Algorithm from Graph Algorithms, Shimon Even
//
// This does a depth-first walk of the graph, recording the length of
// each node's minimum path from the root as it does so.  If the
// minimum path for a set of nodes is greater than the node by which
// the subgraph was reached in the walk, than that node is a separator
// for the subgraph.

type sepNodeT struct {
	dataIndex   int       // index into the user's data
	dfsIndex    int       // ordering from depth-first search
	parent      *sepNodeT // parent in the DFS tree
	level       int       // minimum depth from root, so far
	unusedEdges SetT[*sepNodeT]
}

func findSeparators(start *sepNodeT) (SetT[int], [][]int) {
	separators := NewSet[int]()
	components := [][]int{}
	start.dfsIndex = 1
	start.level = 1
	dfsIndex := 2
	stack := StackT[*sepNodeT]{}
	stack.Push(start)
	node := start
	for {
		if 0 < len(node.unusedEdges) {
			other := node.unusedEdges.Pop()
			if other.dfsIndex == 0 { // other has not been seen before
				stack.Push(other)
				other.parent = node
				other.level = dfsIndex
				other.dfsIndex = dfsIndex
				dfsIndex += 1
				node = other
			} else if other.dfsIndex < node.level {
				node.level = other.dfsIndex
			}
		} else if node.parent == nil {
			break
		} else if node.level < node.parent.dfsIndex {
			parent := node.parent
			if node.level < parent.level {
				parent.level = node.level
			}
			node = parent
		} else {
			parent := node.parent
			if parent != start || 0 < len(start.unusedEdges) {
				separators.Add(parent.dataIndex)
			}
			comp := []int{parent.dataIndex}
			for {
				n := stack.Pop()
				comp = append(comp, n.dataIndex)
				if n == node {
					break
				}
			}
			components = append(components, comp)
			node = parent // not in the algorithm above, but necessary
		}
	}
	return separators, components
}

func SeparatorsTest() {
	//    graph := map[int][]int{0: []int{1, 2, 3}, 1: []int{1}, 2: []int{3, 4}, 3: []int{2, 5}, 4: []int{}, 5: []int{}}
	graph := map[int][]int{0: []int{1, 2}, 1: []int{1, 3}, 2: []int{1, 3}, 3: []int{}, 4: []int{}, 5: []int{}}
	//    graph := map[int][]int{0: []int{1}, 1: []int{2, 4}, 2: []int{2, 1, 4}, 3: []int{3}, 4: []int{5}, 5: []int{}}
	//    graph := map[int][]int{1: []int{2}, 2: []int{3}, 3: []int{2}}
	//    graph := map[int][]int{2: []int{3}, 3: []int{3}}
	seps, comps := GraphSeparators([]int{0, 1, 2, 3, 4, 5}, func(i int) []int { return graph[i] })
	fmt.Printf("separators:")
	for _, elt := range seps {
		fmt.Printf(" %d", elt)
	}
	fmt.Printf("\n")
	for _, comp := range comps {
		for _, elt := range comp {
			fmt.Printf(" %d", elt)
		}
		fmt.Printf("\n")
	}
}
