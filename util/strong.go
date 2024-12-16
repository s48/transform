// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Code to find the strongly connected components of a graph using
// Kosaraju's algorithm.

package util

import (
	"fmt"
)

// inputs: nodes in some graph
// edges: returns the nodes that a node has an edge to
// Returns the strongly connected components in topological order.

func StronglyConnectedComponents[K comparable](inputs []K, edges func(K) []K) [][]K {
	nodes := make([]*nodeT, len(inputs))
	lookup := map[K]*nodeT{}
	for i, input := range inputs {
		nodes[i] = &nodeT{index: i}
		lookup[input] = nodes[i]
	}
	for i, parent := range inputs {
		parentNode := nodes[i]
		for _, child := range edges(parent) {
			childNode := lookup[child]
			parentNode.children = append(parentNode.children, childNode)
			childNode.parents = append(childNode.parents, parentNode)
		}
	}
	order := make([]*nodeT, 0, len(nodes))
	for _, node := range nodes {
		visitPostorder(node, false, func(n *nodeT) { order = append(order, n) })
	}
	for _, node := range nodes {
		node.seen = false
	}
	result := [][]K{}
	for i := len(order) - 1; 0 <= i; i-- {
		node := order[i]
		component := []K{}
		visitPostorder(node, true, func(n *nodeT) { component = append(component, inputs[n.index]) })
		if 0 < len(component) {
			result = append(result, component)
		}
	}
	return result
}

type nodeT struct {
	index    int // index of the corresponding input node
	seen     bool
	children []*nodeT
	parents  []*nodeT
}

func visitPostorder(node *nodeT, up bool, visit func(*nodeT)) {
	var recur func(*nodeT)
	recur = func(node *nodeT) {
		if node.seen {
			return
		}
		node.seen = true
		if up {
			for _, parent := range node.parents {
				recur(parent)
			}
		} else {
			for _, child := range node.children {
				recur(child)
			}
		}
		visit(node)
	}
	recur(node)
}

func StronglyConnectedTest() {
	graph := map[int][]int{0: []int{1}, 1: []int{2, 4}, 2: []int{3, 4}, 3: []int{1, 2}, 4: []int{5}, 5: []int{}}
	//    graph := map[int][]int{0: []int{1}, 1: []int{2, 4}, 2: []int{2, 1, 4}, 3: []int{3}, 4: []int{5}, 5: []int{}}
	//    graph := map[int][]int{1: []int{2}, 2: []int{3}, 3: []int{2}}
	//    graph := map[int][]int{2: []int{3}, 3: []int{3}}
	//   scc := StronglyConnectedComponents([]int{0, 1, 2, 3, 4, 5}, func (i int) []int { return graph[i] })
	scc := StronglyConnectedComponents([]int{5, 4, 3, 2, 1, 0}, func(i int) []int { return graph[i] })
	for _, component := range scc {
		for i, elt := range component {
			if 0 < i {
				fmt.Printf(" ")
			}
			fmt.Printf("%d", elt)
		}
		fmt.Printf("\n")
	}
}
