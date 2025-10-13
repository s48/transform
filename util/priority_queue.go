// Copyright 2025 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Based on the example in container/heap.

package util

import (
	"container/heap"
)

// Wrapper type to hide the sort and heap interface methods.

type PriorityQueueT[T comparable] struct {
	queue priorityQueueT[T]
	cells map[T]*cellT[T] // so we can up date priorities
}

func MakePriorityQueue[T comparable](less func(x T, y T) bool) *PriorityQueueT[T] {
	return &PriorityQueueT[T]{priorityQueueT[T]{less: less}, map[T]*cellT[T]{}}
}

func (pq *PriorityQueueT[T]) Len() int {
	return len(pq.queue.queue)
}

func (pq *PriorityQueueT[T]) Empty() bool {
	return len(pq.queue.queue) == 0
}

func (pq *PriorityQueueT[T]) Enqueue(x T) {
	cell := &cellT[T]{value: x}
	pq.cells[x] = cell
	heap.Push(&pq.queue, cell)
}

func (pq *PriorityQueueT[T]) Dequeue() T {
	cell := heap.Pop(&pq.queue).(*cellT[T])
	delete(pq.cells, cell.value)
	return cell.value
}

func (pq *PriorityQueueT[T]) Peek() T {
	return pq.queue.queue[0].value
}

func (pq *PriorityQueueT[T]) Update(value T) {
	cell := pq.cells[value]
	if cell != nil {
		heap.Fix(&pq.queue, cell.index)
	}
}

// The actual priority queue.

type priorityQueueT[T comparable] struct {
	queue []*cellT[T]
	less  func(x T, y T) bool
}

type cellT[T any] struct {
	value T
	index int
}

func (pq priorityQueueT[T]) Len() int { return len(pq.queue) }

func (pq priorityQueueT[T]) Less(i, j int) bool {
	return pq.less(pq.queue[j].value, pq.queue[i].value)
}

func (pq priorityQueueT[T]) Swap(i, j int) {
	pq.queue[i], pq.queue[j] = pq.queue[j], pq.queue[i]
	pq.queue[i].index = i
	pq.queue[j].index = j
}

func (pq *priorityQueueT[T]) Push(x any) {
	n := len(pq.queue)
	cell := x.(*cellT[T])
	cell.index = n
	pq.queue = append(pq.queue, cell)
}

func (pq *priorityQueueT[T]) Pop() any {
	queue := pq.queue
	newLength := len(queue) - 1
	cell := queue[newLength]
	queue[newLength] = nil // GC safety
	pq.queue = queue[0:newLength]
	return cell
}
