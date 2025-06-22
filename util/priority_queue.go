// Copyright 2025 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Based on the example in container/heap.

package util

import (
	"container/heap"
)

// Wrapper type to hide the sort and heap interface methods.

type PriorityQueueT[T any] struct {
	queue priorityQueueT[T]
}

func MakePriorityQueue[T any](less func(x T, y T) bool) *PriorityQueueT[T] {
	return &PriorityQueueT[T]{priorityQueueT[T]{less: less}}
}

func (pq *PriorityQueueT[T]) Len() int {
	return len(pq.queue.queue)
}

func (pq *PriorityQueueT[T]) Empty() bool {
	return len(pq.queue.queue) == 0
}

func (pq *PriorityQueueT[T]) Enqueue(x T) {
	heap.Push(&pq.queue, x)
}

func (pq *PriorityQueueT[T]) Dequeue() T {
	return heap.Pop(&pq.queue).(T)
}

// The actual priority queue.

type priorityQueueT[T any] struct {
	queue []T
	less  func(x T, y T) bool
}

func (pq priorityQueueT[T]) Len() int { return len(pq.queue) }

func (pq priorityQueueT[T]) Less(i, j int) bool {
	return pq.less(pq.queue[j], pq.queue[i])
}

func (pq priorityQueueT[T]) Swap(i, j int) {
	pq.queue[i], pq.queue[j] = pq.queue[j], pq.queue[i]
}

func (pq *priorityQueueT[T]) Push(x any) {
	pq.queue = append(pq.queue, x.(T))
}

func (pq *priorityQueueT[T]) Pop() any {
	queue := pq.queue
	newLength := len(queue) - 1
	item := queue[newLength]
	var defaultValue T
	queue[newLength] = defaultValue // reinitialize for safety
	pq.queue = queue[0:newLength]
	return item
}
