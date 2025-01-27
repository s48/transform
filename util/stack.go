// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Simple but dumb stack implementation.

package util

import ()

type StackT[T any] struct {
	count int
	elts  []T
}

func (stack *StackT[T]) Len() int {
	return stack.count
}

func (stack *StackT[T]) Ref(i int) T {
	if stack.count <= i {
		panic("indexeing past the end of stack")
	}
	return stack.elts[i]
}

func (stack *StackT[T]) Push(elt T) {
	if stack.count < len(stack.elts) {
		stack.elts[stack.count] = elt
	} else {
		stack.elts = append(stack.elts, elt)
	}
	stack.count += 1
}

func (stack *StackT[T]) Pop() T {
	if stack.count == 0 {
		panic("popping from empty stack")
	}
	stack.count -= 1
	return stack.elts[stack.count]
}

func (stack *StackT[T]) Top() T {
	if stack.count == 0 {
		panic("top from empty stack")
	}
	return stack.elts[stack.count-1]
}
