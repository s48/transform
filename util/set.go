// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package util

import (
	"maps"
)

// A set is a map from objects to the empty struct.

type SetT[E comparable] map[E]struct{}

// s := NewSet[int]()
//   or
// s := NewSet(1)

func NewSet[E comparable](members ...E) SetT[E] {
	set := SetT[E]{}
	for _, member := range members {
		set[member] = struct{}{}
	}
	return set
}

func (set SetT[E]) Add(members ...E) {
	for _, member := range members {
		set[member] = struct{}{}
	}
}

func (set SetT[E]) Remove(member E) {
	delete(set, member)
}

// Removes one member of the set and returns it.
func (set SetT[E]) Pop() E {
	var result E
	for member := range set {
		result = member
		break
	}
	delete(set, result)
	return result
}

func (set SetT[E]) Contains(member E) bool {
	_, found := set[member]
	return found
}

// Because sets are just aliased maps you can loop through them with
//   for elt, _ := range mySet { ... }

func (set SetT[E]) Members() []E {
	result := make([]E, 0, len(set))
	for member := range set {
		result = append(result, member)
	}
	return result
}

func (set SetT[E]) Union(other SetT[E]) SetT[E] {
	result := maps.Clone(set)
	maps.Copy(result, other)
	return result
}

// Assuming that lookup is more-or-less constant we want to loop
// through the smaller of the two sets.

func (set SetT[E]) Intersection(other SetT[E]) SetT[E] {
	if len(other) < len(set) {
		return other.Intersection(set)
	}
	result := NewSet[E]()
	for member := range set {
		if other.Contains(member) {
			result.Add(member)
		}
	}
	return result
}

func (set SetT[E]) Difference(other SetT[E]) SetT[E] {
	result := NewSet[E]()
	for member := range set {
		if !other.Contains(member) {
			result.Add(member)
		}
	}
	return result
}
