// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package app

func add(x uint32, y uint32) uint32 {
	z := x + 6
	z = x + 11
	z--
	if x < y {
		x = x + y + 2
	} else {
		x = x * y
	}
	return x + z
}

func comp(x int, y int) int {
	z := 0
	if x == y {
		z = z + 100000
	} else {
		z = z + 200000
	}
	if x != y {
		z = z + 10000
	} else {
		z = z + 20000
	}
	if x < y {
		z = z + 1000
	} else {
		z = z + 2000
	}
	if x <= y {
		z = z + 100
	} else {
		z = z + 200
	}
	if x > y {
		z = z + 10
	} else {
		z = z + 20
	}
	if x >= y {
		z = z + 1
	} else {
		z = z + 2
	}
	return z
}
