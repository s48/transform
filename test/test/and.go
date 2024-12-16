// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package app

func and(x int, y int) int {
	if x < y && y < 10 {
		x = x + y + 2
	} else {
		x = x * y
	}
	return x
}

func or(x int, y int) int {
	if x < y || y < 10 {
		x = x + y + 2
	} else {
		x = x * y
	}
	return x
}

func not(x int, y int) int {
	if !(x >= y) || !(y >= 10) {
		x = x + y + 2
	} else {
		x = x * y
	}
	return x
}
