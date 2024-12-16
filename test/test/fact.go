// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package app

func fact(n uint32) uint32 {
	var r uint32 = 1
loop:
	if n < 2 {
		return r
	}
	r = r * n
	n = n - 1
	goto loop
}

func fact_int(n int) int {
	r := 1
loop:
	if n < 2 {
		return r
	}
	r = r * n
	n = n - 1
	goto loop
}
