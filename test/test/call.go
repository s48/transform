// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package app

func call(n uint32) uint32 {
	f := func(x uint32) uint32 { return x*10 + 1 }
	r0 := f(n)
	r1 := f(n + 10)
	return r0 + r1
}
