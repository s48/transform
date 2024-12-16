// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package app

func fact_for(n int) int {
	r := 1
	for i := 2; i <= n; i += 1 {
		r *= i
	}
	return r
}

func fact_break(n int) int {
	r := 1
	i := 2
	for {
		if n < i {
			break
		}
		r *= i
		i += 1
	}
	return r
}

func fact_break2(n int) int {
	r := 1
	for i := 2; ; i += 1 {
		if n < i {
			break
		}
		r *= i
	}
	return r
}

func fact_no_three(n int) int {
	r := 1
	for i := 2; i <= n; i += 1 {
		if i == 3 {
			continue
		}
		r *= i
	}
	return r
}

func fact_range(n int) int {
	r := 1
	i := 1
	for range n {
		r *= i
		i += 1
	}
	return r
}

func fact_range_key(n int) int {
	r := 1
	for i := range n {
		r *= i + 1
	}
	return r
}
