// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

package app

func fact_two_loop(n int) int {
	r := 1
loop:
	if n < 2 {
		return r
	}
	r = r * n
	n = n - 1
	goto loop2
loop2:
	if n < 2 {
		return r
	}
	r = r * n
	n = n - 1
	if n < 3 {
		goto loop
	} else {
		goto loop2
	}
}

func fact_two_loop2(n int) int {
	r := 1
loop:
	if n < 2 {
		return r
	}
	r = r * n
	n = n - 1
	if n < 3 {
		goto loop2
	} else {
		goto loop
	}
loop2:
	if n < 2 {
		return r
	}
	r = r * n
	n = n - 1
	if n < 3 {
		goto loop
	} else {
		goto loop2
	}
}

func fact_three_loop(n int) int {
	r := 1
	if n < 5 {
		goto loop
	} else {
		goto loop2
	}
loop:
	if n < 2 {
		return r
	}
	r = r * n
	n = n - 1
	if n < 3 {
		goto loop3
	} else {
		goto loop
	}
loop2:
	if n < 2 {
		return r
	}
	r = r * n
	n = n - 1
	if n < 3 {
		goto loop3
	} else {
		goto loop
	}
loop3:
	if n < 2 {
		return r
	}
	r = r * n
	n = n - 1
	if n < 3 {
		goto loop
	} else {
		goto loop2
	}
}
