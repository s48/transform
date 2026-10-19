// Copyright 2026 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Flags utility.

package util

import (
	"fmt"
)

// Uses get strung together in a slice.

type ListFlagT struct {
	list []string
}

func (list *ListFlagT) String() string {
	return fmt.Sprintf("-v, %s", list.list)
}

func (list *ListFlagT) Set(value string) error {
	list.list = append(list.list, value)
	return nil
}

func (list *ListFlagT) Values() []string {
	return list.list
}
