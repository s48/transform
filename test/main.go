// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Compile and evaluate test files.
//  --go <file>     Compiles and evaluates the functions in 'test/<file>.go'.
//  --func <name>   Only uses the named function.

package main

import (
	"flag"
	"fmt"
	"os"

	"go/ast"

	"github.com/s48/transform/cps"
	"github.com/s48/transform/front"
)

func main() {
	goFilename := flag.String("go", "", "Go file")
	goFunction := flag.String("func", "", "Go function")
	flag.Parse()

	cps.DefinePrimops()

	source := "test/" + *goFilename + ".go"
	in, err := os.ReadFile(source)
	if err != nil {
		if os.IsNotExist(err) {
			panic(fmt.Sprintf("%s: File not found.\n", source))
		} else {
			panic(fmt.Sprintf("Error reading file: %v", err))
		}
	}

	parsedFiles := front.NewParsedFiles("test", "./...")
	parsedFiles.ParseFile(source, in)
	parsedFiles.TypeCheck()

	lambdas := []*cps.CallNodeT{}
	for _, rawDecl := range parsedFiles.AstFiles[0].Decls {
		switch decl := rawDecl.(type) {
		case *ast.FuncDecl:
			if *goFunction == "" || *goFunction == decl.Name.Name {
				lambda := front.MakeTopLevelForm(decl, parsedFiles, front.BindingsT{})
				front.SimplifyTopLevel(lambda)
				cps.AllocateRegisters(lambda)
				lambdas = append(lambdas, lambda)
			}
		}
	}

	for _, lambda := range lambdas {
		runTests(lambda.Name, lambda)
	}
}

//----------------------------------------------------------------

type testT struct {
	procCount int
	jumpCount int
	callCount int
	cases     []testCaseT
}

type testCaseT struct {
	inputs  []int
	outputs []int
}

// There should be a way to put these in the test files themselves.

var allTests = map[string]*testT{
	"add": &testT{cases: []testCaseT{
		testCaseT{[]int{4, 4}, []int{30}},
		testCaseT{[]int{4, 5}, []int{25}},
		testCaseT{[]int{5, 4}, []int{35}},
	}},
	"comp": &testT{cases: []testCaseT{
		testCaseT{[]int{4, 4}, []int{122121}},
		testCaseT{[]int{4, 5}, []int{211122}},
		testCaseT{[]int{5, 4}, []int{212211}},
	}},
	"fact": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{5}, []int{120}},
	}},
	"fact_int": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{5}, []int{120}},
	}},
	"fact_two_loop": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{5}, []int{120}},
	}},
	"fact_two_loop2": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{6}, []int{720}},
	}},
	"fact_three_loop": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{6}, []int{720}},
	}},
	"fact_for": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{5}, []int{120}},
	}},
	"fact_break": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{5}, []int{120}},
	}},
	"fact_break2": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{5}, []int{120}},
	}},
	"fact_no_three": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{5}, []int{40}},
	}},
	"fact_range": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{5}, []int{120}},
	}},
	"fact_range_key": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{5}, []int{120}},
	}},
	"fact_range_define_key": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{5}, []int{120}},
	}},
	"fact_range_no_key": &testT{cases: []testCaseT{
		testCaseT{[]int{1}, []int{1}},
		testCaseT{[]int{5}, []int{120}},
	}},
	"slice_sum": &testT{cases: []testCaseT{
		testCaseT{[]int{}, []int{15}},
	}},
	"nested_for": &testT{cases: []testCaseT{
		testCaseT{[]int{3, 4}, []int{319}},
	}},
	"and": &testT{cases: []testCaseT{
		testCaseT{[]int{1, 4}, []int{7}},     // x < y && y < 10
		testCaseT{[]int{2, 10}, []int{20}},   // x < y && y !< 10
		testCaseT{[]int{4, 3}, []int{12}},    // x !< y && y < 10
		testCaseT{[]int{20, 10}, []int{200}}, // x !< y && y !< 10
	}},
	"or": &testT{cases: []testCaseT{
		testCaseT{[]int{1, 4}, []int{7}},     // x < y || y < 10
		testCaseT{[]int{2, 10}, []int{14}},   // x < y || y !< 10
		testCaseT{[]int{4, 3}, []int{9}},     // x !< y || y < 10
		testCaseT{[]int{20, 10}, []int{200}}, // x !< y || y !< 10
	}},
	"not": &testT{cases: []testCaseT{
		testCaseT{[]int{1, 4}, []int{7}}, // same as "or"
		testCaseT{[]int{2, 10}, []int{14}},
		testCaseT{[]int{4, 3}, []int{9}},
		testCaseT{[]int{20, 10}, []int{200}},
	}},
	"call": &testT{cases: []testCaseT{
		testCaseT{[]int{10}, []int{302}},
	}},
}

func runTests(filename string, proc *cps.CallNodeT) bool {
	test := allTests[filename]
	okay := true
	fmt.Printf("running '%s' tests\n", filename)
	for i, testCase := range test.cases {
		results := cps.RegEvaluate(proc, testCase.inputs)
		if len(results) != len(testCase.outputs) {
			fmt.Printf("  test %d returned %d outputs when %d were expected\n",
				i, len(results), len(testCase.outputs))
			okay = false
			continue
		}
		for j, result := range results {
			if result == testCase.outputs[j] {
				continue
			}
			fmt.Printf("  test %d returned", i)
			for _, n := range results {
				fmt.Printf(" %d", n)
			}
			fmt.Printf(" but expected")
			for _, n := range testCase.outputs {
				fmt.Printf(" %d", n)
			}
			fmt.Printf("\n")
			okay = false
			break
		}
	}
	return okay
}
