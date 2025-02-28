// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Pretty-printer for CPS nodes.  The output is Scheme-like for the
// most part.

package cps

import (
	"bytes"
	"fmt"
	"io"
	"os"
	"strings"
)

func PpCps(rawNode NodeT) {
	writer := MakePpCpsWriter(os.Stdout)
	switch node := rawNode.(type) {
	case *CallNodeT:
		if node == nil {
			fmt.Printf("ppCps node is nil\n")
		} else if node.IsLambda() {
			ppCpsLambda(node, 4, writer)
		} else {
			writeNonSimpleCall(node, writer)
		}
	default:
		ppCpsValue(rawNode, writer)
	}
	writer.Newline()
}

func ppCpsLambda(node *CallNodeT, indentTo int, writer *PpCpsWriterT) {
	writer.Freshline()
	writer.Newline()
	fmt.Fprintf(writer, "%d", node.Id)
	writer.IndentTo(indentTo)
	fmt.Fprintf(writer, "(%c %s ", "CPJ"[node.CallType], callName(node))
	body := node
	if body.IsLambda() {
		writeCallOutputs(node, writer)
		body = node.Next[0]
	} else {
		fmt.Fprintf(writer, "()")
	}
	internal := ppCpsBody(body, indentTo, writer)
	fmt.Fprintf(writer, ")")
	for _, lambda := range internal {
		ppCpsLambda(lambda, indentTo+1, writer)
	}
}

func ppCpsBody(call *CallNodeT, indentTo int, writer *PpCpsWriterT) []*CallNodeT {
	writer.Newline()
	if isSimpleCall(call) || isLetCall(call) {
		return writeLetStar(call, indentTo, writer)
	} else {
		writer.IndentTo(indentTo + 2)
		return writeNonSimpleCall(call, writer)
	}
}

func isSimpleCall(call *CallNodeT) bool {
	return len(call.Next) == 1
}

func isLetCall(call *CallNodeT) bool {
	return call.Primop.Name() == "let"
}

// Write out a series of calls as a LET*.  The LET* ends when a call is reached
// that is neither a simple call or a call to a lambda.

func writeLetStar(call *CallNodeT, indentTo int, writer *PpCpsWriterT) []*CallNodeT {
	writer.IndentTo(indentTo + 2)
	fmt.Fprintf(writer, "(LET* (")
	lambdas := []*CallNodeT{}
	first := true
	for ; isSimpleCall(call) || isLetCall(call); call = call.Next[0] {
		if !first {
			fmt.Fprintf(writer, "\n")
		}
		first = false
		lambdas = append(lambdas, writeSimpleCall(call, indentTo, writer)...)
	}
	fmt.Fprintf(writer, ")\n")
	writer.IndentTo(indentTo + 4)
	lambdas = append(lambdas, writeNonSimpleCall(call, writer)...)
	fmt.Fprintf(writer, ")")
	return lambdas
}

// Write out one line of a LET*.  For non-let-calls we
// write the variables bound by the continuation and then the primop and
// non-continuation arguments of the call.

func writeSimpleCall(call *CallNodeT, indentTo int, writer *PpCpsWriterT) []*CallNodeT {
	//    fmt.Printf("%d -> %d + 9\n", writer.Column, indentTo)
	writer.IndentTo(indentTo + 9)
	if isLetCall(call) {
		return writeLetCall(call, indentTo, writer)
	} else {
		fmt.Fprintf(writer, "(")
		writeCallOutputs(call, writer)
		writer.IndentTo(indentTo + 23)
		fmt.Fprintf(writer, "(%s", call.Primop.Name())
		writeCallInputs(call, 0, writer)
		fmt.Fprintf(writer, ")")
		writer.IndentTo(60)
		fmt.Fprintf(writer, " %s", callExtra(call))
		return findLambdaNodes(call)
	}
}

func writeLetCall(call *CallNodeT, indentTo int, writer *PpCpsWriterT) []*CallNodeT {
	fmt.Fprintf(writer, "(")
	writeCallOutputs(call, writer)
	if len(call.Inputs) == 0 {
		fmt.Fprintf(writer, ")")
		writer.IndentTo(60)
		fmt.Fprintf(writer, " %s", callExtra(call))
		return []*CallNodeT{}
	} else {
		writer.IndentTo(indentTo + 23)
		ppCpsValue(call.Inputs[0], writer)
		writeCallInputs(call, 1, writer)
		writer.IndentTo(60)
		fmt.Fprintf(writer, " %s", callExtra(call))
		return findLambdaNodes(call)
	}
}

func findLambdaNodes(call *CallNodeT) []*CallNodeT {
	lambdas := []*CallNodeT{}
	for _, input := range call.Inputs {
		if input != nil && input.NodeType() == CallNode {
			lambdas = append(lambdas, input.(*CallNodeT))
		}
	}
	if len(call.Next) != 1 {
		lambdas = append(lambdas, call.Next...)
	}
	return lambdas
}

// Write out a call that ends a LET* block.

func writeNonSimpleCall(call *CallNodeT, writer *PpCpsWriterT) []*CallNodeT {
	fmt.Fprintf(writer, "(%s", call.Primop.Name())
	writeCallInputs(call, 0, writer)
	if 0 < len(call.Next) {
		fmt.Fprintf(writer, " =>")
		for _, next := range call.Next {
			fmt.Fprintf(writer, " ^")
			printCallName(next, writer)
		}
	}
	writer.IndentTo(60)
	fmt.Fprintf(writer, " %s", callExtra(call))
	return findLambdaNodes(call)
}

func ppCpsValue(rawNode NodeT, writer *PpCpsWriterT) {
	if rawNode == nil {
		fmt.Fprintf(writer, "{nil}")
		return
	}
	switch node := rawNode.(type) {
	case *CallNodeT:
		fmt.Fprintf(writer, "^")
		printCallName(node, writer)
	case *LiteralNodeT:
		fmt.Fprintf(writer, "'%s", node.String())
	case *ReferenceNodeT:
		printVariableName(node.Variable, writer)
	default:
		panic(fmt.Sprintf("ppCpsValue got funny node %+v", node))
	}
}

// Printing variables and lambda nodes

func printVariableName(variable *VariableT, writer *PpCpsWriterT) {
	if variable == nil {
		fmt.Fprintf(writer, "nil")
	} else {
		fmt.Fprintf(writer, "%s_%d", variable.Name, variable.Id)
	}
}

func printCallName(node *CallNodeT, writer *PpCpsWriterT) {
	fmt.Fprintf(writer, "%s_%d", node.Name, node.Id)
}

func callName(node *CallNodeT) string {
	return fmt.Sprintf("%s_%d", node.Name, node.Id)
}

func writeCallInputs(call *CallNodeT, start int, writer *PpCpsWriterT) {
	for i := start; i < len(call.Inputs); i++ {
		fmt.Fprintf(writer, " ")
		ppCpsValue(call.Inputs[i], writer)
	}
	fmt.Fprintf(writer, ")")
}

func writeCallOutputs(node *CallNodeT, writer io.Writer) {
	fmt.Fprintf(writer, "(")
	for i, variable := range node.Outputs {
		if 0 < i {
			fmt.Fprintf(writer, " ")
		}
		if variable == nil {
			fmt.Fprintf(writer, "_")
		} else {
			fmt.Fprintf(writer, "%s_%d", variable.Name, variable.Id)
			if variable.Register != nil {
				fmt.Fprintf(writer, "(%s)", variable.Register)
			}
		}
	}
	fmt.Fprintf(writer, ")")
}

func callExtra(call *CallNodeT) string {
	result := fmt.Sprintf("%d %v", call.flag, call.IsSimplified())
	if call.source != 0 && TheFileSet != nil {
		position := TheFileSet.Position(call.source)
		if position.IsValid() {
			result += fmt.Sprintf(" %d:%d", position.Line, position.Column)
		}
	}
	return result
}

//----------------------------------------------------------------
// Printing a call on a single line.

func CallString(call *CallNodeT) string {
	buf := new(bytes.Buffer)
	fmt.Fprintf(buf, "(%s", call.Primop.Name())
	for _, rawInput := range call.Inputs {
		if rawInput == nil {
			fmt.Fprintf(buf, " {nil}")
			continue
		}
		switch input := rawInput.(type) {
		case *CallNodeT:
			fmt.Fprintf(buf, " ^%s_%d", call.Name, call.Id)
		case *LiteralNodeT:
			fmt.Fprintf(buf, " '%s", input.String())
		case *ReferenceNodeT:
			fmt.Fprintf(buf, " %s_%d", input.Variable.Name, input.Variable.Id)
		default:
			panic(fmt.Sprintf("ppCpsValue got funny input %+v", input))
		}
	}
	fmt.Fprintf(buf, ")")
	return buf.String()
}

//----------------------------------------------------------------
// An io.Writer that keeps track of the current column.

type PpCpsWriterT struct {
	writer io.Writer
	Column int
}

func MakePpCpsWriter(writer io.Writer) *PpCpsWriterT {
	return &PpCpsWriterT{writer: writer, Column: 0}
}

func (writer *PpCpsWriterT) Write(p []byte) (n int, err error) {
	for _, b := range p {
		if b == '\n' {
			writer.Column = 0
		} else {
			writer.Column += 1
		}
	}
	return writer.writer.Write(p)
}

func (writer *PpCpsWriterT) Newline() {
	writer.Column = 0
	writer.writer.Write([]byte("\n"))
}

func (writer *PpCpsWriterT) Freshline() {
	if writer.Column != 0 {
		writer.Newline()
	}
}

func (writer *PpCpsWriterT) IndentTo(column int) {
	if writer.Column == column {
		return
	}
	count := column
	if writer.Column < column {
		count -= writer.Column
	} else {
		writer.Newline()
	}
	writer.writer.Write([]byte(strings.Repeat(" ", count)))
	writer.Column += count
}
