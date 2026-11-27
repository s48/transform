// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Converting Go ASTs into CPS.  This is far from complete.

package front

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"math/big"

	. "github.com/s48/transform/cps"
	"github.com/s48/transform/util"
)

// Keeping track of where we are in the Go AST.

type envT struct {
	// A stack of continuation variables to call at returns.
	returnVars util.StackT[*VariableT]
	// Type information from the Go front end.
	typeInfo *types.Info
	// types.Obj -> package variable
	packageBindings BindingsT
	// collect package variables as they are referenced
	newPackageVars []*VariableT
	// types.Obj -> lexically-bound variable
	bindings BindingsT
	// For adding 'makeCell' calls at the beginning.
	currentBlock util.StackT[*CallsT]

	// Variables bound to 'continue', 'break', and 'fallthrough'
	// continuations.  There are stacks with the current values on
	// top, for 'break' and 'continuation' statements without labels,
	// and binding tables for those with labels.
	continueVars    util.StackT[*VariableT]
	breakVars       util.StackT[*VariableT]
	fallthroughVars util.StackT[*VariableT]
	// These are not yet in use.
	continueBindings BindingsT
	breakBindings    BindingsT
}

type BindingsT map[types.Object]*VariableT

func bindIdent(bindings BindingsT, ident *ast.Ident, typeInfo *types.Info) *VariableT {
	obj := typeInfo.ObjectOf(ident)
	if obj == nil {
		panic("no type object for identifier '" + ident.Name + "'")
	}
	vart := MakeVariable(ident.Name, obj.Type(), ident.Pos())
	bindings[obj] = vart
	return vart
}

// 'break' with a label means to jump to the statement after the labeled for/switch/select
//    label foo:
//    statement {
//        break foo
//    }
// is the same as
//    statement {
//        goto foo
//    }
//    label foo:
// A labeled loop statement has three possible targets, the normal one for goto,
// a second one for break, and a third for continue.  At this point we don't
// handle labels for break and continue.

func MakeEnv(typeInfo *types.Info, pkgBindings BindingsT) *envT {
	return &envT{
		typeInfo:         typeInfo,
		packageBindings:  pkgBindings,
		newPackageVars:   nil,
		bindings:         BindingsT{},
		continueBindings: BindingsT{},
		breakBindings:    BindingsT{}}
}

func (env *envT) bindVar(ident *ast.Ident) *VariableT {
	return bindIdent(env.bindings, ident, env.typeInfo)
}

func (env *envT) bindCellVar(ident *ast.Ident) *VariableT {
	vart := env.bindVar(ident)
	vart.Flags["cell"] = true
	env.addMakeCell(vart)
	return vart
}

func (env *envT) addMakeCell(vart *VariableT) {
	env.currentBlock.Top().AddFirst(MakeCall(LookupPrimop("makeCell"), []*VariableT{vart}))
}

func (env *envT) lookupVar(ident *ast.Ident) *VariableT {
	return env.lookupObj(env.typeInfo.ObjectOf(ident))
}

func (env *envT) lookupObj(obj types.Object) *VariableT {
	if obj == nil {
		return nil
	}
	vart, found := env.bindings[obj]
	if found {
		return vart
	}
	return env.packageBindings[obj]
}

//----------------------------------------------------------------

func CpsFunc(name string, funcType *ast.FuncType, body *ast.BlockStmt, typ types.Type, env *envT) *CallNodeT {
	contVar := MakeVariable("c", typ.(*types.Signature).Results())
	env.returnVars.Push(contVar)
	calls := MakeCalls()
	env.currentBlock.Push(calls)
	vars := makeFieldVars(funcType.Params.List, true, env, calls)
	if funcType.Results != nil {
		vars = append(vars, makeFieldVars(funcType.Results.List, false, env, calls)...)
	}
	vars = append([]*VariableT{contVar}, vars...)
	lambda := MakeLambda(name, ProcLambda, vars)
	TopLambda = lambda
	cpsBlockStmt(body, env, calls)
	if !calls.HasFinal() {
		calls.BuildFinalCall("return", 0, contVar)
	}
	env.returnVars.Pop()
	env.currentBlock.Pop()
	calls.AddFirst(lambda)
	CheckNode(lambda)
	return lambda
}

// Make the variables for a procedures arguments and returns.  Aggregate
// arguments are copied, as the caller passes a reference to its value
// (see PointerLhsT).
func makeFieldVars(fields []*ast.Field, isParams bool, env *envT, calls *CallsT) []*VariableT {
	vars := []*VariableT{}
	for _, field := range fields {
		for _, ident := range field.Names {
			paramVarType := env.typeInfo.Defs[ident].Type() // .Underlying()
			paramVar := MakeVariable(ident.Name, paramVarType)
			vars = append(vars, paramVar)
			cellVar := env.bindCellVar(ident)
			var value NodeT = MakeReferenceNode(paramVar)
			if isParams {
				value = freshAggregateCopy(value, paramVarType, calls)
			}
			calls.BuildNoOutputCall("cellSet", cellVar, value)
		}
	}
	return vars
}

//----------------------------------------------------------------
// Statements

func cpsStmt(astNode ast.Stmt, env *envT, calls *CallsT) {
	switch x := astNode.(type) {
	case *ast.BlockStmt:
		cpsBlockStmt(x, env, calls)
	case *ast.DeclStmt:
		decl := x.Decl
		switch decl := decl.(type) {
		case *ast.GenDecl:
			switch decl.Tok {
			case token.VAR:
				for _, rawSpec := range decl.Specs {
					spec := rawSpec.(*ast.ValueSpec)
					values := []NodeT{}
					if spec.Values != nil {
						values = cpsArguments(spec.Values, env, calls)
					}
					for i, ident := range spec.Names {
						cellVar := env.bindCellVar(ident)
						var value any
						if spec.Values == nil {
							valueVar := CopyVariable(cellVar)
							delete(valueVar.Flags, "cell") // It isn't a cell.
							calls.AddCall(LookupPrimop("defaultValue"), []*VariableT{valueVar}, nil)
							// value = MakeLiteral(big.NewInt(0), cellVar.Type)
							value = valueVar
						} else {
							value = freshAggregateCopy(values[i], cellVar.Type, calls)
						}
						calls.BuildNoOutputCall("cellSet", cellVar, value)
					}
				}
			case token.CONST:
				// Do nothing: we assume that the Go front end has taken care of it.
			default:
				panic(fmt.Sprintf("unrecognized declaration at %s", source(decl.TokPos)))
			}
		default:
			panic(fmt.Sprintf("unrecognized declaration at %s", source(decl.Pos())))
		}
	case *ast.AssignStmt:
		switch x.Tok {
		case token.DEFINE, token.ASSIGN:
			newOkay := x.Tok == token.DEFINE
			// RHS can either be a single expression returning values
			// or a sequence of values, one per LHS identifier.
			if len(x.Rhs) == 1 {
				values := cpsExpr(x.Rhs[0], env, calls)
				assignCells(x.Lhs, values, newOkay, env, calls)
			} else {
				values := cpsArguments(x.Rhs, env, calls)
				assignCells(x.Lhs, values, newOkay, env, calls)
			}
		case token.ADD_ASSIGN, token.SUB_ASSIGN, token.MUL_ASSIGN,
			token.QUO_ASSIGN, token.REM_ASSIGN, token.AND_ASSIGN,
			token.OR_ASSIGN, token.XOR_ASSIGN, token.SHL_ASSIGN,
			token.SHR_ASSIGN, token.AND_NOT_ASSIGN:

			rhs := cpsExpr(x.Rhs[0], env, calls)[0]
			lhs := cpsLhs(x.Lhs[0], false, env, calls)
			before := lhs.read(calls)
			after := makeExprCall(opAssignPrimops[x.Tok], x.TokPos, x.Lhs[0], env, calls, before, rhs)[0]
			lhs.write(after, calls)
		default:
			panic(fmt.Sprintf("assignment op not handled %s", x.Tok.String()))
		}
	case *ast.ForStmt:
		if x.Init != nil {
			cpsStmt(x.Init, env, calls)
		}
		body := func(env *envT, calls *CallsT) {
			cpsStmt(x.Body, env, calls)
		}
		post := MakeCalls()
		if x.Post != nil {
			cpsStmt(x.Post, env, post)
		}
		if x.Cond == nil {
			makeForLoop(nil, nil, body, post, x.For, env, calls)
		} else {
			condCalls := MakeCalls()
			cond := cpsExpr(x.Cond, env, condCalls)[0]
			makeForLoop(condCalls, cond, body, post, x.For, env, calls)
		}
	case *ast.RangeStmt:
		cpsRangeLoop(x, env, calls)
	case *ast.IfStmt:
		cpsIfStatement(x, env, calls)
	case *ast.SwitchStmt:
		cpsSwitchStatement(x, env, calls)
	case *ast.IncDecStmt:
		lhs := cpsLhs(x.X, false, env, calls)
		delta := big.NewInt(1)
		if x.Tok == token.DEC {
			delta = big.NewInt(-1)
		}
		deltaNode := MakeLiteral(delta, env.typeInfo.Types[x.X].Type)
		before := lhs.read(calls)
		after := makeExprCall("+", x.TokPos, x.X, env, calls, before, deltaNode)[0]
		lhs.write(after, calls)
	case *ast.ReturnStmt:
		var values []NodeT
		if len(x.Results) != 1 {
			values = cpsArguments(x.Results, env, calls)
		} else {
			switch result := x.Results[0].(type) {
			case *ast.CallExpr:
				values = cpsCallExpr(result, env, calls)
			default:
				values = cpsArguments(x.Results, env, calls)
			}
		}
		// Use Map to convert []NodeT to []Any to satisfy Go's type checking.
		anyValues := Map(func(x NodeT) any { return x }, values)
		anyValues = append([]any{env.returnVars.Top()}, anyValues...)
		calls.BuildFinalCall("return", 0, anyValues...)
		calls.SetLastSource(x.Return)
	case *ast.LabeledStmt:
		cpsStmt(x.Stmt, env, calls)
	case *ast.ExprStmt:
		results := cpsExpr(x.X, env, calls)
		EraseAll(results)
	case *ast.BranchStmt:
		var jumpVar *VariableT
		switch x.Tok {
		case token.GOTO:
			jumpVar = env.lookupVar(x.Label)
		case token.BREAK:
			jumpVar = env.breakVars.Top()
		case token.CONTINUE:
			jumpVar = env.continueVars.Top()
		case token.FALLTHROUGH:
			jumpVar = env.fallthroughVars.Top()
		}
		if jumpVar == nil {
			panic("unbound branch")
		}
		// Tok    token.Token // keyword token (BREAK, CONTINUE, GOTO, FALLTHROUGH)
		// Label  *Ident      // label name; or nil
		calls.BuildFinalCall("jump", 0, jumpVar)
		calls.SetLastSource(x.TokPos)
	default:
		panic(fmt.Sprintf("unrecognized statement %T", astNode))
	}
}

var opAssignPrimops = map[token.Token]string{
	token.ADD_ASSIGN:     "+",
	token.SUB_ASSIGN:     "-",
	token.MUL_ASSIGN:     "*",
	token.QUO_ASSIGN:     "/",
	token.REM_ASSIGN:     "%",
	token.AND_ASSIGN:     "&",
	token.OR_ASSIGN:      "|",
	token.XOR_ASSIGN:     "^",
	token.SHL_ASSIGN:     "<<",
	token.SHR_ASSIGN:     ">>",
	token.AND_NOT_ASSIGN: "&^"}

// Blocks, which are entirely about labels and gotos.

func cpsBlockStmt(blockStmt *ast.BlockStmt, env *envT, calls *CallsT) {
	if len(blockStmt.List) == 0 {
		return
	}
	env.currentBlock.Push(calls)
	labels := []*ast.Ident{}
	block := []ast.Stmt{}
	blocks := [][]ast.Stmt{}
	for _, stmtNode := range blockStmt.List {
		switch stmt := stmtNode.(type) {
		case *ast.LabeledStmt:
			labels = append(labels, stmt.Label)
			blocks = append(blocks, block)
			block = []ast.Stmt{stmt.Stmt}
		default:
			block = append(block, stmtNode)
		}
	}
	if 0 < len(block) {
		blocks = append(blocks, block)
	}

	if len(labels) == 0 {
		cpsBlock(blockStmt.List, env, calls)
	} else {
		cpsBlockLabels(labels, blocks, env, calls)
	}
	env.currentBlock.Pop()
}

func cpsBlock(statements []ast.Stmt, env *envT, calls *CallsT) {
	for _, next := range statements {
		cpsStmt(next, env, calls)
	}
}

func cpsBlockLabels(labels []*ast.Ident, blocks [][]ast.Stmt, env *envT, calls *CallsT) {
	vars := []*VariableT{}
	for _, label := range labels {
		labelVar := env.bindVar(label)
		labelVar.Flags["label"] = true
		vars = append(vars, labelVar)
	}

	firstBlock := MakeCalls()
	cpsBlock(blocks[0], env, firstBlock)
	if !firstBlock.HasFinal() {
		firstBlock.BuildFinalCall("jump", 0, vars[0])
	}

	lambdas := []NodeT{}
	var lastBlockLast *CallNodeT
	for i, block := range blocks[1:] {
		calls := MakeCalls()
		cpsBlock(block, env, calls)
		lambda := MakeLambda(vars[i].Name, JumpLambda, nil)
		AttachNext(lambda, calls.First)
		lambdas = append(lambdas, lambda)
		if i == len(vars)-1 {
			lastBlockLast = calls.Last
		} else if !calls.HasFinal() {
			calls.BuildFinalCall("jump", 0, vars[i+1])
		}
	}
	calls.AddPrimopVarsCall("letrec", vars, lambdas...)
	calls.AppendCalls(firstBlock)
	calls.Last = lastBlockLast
}

func cpsIfStatement(x *ast.IfStmt, env *envT, calls *CallsT) {
	// Init Stmt      // initialization statement; or nil
	// Cond Expr      // condition
	// Body *BlockStmt
	// Else Stmt // else branch; or nil
	if x.Init != nil {
		cpsStmt(x.Init, env, calls)
	}
	joinVar := MakeVariable("join", nil)

	trueCalls := MakeCalls()
	cpsBlockStmt(x.Body, env, trueCalls)
	if !trueCalls.HasFinal() {
		trueCalls.BuildFinalCall("jump", 0, joinVar)
	}

	falseCalls := MakeCalls()
	if x.Else != nil {
		cpsStmt(x.Else, env, falseCalls)
	}
	if !falseCalls.HasFinal() {
		falseCalls.BuildFinalCall("jump", 0, joinVar)
	}

	cond := cpsExpr(x.Cond, env, calls)[0]
	if len(joinVar.Refs) == 0 {
		makeIf(cond, trueCalls, falseCalls, nil, x.If, calls)
	} else {
		joinLambda := MakeLambda("c", JumpLambda, nil)
		calls.BuildVarCall("let", joinVar, joinLambda)
		makeIf(cond, trueCalls, falseCalls, joinLambda, x.If, calls)
	}
}

// SwitchStmt:
//   Init   Stmt       // initialization statement; or nil
//   Tag    Expr       // tag expression; or nil
//   Body   *BlockStmt // CaseClauses only
// If Tag is nil the case expressions have boolean values.
//
// CaseClause:
//   List  []Expr    // list of expressions or types; nil means default case
//   Body  []Stmt    // statement list; or nil
//
// A switch turns into a LETREC where the values are the CaseClause
// Bodies as jump lambdas, plus one more that binds a 'break' variable
// to the continuation to the switch statement.  Each CaseClause jump
// lambda ends with a jump, either to the 'break' variable, or, if
// there is a 'fallthrough', to the variable bound to the next
// CaseClause's body.
//
// The body of the LETREC is a set of nested IF's that check the value
// of the tag against the CaseClause Exprs, jumping to the proper
// clause body when it finds a match.

func cpsSwitchStatement(x *ast.SwitchStmt, env *envT, calls *CallsT) {
	if x.Init != nil {
		cpsStmt(x.Init, env, calls)
	}
	var tagNode NodeT
	if x.Tag != nil {
		tagNode = cpsExpr(x.Tag, env, calls)[0]
	}
	breakVar := MakeVariable("break", nil)
	env.breakVars.Push(breakVar)

	bodyVars := make([]*VariableT, len(x.Body.List))
	var defaultVar *VariableT
	for i, rawCase := range x.Body.List {
		caseClause := rawCase.(*ast.CaseClause)
		bodyVars[i] = MakeVariable("case", nil, caseClause.Case)
		if caseClause.List == nil {
			defaultVar = bodyVars[i]
		}
	}
	if defaultVar == nil {
		defaultVar = breakVar
	}

	bodyLambdas := make([]NodeT, len(x.Body.List))
	for i, rawCase := range x.Body.List {
		caseClause := rawCase.(*ast.CaseClause)
		var fallthroughVar *VariableT
		if i < len(bodyVars)-1 {
			fallthroughVar = bodyVars[i+1]
		}
		bodyLambdas[i] =
			cpsSwitchCaseBody(caseClause, fallthroughVar, breakVar, env)
	}

	breakLambda := MakeLambda("c", JumpLambda, nil)
	env.breakVars.Pop()
	calls.AddPrimopVarsCall(
		"letrec",
		append(bodyVars, breakVar),
		append(bodyLambdas, breakLambda)...)
	for i, rawCase := range x.Body.List {
		caseClause := rawCase.(*ast.CaseClause)
		cpsSwitchCaseCond(caseClause, tagNode, bodyVars[i], env, calls)
	}
	Erase(tagNode) // it was never used
	calls.BuildFinalCall("jump", 0, defaultVar)
	calls.SetLast(breakLambda)
}

// CaseClause:
//   List  []Expr    // list of expressions or types; nil means default case
//   Body  []Stmt    // statement list; or nil

func cpsSwitchCaseBody(
	caseClause *ast.CaseClause,
	fallthroughVar *VariableT,
	breakVar *VariableT,
	env *envT) *CallNodeT {

	calls := MakeCalls()
	env.fallthroughVars.Push(fallthroughVar)
	cpsBlock(caseClause.Body, env, calls)
	env.fallthroughVars.Pop()
	if !calls.HasFinal() {
		calls.BuildFinalCall("jump", 0, breakVar)
	}
	body := MakeLambda("case", JumpLambda, nil)
	AttachNext(body, calls.First)
	return body
}

func cpsSwitchCaseCond(
	caseClause *ast.CaseClause,
	tagNode NodeT,
	bodyVar *VariableT,
	env *envT,
	calls *CallsT) {

	for _, expr := range caseClause.List {
		value := cpsExpr(expr, env, calls)[0]
		if tagNode != nil {
			value = MakeReferenceNode(calls.BuildCall(
				"==",
				"v",
				types.Typ[types.Bool],
				CopyNodeTree(tagNode),
				value))
		}
		trueCall := MakeCall(LookupPrimop("jump"), nil, MakeReferenceNode(bodyVar))
		trueCall.Next = nil
		call := MakeCall(LookupPrimop("if"), nil, value)
		call.Next = []*CallNodeT{nil, nil}
		AttachNext(call, trueCall)
		calls.AppendCall(call)
	}
}

// for ( ...; i < 10; i++) { body }
//  ->
// condCalls: { t0 := i < 10; }
// cond:      t0
// post:      { i++ }

// The body's conversion needs to be delayed until after the 'continue'
// and 'break' labels have been added to the environment.
//
// From the Go spec:
//   Each iteration has its own separate declared variable (or
//   variables) [Go 1.22]. The variable used by the first iteration is
//   declared by the init statement. The variable used by each
//   subsequent iteration is declared implicitly before executing the
//   post statement and initialized to the value of the previous
//   iteration's variable at that moment.
// This is detectable if a function closes over an interation variable.

func makeForLoop(condCalls *CallsT, // any calls for evaluating 'cond'
	cond NodeT, // the loop ending expression
	body func(env *envT, calls *CallsT), // adds the body to 'calls'
	post *CallsT, // executed after the body
	position token.Pos,
	env *envT,
	calls *CallsT) {

	// (let ((break (lambda () ... after ...))) )
	breakVar := MakeVariable("break", nil)
	breakLambda := MakeLambda("break", JumpLambda, nil)
	calls.BuildVarCall("let", breakVar, breakLambda)

	//   (letrec ((top (lambda () ...))
	//            (continue (lambda () ...)))
	//     (top))
	topVar := MakeVariable("for", nil)
	topLambda := MakeLambda("for", JumpLambda, nil)
	continueVar := MakeVariable("continue", nil)
	continueLambda := MakeLambda("continue", JumpLambda, nil)
	calls.AddPrimopVarsCall("letrec",
		[]*VariableT{topVar, continueVar},
		topLambda,
		continueLambda)
	calls.BuildFinalCall("jump", 0, topVar)
	calls.SetLastSource(position)
	calls.SetLast(breakLambda)

	// continue = (lambda () ... post... (top))
	post.BuildFinalCall("jump", 0, topVar)
	calls.SetLastSource(position)
	AttachNext(continueLambda, post.First)

	//  top = (lambda () (if cond (block ... body ... (continue)) (break)))
	env.breakVars.Push(breakVar)
	env.continueVars.Push(continueVar)
	bodyCalls := MakeCalls()
	body(env, bodyCalls)
	env.breakVars.Pop()
	env.continueVars.Pop()
	bodyCalls.BuildFinalCall("jump", 0, continueVar)
	calls.SetLastSource(position)
	if cond == nil {
		AttachNext(topLambda, bodyCalls.First)
	} else {
		breakCalls := MakeCalls()
		breakCalls.BuildFinalCall("jump", 0, breakVar)
		makeIf(cond, bodyCalls, breakCalls, nil, position, condCalls)
		AttachNext(topLambda, condCalls.First)
	}
}

// RangeStmt has:
//  Tok   token.Token  // Says whether the Key is assigned or defined.
//                     // One of ILLEGAL (Key is nil), ASSIGN, DEFINE
//  Key   Expr         // Can be nil.  An Ident if DEFINE, otherwise an
//                     // an assignable expression.
//  Value Expr         // Same as rules as Key.
//  X     Expr         // The thing to range over.
//  Body  *BlockStmt
// Basically, X gives the loop count and, if present, Key and/or Value get
// set to the iteration value, which is an integer except for tables, and
// the corresponding element of X.
//
// This doesn't handle Value yet, only Key.
//
// From the Go spec:
//   The iteration variables may be declared by the "range" clause
//   using a form of short variable declaration (:=). In this case
//   their scope is the block of the "for" statement and each
//   iteration has its own new variables
// We don't currently do this.

func cpsRangeLoop(rangeStmt *ast.RangeStmt, env *envT, calls *CallsT) {
	rangeVal := cpsExpr(rangeStmt.X, env, calls)[0]
	var keyLhs LhsT
	var valueLhs LhsT
	if rangeStmt.Tok == token.ILLEGAL {
		// We make an LHS with an unbound variable.
		keyVar := MakeVariable("key", types.Typ[types.Int], rangeStmt.For)
		keyVar.Flags["cell"] = true
		env.addMakeCell(keyVar)
		keyLhs = &PointerLhsT{"cellRef", "cellSet", keyVar, rangeStmt.For, true}
	} else {
		newOkay := rangeStmt.Tok == token.DEFINE
		keyLhs = cpsLhs(rangeStmt.Key, newOkay, env, calls)
		if rangeStmt.Value != nil {
			valueLhs = cpsLhs(rangeStmt.Value, newOkay, env, calls)
		}
	}
	// The loop runs from 0 to rangeLimit, and the values are from
	// indexPrimop(rangeVal, key).  Ranging over an integer has no values.
	rangeLimit := rangeVal
	indexPrimop := ""
	rangeType := env.typeInfo.Types[rangeStmt.X].Type
	_, isArrayPointer := arrayPointerElem(rangeType)
	rangeVal, rangeType = derefArrayPointer(rangeVal, rangeType, calls)
	switch rangeType := rangeType.Underlying().(type) {
	case *types.Slice:
		rangeLimit = MakeReferenceNode(calls.BuildCall("len", "len", types.Typ[types.Int], rangeVal))
		indexPrimop = "sliceIndex"
	case *types.Array:
		// The range expression is evaluated once, so a value variable
		// gets the elements of a copy of the array.  An array pointed
		// to is not copied.
		if valueLhs != nil && !isArrayPointer {
			rangeVal = freshAggregateCopy(rangeVal, rangeType, calls)
		}
		rangeLimit = MakeLiteral(big.NewInt(rangeType.Len()), types.Typ[types.Int])
		indexPrimop = "arrayIndex"
	}
	if valueLhs != nil && indexPrimop == "" {
		panic(fmt.Sprintf("range value over an unsupported type at %s", source(rangeStmt.X.Pos())))
	}
	keyLhs.write(MakeLiteral(big.NewInt(0), types.Typ[types.Int]), calls)
	body := func(env *envT, calls *CallsT) {
		if valueLhs != nil {
			// An aggregate element's address is its value; see PointerLhsT.
			valueType := valueLhs.valueType()
			if isAggregateType(valueType) {
				valueVar := MakeVariable("v", valueType)
				calls.BuildVarCall(indexPrimop, valueVar, CopyNodeTree(rangeVal), keyLhs.read(calls))
				valueLhs.write(MakeReferenceNode(valueVar), calls)
			} else {
				pointerVar := MakeVariable("v", types.NewPointer(valueType))
				calls.BuildVarCall(indexPrimop, pointerVar, CopyNodeTree(rangeVal), keyLhs.read(calls))
				// calls.SetLastSource(x.Lbrack)
				valueVar := MakeVariable("v", valueType)
				calls.BuildVarCall("pointerRef", valueVar, pointerVar)
				valueLhs.write(MakeReferenceNode(valueVar), calls)
			}
		}
		cpsStmt(rangeStmt.Body, env, calls)
	}
	post := MakeCalls()
	keyVal := keyLhs.read(post)
	keyVal = MakeReferenceNode(post.BuildCall("+", "keyval", keyVal.(*ReferenceNodeT).Variable.Type, keyVal, 1))
	post.SetLastSource(rangeStmt.Range)
	keyLhs.write(keyVal, post)
	post.SetLastSource(rangeStmt.Range)
	condCalls := MakeCalls()
	keyVal = keyLhs.read(condCalls)
	condVar := condCalls.BuildCall("<", "cond", types.Typ[types.Bool], keyVal, rangeLimit)
	condCalls.SetLastSource(rangeStmt.Range)
	makeForLoop(condCalls, MakeReferenceNode(condVar), body, post, rangeStmt.For, env, calls)
	if indexPrimop == "arrayIndex" {
		// The limit is a literal, so the loop has only used copies.
		Erase(rangeVal)
	}
}

// We don't do maps or anything compilicated, so we assume keys are
// ints.
func rangeStmtKeyType(rangeExp ast.Expr, env *envT) types.Type {
	return types.Typ[types.UntypedInt]
}

func makeIf(
	cond NodeT,
	trueCalls *CallsT,
	falseCalls *CallsT,
	joinLambda *CallNodeT,
	source token.Pos,
	calls *CallsT) {

	calls.BuildFinalCall("if", 2, trueCalls.First, falseCalls.First, cond)
	calls.SetLastSource(source)
	if joinLambda != nil {
		calls.SetLast(joinLambda)
	}
}

func makeBoolJump(joinVar *VariableT, value bool) *CallsT {
	calls := MakeCalls()
	calls.BuildFinalCall("jump", 0, joinVar, value)
	return calls
}

//----------------------------------------------------------------
// Expressions

// What Go says about the order of evaluation:
//
//   ..., when evaluating the operands of an expression, assignment, or
//   return statement, all function calls, method calls, and (channel)
//   communication operations are evaluated in lexical left-to-right order.
// Value conversions are not function calls, nor are references to variables.
// Given f(a, g(), h(b)) all we know is that:
//   g is evaluated before the call to g
//   h is evaluated before the call to h
//   b is evaluated before the call to h
//   the call to the value of g happens before the call to the value of h
// Other than that, f, a, g, h, and b can be evaluated in any order.

func cpsArguments(args []ast.Expr, env *envT, calls *CallsT) []NodeT {
	values := []NodeT{}
	for _, arg := range args {
		value := cpsExpr(arg, env, calls)
		if len(value) != 1 {
			panic(fmt.Sprintf("argument didn't return one value %v", arg))
		}
		values = append(values, value[0])
	}
	return values
}

func cleanExpr(astNode ast.Expr, env *envT) ast.Expr {
	astNode = ast.Unparen(astNode) // remove any parens
	switch x := astNode.(type) {
	case *ast.IndexExpr:
		// If this is a generic being applied to a type we ignore the
		// index.  The type checker has already taken it into account.
		if env.typeInfo.Types[x.Index].IsType() {
			return cleanExpr(x.X, env)
		}
	}
	return astNode
}

func cpsExpr(astNode ast.Expr, env *envT, calls *CallsT) []NodeT {
	astNode = cleanExpr(astNode, env) // remove any parens or type parameters
	switch x := astNode.(type) {
	case *ast.Ident:
		return []NodeT{cpsIdent(x, false, env, calls)}
	case *ast.BasicLit:
		if x.Kind == token.INT {
			n, success := new(big.Int).SetString(x.Value, 0)
			if !success {
				panic("could not parse '" + x.Value + "' as an integer")
			}
			return []NodeT{MakeLiteral(n, env.typeInfo.Types[x].Type)}
		} else {
			panic(fmt.Sprintf("unrecognized BasicLit type %v '%s' at %s",
				x.Kind, x.Value, source(x.Pos())))
		}
	case *ast.CompositeLit:
		inputs := cpsArguments(x.Elts, env, calls)
		return makeExprCall("makeLiteral", x.Lbrace, x, env, calls, inputs...)
	case *ast.UnaryExpr:
		op := x.Op.String()
		switch op {
		case "!":
			// works as-is
		case "-":
			op = "negate"
		case "^":
			op = "bitwiseNot"
		case "&":
			// &X is the location that cpsLhs(X) reads and writes.  An
			// aggregate's location is its data, which is also its
			// value (see PointerLhsT), so only the type changes.
			operand := ast.Unparen(x.X)
			operandType := env.typeInfo.Types[operand].Type
			if isAggregateType(operandType) {
				value := cpsLhs(operand, false, env, calls).read(calls)
				pointerVar := calls.BuildCall("aggregateToPointer", "v",
					types.NewPointer(operandType), value)
				calls.SetLastSource(x.OpPos)
				return []NodeT{MakeReferenceNode(pointerVar)}
			}
			switch operand := operand.(type) {
			case *ast.Ident:
				vart := env.lookupVar(operand)
				if vart != nil && vart.HasFlag("cell") {
					return []NodeT{MakeReferenceNode(vart)}
				}
			case *ast.IndexExpr, *ast.StarExpr:
				lhs := cpsLhs(operand, false, env, calls).(*PointerLhsT)
				return []NodeT{MakeReferenceNode(lhs.pointer)}
			}
			op = "addressOf" // disambiguate from binary '&'
		default:
			panic(fmt.Sprintf("unrecognized unary operator '%s' at %s", op, source(x.Pos())))
		}
		value := cpsArguments([]ast.Expr{x.X}, env, calls)[0]
		return makeExprCall(op, x.OpPos, x, env, calls, value)
	case *ast.BinaryExpr:
		if x.Op.String() == "&&" || x.Op.String() == "||" {
			return cpsAndOrExpr(x, env, calls)
		} else if x.Op.String() == "<=" || x.Op.String() == ">" {
			primop := ">="
			if x.Op.String() == ">" {
				primop = "<"
			}
			inputs := cpsArguments([]ast.Expr{x.Y, x.X}, env, calls)
			return makeExprCall(primop, x.OpPos, x, env, calls, inputs...)
		} else {
			inputs := cpsArguments([]ast.Expr{x.X, x.Y}, env, calls)
			return makeExprCall(x.Op.String(), x.OpPos, x, env, calls, inputs...)
		}
	case *ast.IndexExpr:
		return []NodeT{cpsLhs(x, false, env, calls).read(calls)}
	case *ast.CallExpr:
		return cpsCallExpr(x, env, calls)
	case *ast.ArrayType:
		// The type of the expression is the type expression.
		return []NodeT{MakeLiteral(nil, env.typeInfo.Types[x].Type)}
	case *ast.SliceExpr:
		slice := cpsArguments([]ast.Expr{x.X}, env, calls)[0]
		var low NodeT
		if x.Low == nil {
			low = MakeLiteral(big.NewInt(0), types.Typ[types.Int])
		} else {
			low = cpsArguments([]ast.Expr{x.Low}, env, calls)[0]
		}
		var high NodeT
		if x.High == nil {
			high = makeExprTypeCall("len", x.Rbrack, types.Typ[types.Int], env, calls, CopyNodeTree(slice))[0]
		} else {
			high = cpsArguments([]ast.Expr{x.High}, env, calls)[0]
		}
		size := makeExprTypeCall("-", x.Rbrack, types.Typ[types.Int], env, calls, high, CopyNodeTree(low))[0]
		pointerType := types.NewPointer(env.typeInfo.Types[x.X].Type)
		pointer := makeExprTypeCall("sliceIndex", x.Lbrack, pointerType, env, calls, slice, low)[0]
		return makeExprCall("makeSlice", x.Lbrack, x, env, calls, pointer, size)
	case *ast.FuncLit: // .Type *FuncType   .Body *BlockStmt
		return []NodeT{CpsFunc("@", x.Type, x.Body, env.typeInfo.Types[x].Type, env)}
	case *ast.SelectorExpr:
		// 'const' from another package
		typeAndValue := env.typeInfo.Types[x]
		if typeAndValue.IsValue() && typeAndValue.Value != nil {
			return []NodeT{MakeLiteral(typeAndValue.Value, typeAndValue.Type)}
		}
		// method call
		selection := env.typeInfo.Selections[x]
		if selection != nil {
			panic(fmt.Sprintf("have selection %s\n", selection))
		}
		panic(fmt.Sprintf("unhandled selector expression %s", source(x.Pos())))
	case *ast.StarExpr:
		pointer := cpsArguments([]ast.Expr{x.X}, env, calls)[0]
		pointerVar := pointer.(*ReferenceNodeT).Variable
		valueType := pointerVar.Type.(*types.Pointer).Elem()
		// A pointer to an aggregate is the aggregate's value (see
		// PointerLhsT), with a different type.
		primop := "pointerRef"
		if isAggregateType(valueType) {
			primop = "pointerToAggregate"
		}
		valueVar := calls.BuildCall(primop, pointerVar.Name, valueType, pointer)
		calls.SetLastSource(x.Star)
		return []NodeT{MakeReferenceNode(valueVar)}
	default:
		panic(fmt.Sprintf("unrecognized expression %T %s", astNode, source(astNode.Pos())))
	}
	return nil
}

func cpsIdent(ident *ast.Ident, isCalled bool, env *envT, calls *CallsT) NodeT {
	typeAndValue := env.typeInfo.Types[ident]
	if typeAndValue.IsValue() && typeAndValue.Value != nil {
		return MakeLiteral(typeAndValue.Value, typeAndValue.Type)
	}
	vart := env.lookupVar(ident)
	if vart == nil {
		// It's a Go built-in like 'len', 'make', or 'uint64' (in a
		// cast). We assume it's implemented by a primop.  Uses[ident]
		// is non-nil for source packages (e.g. vpu) and nil for
		// 'len'.  Defs[ident] is also nil for 'len'.  The 'builtin'
		// package has documentation for all of Go's builtin names,
		// but I can't find a programatic list anywhere.
		primop := LookupPrimop(ident.Name)
		if primop == nil {
			panic(fmt.Sprintf("unbound variable %s", ident.Name))
		}
		vart = MakeVariable(ident.Name, typeAndValue.Type, ident.Pos())
		vart.Flags["package"] = true
		vart.Flags["primop"] = primop
	}
	if vart.HasFlag("package") && len(vart.Refs) == 0 && vart.Flags["primop"] == nil {
		// The first reference to a package variable.  It may be a
		// function that needs to be converted.
		Push(&env.newPackageVars, vart)
	}
	if vart.HasFlag("package") {
		// 'var' variables always get "packageRef", 'func' ones do
		// if not being called.
		if vart.HasFlag("var") || !isCalled {
			vart = calls.BuildCall("packageRef", vart.Name, vart.Type, vart)
		}
	} else if vart.HasFlag("cell") {
		vart = calls.BuildCall("cellRef", vart.Name, vart.Type, vart)
	}
	return MakeReferenceNode(vart)
}

// && and || require conditionals because the second argument is
// evaluated only if the first is true (&&) or false (||).

func cpsAndOrExpr(binaryExpr *ast.BinaryExpr, env *envT, calls *CallsT) []NodeT {
	joinVar := MakeVariable("join", nil)
	valueVar := MakeVariable("v", types.Typ[types.Bool])
	joinLambda := MakeLambda("c", JumpLambda, []*VariableT{valueVar})
	calls.BuildVarCall("let", joinVar, joinLambda)

	secondIfTrue := makeBoolJump(joinVar, true)
	secondIfFalse := makeBoolJump(joinVar, false)
	secondIf := MakeCalls()
	xCond := cpsExpr(binaryExpr.X, env, calls)[0]
	yCond := cpsExpr(binaryExpr.Y, env, secondIf)[0]

	makeIf(yCond, secondIfTrue, secondIfFalse, nil, binaryExpr.OpPos, secondIf)

	if binaryExpr.Op.String() == "&&" {
		ifFalse := makeBoolJump(joinVar, false)
		makeIf(xCond, secondIf, ifFalse, nil, binaryExpr.OpPos, calls)
	} else {
		ifTrue := makeBoolJump(joinVar, true)
		makeIf(xCond, ifTrue, secondIf, nil, binaryExpr.OpPos, calls)
	}
	calls.SetLast(joinLambda)
	return []NodeT{MakeReferenceNode(valueVar)}
}

func cpsCallExpr(callExpr *ast.CallExpr, env *envT, calls *CallsT) []NodeT {
	// A call with a constant value, such as len(a) for an array 'a',
	// does not evaluate its arguments.
	typeAndValue := env.typeInfo.Types[callExpr]
	if typeAndValue.Value != nil {
		return []NodeT{MakeLiteral(typeAndValue.Value, typeAndValue.Type)}
	}
	length, isArrayLength := arrayLength(callExpr, env)
	if isArrayLength {
		// The argument contains a call, so it is evaluated for that.
		Erase(cpsExpr(callExpr.Args[0], env, calls)[0])
		return []NodeT{MakeLiteral(big.NewInt(length), types.Typ[types.Int])}
	}
	args := cpsArguments(callExpr.Args, env, calls)
	fun, object := cpsCalledExpr(callExpr.Fun, env, calls)
	if object != nil {
		args = append([]NodeT{object}, args...)
	}
	var resultTypes []types.Type
	switch resultType := env.typeInfo.Types[callExpr].Type.(type) {
	case *types.Tuple:
		for i := range resultType.Len() {
			resultTypes = append(resultTypes, resultType.At(i).Type())
		}
	default:
		resultTypes = []types.Type{resultType}
	}
	resultVars := make([]*VariableT, len(resultTypes))
	results := make([]NodeT, len(resultTypes))
	for i, typ := range resultTypes {
		resultVars[i] = MakeVariable("v", typ)
		results[i] = MakeReferenceNode(resultVars[i])
	}
	funVar := fun.(*ReferenceNodeT).Variable
	primop := funVar.Flags["primop"]
	if primop == nil {
		args = append([]NodeT{fun}, args...)
		primop = LookupPrimop("procCall")
	}
	calls.AddCall(primop.(PrimopT), resultVars, args)
	calls.SetLastSource(callExpr.Lparen)
	return results
}

// If this is a call to the builtin len or cap on an array or a pointer
// to an array, returns the array's length.
func arrayLength(callExpr *ast.CallExpr, env *envT) (int64, bool) {
	ident, isIdent := ast.Unparen(callExpr.Fun).(*ast.Ident)
	if !isIdent {
		return 0, false
	}
	builtin, isBuiltin := env.typeInfo.Uses[ident].(*types.Builtin)
	if !isBuiltin || (builtin.Name() != "len" && builtin.Name() != "cap") {
		return 0, false
	}
	typ := env.typeInfo.Types[callExpr.Args[0]].Type
	elem, isPointer := arrayPointerElem(typ)
	if isPointer {
		typ = elem
	}
	array, isArray := typ.Underlying().(*types.Array)
	if !isArray {
		return 0, false
	}
	return array.Len(), true
}

// Go lets a pointer to an array stand for the array when indexing,
// slicing, ranging, and in len and cap.  (Pointers to other types
// can't be used this way, as slices, maps, and strings already refer
// to their data.)  Returns the array type if 'typ' is a pointer to an
// array.
func arrayPointerElem(typ types.Type) (types.Type, bool) {
	pointer, isPointer := typ.Underlying().(*types.Pointer)
	if !isPointer {
		return nil, false
	}
	_, isArray := pointer.Elem().Underlying().(*types.Array)
	return pointer.Elem(), isArray
}

// If 'value', of type 'typ', is a pointer to an array, returns the
// array and its type.  Otherwise returns 'value' and 'typ'.
func derefArrayPointer(value NodeT, typ types.Type, calls *CallsT) (NodeT, types.Type) {
	elem, isPointer := arrayPointerElem(typ)
	if !isPointer {
		return value, typ
	}
	arrayVar := calls.BuildCall("pointerToAggregate", "v", elem, value)
	return MakeReferenceNode(arrayVar), elem
}

func cpsCalledExpr(expr ast.Expr, env *envT, calls *CallsT) (NodeT, NodeT) {
	expr = cleanExpr(expr, env) // remove any parens or type parameters
	switch x := expr.(type) {
	case *ast.Ident:
		return cpsIdent(x, true, env, calls), nil
	case *ast.SelectorExpr:
		// method call
		selection := env.typeInfo.Selections[x]
		if selection != nil {
			panic(fmt.Sprintf("have selection %s\n", selection))
		}
		switch base := x.X.(type) {
		case *ast.Ident:
			switch env.typeInfo.Uses[base].(type) {
			// non-const import from another package
			case *types.PkgName:
				return MakeReferenceNode(env.lookupVar(x.Sel)), nil
			}
		}
		vart := env.lookupObj(env.typeInfo.ObjectOf(x.Sel).(*types.Func).Origin())
		if vart == nil {
			panic(fmt.Sprintf("no binding for method %s", x.Sel.Name))
		}
		return MakeReferenceNode(vart), cpsExpr(x.X, env, calls)[0]
	}
	return cpsExpr(expr, env, calls)[0], nil
}

// Create a call to the primop and return a reference node bount to
// the output variable.

func makeExprCall(primop string,
	source token.Pos,
	expr ast.Expr,
	env *envT,
	calls *CallsT,
	inputs ...NodeT) []NodeT {

	return makeExprTypeCall(primop, source, env.typeInfo.Types[expr].Type, env, calls, inputs...)
}

func makeExprTypeCall(primop string,
	pos token.Pos,
	resultType types.Type,
	env *envT,
	calls *CallsT,
	inputs ...NodeT) []NodeT {

	result := MakeVariable("v", resultType)
	calls.AddPrimopVarsCall(primop, []*VariableT{result}, inputs...)
	calls.SetLastSource(pos)
	return []NodeT{MakeReferenceNode(result)}
}

//----------------------------------------------------------------
// Handling the Left-Hand Side of expressions.  For a LHS we may
// either be:
//  - getting the value
//  - setting the value
//  - both, for operators like += and ++

type LhsT interface {
	read(calls *CallsT) NodeT
	write(value NodeT, calls *CallsT)
	valueType() types.Type
}

// I know of three three kinds of LHS expressions: identifiers, index
// expressions (x[y]) and star expressions (*x).  For identifiers if
// newOkay is true this is a definition and a new variable can be created
// (I suspect this is a must).  Index expressions can be for arrays,
// slices, strings, and maps.  So far we only handle slices and arrays.

func cpsLhs(astNode ast.Expr, newOkay bool, env *envT, calls *CallsT) LhsT {
	astNode = ast.Unparen(astNode) // remove any parens
	switch x := astNode.(type) {
	case *ast.Ident:
		cellVar := env.lookupVar(x)
		isNew := false
		if cellVar == nil {
			if !newOkay {
				panic(fmt.Sprintf("unbound variable %s", x.Name))
			}
			cellVar = env.bindCellVar(x)
			isNew = true
		}
		if cellVar.HasFlag("cell") {
			return &PointerLhsT{"cellRef", "cellSet", cellVar, x.NamePos, isNew}
		} else if cellVar.HasFlag("package") {
			return &PointerLhsT{"packageRef", "packageSet", cellVar, x.NamePos, isNew}
		} else {
			panic("non-cell variable in LHS")
		}
	case *ast.IndexExpr:
		values := cpsArguments([]ast.Expr{x.X, x.Index}, env, calls)
		var xType types.Type
		values[0], xType = derefArrayPointer(values[0], env.typeInfo.Types[x.X].Type, calls)
		var indexPrimop string
		var elemType types.Type
		switch xType := xType.Underlying().(type) {
		case *types.Slice:
			indexPrimop = "sliceIndex"
			elemType = xType.Elem()
		case *types.Array:
			indexPrimop = "arrayIndex"
			elemType = xType.Elem()
		default:
			panic(fmt.Sprintf("Indexed LHS of unexpected type '%s' at %s",
				xType,
				source(astNode.Pos())))
		}
		// An aggregate element is stored in place, so its address is
		// its value; see PointerLhsT.
		readPrimop := "pointerRef"
		pointerType := types.Type(types.NewPointer(elemType))
		if isAggregateType(elemType) {
			readPrimop = ""
			pointerType = elemType
		}
		pointerVar := MakeVariable("v", pointerType)
		calls.BuildVarCall(indexPrimop, pointerVar, values[0], values[1])
		calls.SetLastSource(x.Lbrack)
		return &PointerLhsT{readPrimop, "pointerSet", pointerVar, x.Lbrack, false}
	case *ast.StarExpr:
		pointer := cpsExpr(x.X, env, calls)[0]
		pointerType := env.typeInfo.Types[x.X].Type
		valueType := pointerType.Underlying().(*types.Pointer).Elem()
		if isAggregateType(valueType) {
			// See the R-value case in cpsExpr.
			valueVar := MakeVariable("v", valueType)
			calls.BuildVarCall("pointerToAggregate", valueVar, pointer)
			calls.SetLastSource(x.Star)
			return &PointerLhsT{"", "pointerSet", valueVar, x.Star, false}
		}
		pointerVar := MakeVariable("v", pointerType)
		calls.BuildVarCall("let", pointerVar, pointer)
		return &PointerLhsT{"pointerRef", "pointerSet", pointerVar, x.Star, false}
	default:
		panic(fmt.Sprintf("unrecognized LHS %T %+v", astNode, astNode))
	}
	return nil
}

func assignCells(lhss []ast.Expr, values []NodeT, newOkay bool, env *envT, calls *CallsT) {
	if len(lhss) != len(values) {
		panic(fmt.Sprintf("wrong number of values in assignment %d != %d", len(lhss), len(values)))
	}
	for i, lhs := range lhss {
		switch x := lhs.(type) {
		case *ast.Ident:
			if x.Name == "_" {
				Erase(values[i])
				continue
			}
		}
		cpsLhs(lhs, newOkay, env, calls).write(values[i], calls)
	}
}

// An LHS where the location is a single variable, which so
// far is all of them.
//
// Aggregates (arrays and structs) are values in Go, but an aggregate
// value here is a reference to its data, so they are copied when
// stored.  Reading an aggregate gives a reference to it where it is,
// without copying it.  For a part of an aggregate that is itself an
// aggregate (a[i] when 'a' is an array of arrays) the reference is the
// part's address, which is what lets a[i][j] be an L-value.  Writing
// an aggregate copies it, into the one already in the location, or,
// for a new variable, into a new one.
type PointerLhsT struct {
	readPrimop  string // "" if 'pointer' is the value, for an aggregate part
	writePrimop string
	pointer     *VariableT
	source      token.Pos
	isNew       bool // the location is a variable being defined
}

func (lhs *PointerLhsT) read(calls *CallsT) NodeT {
	node := MakeReferenceNode(lhs.pointer)
	if lhs.readPrimop == "" {
		return node
	}
	valueVar := MakeVariable(lhs.pointer.Name, lhs.valueType())
	calls.BuildVarCall(lhs.readPrimop, valueVar, node)
	calls.SetLastSource(lhs.source)
	return MakeReferenceNode(valueVar)
}

func (lhs *PointerLhsT) write(value NodeT, calls *CallsT) {
	if isAggregateType(lhs.valueType()) {
		if lhs.isNew {
			value = freshAggregateCopy(value, lhs.valueType(), calls)
		} else {
			calls.BuildNoOutputCall("copyAggregate", lhs.read(calls), value)
			calls.SetLastSource(lhs.source)
			return
		}
	}
	calls.BuildNoOutputCall(lhs.writePrimop, lhs.pointer, value)
}

// Arrays and structs.
func isAggregateType(typ types.Type) bool {
	switch typ.Underlying().(type) {
	case *types.Array, *types.Struct:
		return true
	}
	return false
}

// If 'typ' is an aggregate type, returns a copy of 'value' in a new
// one, otherwise returns 'value'.
func freshAggregateCopy(value NodeT, typ types.Type, calls *CallsT) NodeT {
	if !isAggregateType(typ) {
		return value
	}
	copyVar := MakeVariable("v", typ)
	calls.BuildVarCall("new", copyVar)
	calls.BuildNoOutputCall("copyAggregate", copyVar, value)
	return MakeReferenceNode(copyVar)
}

// Hack forced by our not giving cells the pointer type that
// they really have.

func (lhs *PointerLhsT) valueType() types.Type {
	if lhs.readPrimop == "cellRef" || lhs.readPrimop == "packageRef" || lhs.readPrimop == "" {
		return lhs.pointer.Type
	} else {
		return lhs.pointer.Type.(*types.Pointer).Elem()
	}
}
