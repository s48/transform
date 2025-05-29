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
	packageBindings PackageBindingsT
	// types.Obj -> lexically-bound variable
	bindings BindingsT
	// For adding 'makeCell' calls at the beginning.
	currentBlock util.StackT[*CallsT]

	// Variables bound to 'continue' and 'break' continuations.  There
	// are stacks with the current values on top, for 'break' and
	// 'continuation' statements without labels, and binding tables
	// for those with labels.
	continueVars util.StackT[*VariableT]
	breakVars    util.StackT[*VariableT]
	// These are not yet in use.
	continueBindings BindingsT
	breakBindings    BindingsT
}

type BindingsT map[types.Object]*VariableT

func BindIdent(bindings BindingsT, ident *ast.Ident, typeInfo *types.Info) *VariableT {
	obj := typeInfo.ObjectOf(ident)
	if obj == nil {
		panic("no type object for identifier '" + ident.Name + "'")
	}
	vart := MakeVariable(ident.Name, obj.Type(), ident.Pos())
	bindings[obj] = vart
	return vart
}

type PackageBindingsT interface {
	LookupVar(obj types.Object) *VariableT
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

func MakeEnv(typeInfo *types.Info, pkgBindings PackageBindingsT) *envT {
	return &envT{
		typeInfo:         typeInfo,
		packageBindings:  pkgBindings,
		bindings:         BindingsT{},
		continueBindings: BindingsT{},
		breakBindings:    BindingsT{}}
}

func (env *envT) bindVar(ident *ast.Ident) *VariableT {
	return BindIdent(env.bindings, ident, env.typeInfo)
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
	return env.packageBindings.LookupVar(obj)
}

//----------------------------------------------------------------

func CpsFunc(name string, funcType *ast.FuncType, body *ast.BlockStmt, typ types.Type, env *envT) *CallNodeT {
	contVar := MakeVariable("c", typ.(*types.Signature).Results())
	env.returnVars.Push(contVar)
	calls := MakeCalls()
	env.currentBlock.Push(calls)
	vars := makeFieldVars(funcType.Params.List, env, calls)
	if funcType.Results != nil {
		vars = append(vars, makeFieldVars(funcType.Results.List, env, calls)...)
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

// Make the variables for a procedures arguments and returns.
func makeFieldVars(fields []*ast.Field, env *envT, calls *CallsT) []*VariableT {
	vars := []*VariableT{}
	for _, field := range fields {
		for _, ident := range field.Names {
			paramVarType := env.typeInfo.Defs[ident].Type() // .Underlying()
			paramVar := MakeVariable(ident.Name, paramVarType)
			vars = append(vars, paramVar)
			cellVar := env.bindCellVar(ident)
			calls.BuildNoOutputCall("cellSet", cellVar, paramVar)
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
						var value NodeT
						if spec.Values == nil {
							value = MakeLiteral(big.NewInt(0), cellVar.Type)
						} else {
							value = values[i]
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
		// Use Map to convert []NodeT to []Any to satisfy Go's type checking.
		values := Map(func(x NodeT) any { return x }, cpsArguments(x.Results, env, calls))
		values = append([]any{env.returnVars.Top()}, values...)
		calls.BuildFinalCall("return", 0, values...)
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
			// case token.FALLTHROUGH:
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
		makeIf(cond, trueCalls, falseCalls, nil, x.If, env, calls)
	} else {
		joinLambda := MakeLambda("c", JumpLambda, nil)
		calls.BuildVarCall("let", joinVar, joinLambda)
		makeIf(cond, trueCalls, falseCalls, joinLambda, x.If, env, calls)
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
	calls.SetLast(breakLambda)

	// continue = (lambda () ... post... (top))
	post.BuildFinalCall("jump", 0, topVar)
	AttachNext(continueLambda, post.First)

	//  top = (lambda () (if cond (block ... body ... (continue)) (break)))
	env.breakVars.Push(breakVar)
	env.continueVars.Push(continueVar)
	bodyCalls := MakeCalls()
	body(env, bodyCalls)
	env.breakVars.Pop()
	env.continueVars.Pop()
	bodyCalls.BuildFinalCall("jump", 0, continueVar)
	if cond == nil {
		AttachNext(topLambda, bodyCalls.First)
	} else {
		breakCalls := MakeCalls()
		breakCalls.BuildFinalCall("jump", 0, breakVar)
		makeIf(cond, bodyCalls, breakCalls, nil, position, env, condCalls)
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
	rangeLimit := rangeVal
	if rangeVal.NodeType() == ReferenceNode {
		rangeVar := rangeVal.(*ReferenceNodeT).Variable
		switch rangeVar.Type.(type) {
		case *types.Slice:
			rangeLimit = MakeReferenceNode(calls.BuildCall("len", "len", types.Typ[types.Int], rangeVal))
		}
	}
	var keyLhs LhsT
	var valueLhs LhsT
	if rangeStmt.Tok == token.ILLEGAL {
		// We make an LHS with an unbound variable.
		keyVar := MakeVariable("key", types.Typ[types.Int], rangeStmt.For)
		keyVar.Flags["cell"] = true
		env.addMakeCell(keyVar)
		keyLhs = &PointerLhsT{"cellRef", "cellSet", keyVar, rangeStmt.For}
	} else {
		newOkay := rangeStmt.Tok == token.DEFINE
		keyLhs = cpsLhs(rangeStmt.Key, newOkay, env, calls)
		if rangeStmt.Value != nil {
			valueLhs = cpsLhs(rangeStmt.Value, newOkay, env, calls)
		}
	}
	keyLhs.write(MakeLiteral(big.NewInt(0), types.Typ[types.Int]), calls)
	body := func(env *envT, calls *CallsT) {
		if valueLhs != nil {
			pointerVar := MakeVariable("v", types.NewPointer(valueLhs.valueType()))
			calls.BuildVarCall("sliceIndex", pointerVar, CopyNodeTree(rangeVal), keyLhs.read(calls))
			// calls.SetLastSource(x.Lbrack)
			valueVar := MakeVariable("v", valueLhs.valueType())
			calls.BuildVarCall("pointerRef", valueVar, pointerVar)
			valueLhs.write(MakeReferenceNode(valueVar), calls)
		}
		cpsStmt(rangeStmt.Body, env, calls)
	}
	post := MakeCalls()
	keyVal := keyLhs.read(post)
	keyVal = MakeReferenceNode(post.BuildCall("+", "keyval", keyVal.(*ReferenceNodeT).Variable.Type, keyVal, 1))
	keyLhs.write(keyVal, post)
	post.SetLastSource(rangeStmt.Range)
	condCalls := MakeCalls()
	keyVal = keyLhs.read(condCalls)
	condVar := condCalls.BuildCall("<", "cond", types.Typ[types.Bool], keyVal, rangeLimit)
	condCalls.SetLastSource(rangeStmt.Range)
	makeForLoop(condCalls, MakeReferenceNode(condVar), body, post, rangeStmt.For, env, calls)
}

// We don't do maps or anything compilicated, so we assume keys are
// ints.
func rangeStmtKeyType(rangeExp ast.Expr, env *envT) types.Type {
	return types.Typ[types.UntypedInt]
}

func makeIf(cond NodeT,
	trueCalls *CallsT, falseCalls *CallsT,
	joinLambda *CallNodeT,
	source token.Pos,
	env *envT, calls *CallsT) {

	if joinLambda == nil {
		calls.BuildFinalCall("if", 2, trueCalls.First, falseCalls.First, cond)
		calls.SetLastSource(source)
	} else {
		calls.BuildFinalCall("if", 2, trueCalls.First, falseCalls.First, cond)
		calls.SetLastSource(source)
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
			panic(fmt.Sprintf("unrecognized BasicLit type"))
		}
	case *ast.CompositeLit:
		inputs := cpsArguments(x.Elts, env, calls)
		return makeExprCall("makeLiteral", x.Lbrace, x, env, calls, inputs...)
	case *ast.UnaryExpr:
		value := cpsArguments([]ast.Expr{x.X}, env, calls)[0]
		op := x.Op.String()
		if op == "&" {
			op = "addressOf" // disambiguate from binary '&'
		}
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

	makeIf(yCond, secondIfTrue, secondIfFalse, nil, binaryExpr.OpPos, env, secondIf)

	if binaryExpr.Op.String() == "&&" {
		ifFalse := makeBoolJump(joinVar, false)
		makeIf(xCond, secondIf, ifFalse, nil, binaryExpr.OpPos, env, calls)
	} else {
		ifTrue := makeBoolJump(joinVar, true)
		makeIf(xCond, ifTrue, secondIf, nil, binaryExpr.OpPos, env, calls)
	}
	calls.SetLast(joinLambda)
	return []NodeT{MakeReferenceNode(valueVar)}
}

func cpsCallExpr(callExpr *ast.CallExpr, env *envT, calls *CallsT) []NodeT {
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
			default:
				// Method dispatch.
				vart := env.lookupObj(env.typeInfo.ObjectOf(x.Sel).(*types.Func).Origin())
				if vart == nil {
					panic(fmt.Sprintf("no binding for method %s.%s", base.Name, x.Sel.Name))
				}
				return MakeReferenceNode(vart), cpsExpr(x.X, env, calls)[0]
			}
		}
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
	source token.Pos,
	resultType types.Type,
	env *envT,
	calls *CallsT,
	inputs ...NodeT) []NodeT {

	result := MakeVariable("v", resultType)
	calls.AddPrimopVarsCall(primop, []*VariableT{result}, inputs...)
	calls.SetLastSource(source)
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
// slices, strings, and maps.  So far we only handle slices. and don't
// handle star expressions.

func cpsLhs(astNode ast.Expr, newOkay bool, env *envT, calls *CallsT) LhsT {
	astNode = ast.Unparen(astNode) // remove any parens
	switch x := astNode.(type) {
	case *ast.Ident:
		cellVar := env.lookupVar(x)
		if cellVar == nil {
			if !newOkay {
				panic(fmt.Sprintf("unbound variable %s", x.Name))
			}
			cellVar = env.bindCellVar(x)
		}
		if cellVar.HasFlag("cell") {
			return &PointerLhsT{"cellRef", "cellSet", cellVar, x.NamePos}
		} else {
			panic("non-cell variable in LHS")
		}
	case *ast.IndexExpr:
		values := cpsArguments([]ast.Expr{x.X, x.Index}, env, calls)
		typeAndValue := env.typeInfo.Types[x.X]
		switch xType := typeAndValue.Type.Underlying().(type) {
		case *types.Slice:
			pointerVar := MakeVariable("v", types.NewPointer(xType.Elem()))
			calls.BuildVarCall("sliceIndex", pointerVar, values[0], values[1])
			calls.SetLastSource(x.Lbrack)
			return &PointerLhsT{"pointerRef", "PointerSet", pointerVar, x.Lbrack}
		default:
			panic("Indexed LHS of unexpected type at " + source(astNode.Pos()))
		}
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
		cpsLhs(lhs, newOkay, env, calls).write(values[i], calls)
	}
}

// An LHS where the location is a single variable, which so
// far is all of them.
type PointerLhsT struct {
	readPrimop  string
	writePrimop string
	pointer     *VariableT
	source      token.Pos
}

func (lhs *PointerLhsT) read(calls *CallsT) NodeT {
	node := MakeReferenceNode(lhs.pointer)
	valueVar := MakeVariable(lhs.pointer.Name, lhs.valueType())
	calls.BuildVarCall(lhs.readPrimop, valueVar, node)
	calls.SetLastSource(lhs.source)
	return MakeReferenceNode(valueVar)
}

func (lhs *PointerLhsT) write(value NodeT, calls *CallsT) {
	calls.BuildNoOutputCall(lhs.writePrimop, lhs.pointer, value)
}

// Hack forced by our not giving cells the pointer type that
// they really have.

func (lhs *PointerLhsT) valueType() types.Type {
	if lhs.readPrimop == "cellRef" {
		return lhs.pointer.Type
	} else {
		return lhs.pointer.Type.(*types.Pointer).Elem()
	}
}
