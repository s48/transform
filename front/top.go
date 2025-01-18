// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Converting Go ASTs into CPS.

package front

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"os"

	. "github.com/s48/transform/cps"
	"golang.org/x/tools/go/packages"
)

type ParsedFileT struct {
	AstFile   *ast.File
	Packages  []*packages.Package
	TypesInfo *types.Info
	FileSet   *token.FileSet
}

func ParseFile(fileName string,
	fileContents []byte,
	directory string,
	packagePath string) *ParsedFileT {

	fileSet := token.NewFileSet()
	// As recommended in the docs, we skip the old, pre-Generic type checking.
	file, err := parser.ParseFile(fileSet,
		fileName,
		fileContents,
		parser.SkipObjectResolution)
	if err != nil {
		panic(err)
	}

	mode := packages.LoadTypes |
		packages.NeedFiles |
		packages.NeedSyntax |
		packages.NeedTypesInfo
	packageConf := &packages.Config{Mode: mode, Dir: directory}
	peckages, err := packages.Load(packageConf, packagePath)
	if err != nil {
		panic(err) // failed to load anything
	}
	if 0 < packages.PrintErrors(peckages) {
		panic("packages had errors")
	}

	imports := importsT{packages: map[string]*types.Package{}}
	for _, peckage := range peckages {
		// fmt.Printf("have package '%s'\n", peckage.PkgPath)
		imports.packages[peckage.PkgPath] = peckage.Types
	}

	// Actual type checking.
	conf := types.Config{Importer: imports}
	typeInfo := types.Info{
		Types:     map[ast.Expr]types.TypeAndValue{},
		Defs:      map[*ast.Ident]types.Object{},
		Uses:      map[*ast.Ident]types.Object{},
		Instances: map[*ast.Ident]types.Instance{},
	}
	_, err = conf.Check("app", fileSet, []*ast.File{file}, &typeInfo)
	if err != nil {
		panic(err)
	}

	// ast.Fprint(os.Stdout, nil, file.Decls[0], nil)

	return &ParsedFileT{file, peckages, &typeInfo, fileSet}
}

// This implements the type.Importer interface.

type importsT struct {
	packages map[string]*types.Package
}

func (imports importsT) Import(path string) (*types.Package, error) {
	peckage := imports.packages[path]
	if peckage == nil {
		panic("Package '" + path + "' not found")
		return nil, nil
	} else {
		return peckage, nil
	}
}

// ----------------------------------------------------------------

// Convert a token position to a file and line number
func source(pos token.Pos) string {
	return TheFileSet.Position(pos).String()
}

func MakeTopLevelForm(decl *ast.FuncDecl, parsedFile *ParsedFileT, globals BindingsT) *CallNodeT {
	TheFileSet = parsedFile.FileSet
	contVar := MakeVariable("c", nil)
	env := makeEnv(contVar, parsedFile.TypesInfo, globals)
	calls := MakeCalls()
	env.currentBlock.Push(calls)
	vars := append(makeFieldVars(decl.Type.Params.List, env, calls),
		makeFieldVars(decl.Type.Results.List, env, calls)...)
	vars = append([]*VariableT{contVar}, vars...)
	lambda := MakeLambda(decl.Name.Name, ProcLambda, vars)
	TopLambda = lambda
	cpsStmt(decl.Body, env, calls)
	env.currentBlock.Pop()
	calls.AddFirst(lambda)
	CheckNode(lambda)
	return lambda
}

func SimplifyTopLevel(lambda *CallNodeT) {
	CheckNode(lambda)
	TopLambda = lambda
	SimplifyNext(lambda)
	CheckNode(lambda)

	// Put cell variables in SSA form.
	SimplifyCells(lambda)
	CheckNode(lambda)

	// Clean up - this may not be necessary here.
	SimplifyNext(lambda)
	CheckNode(lambda)

	// Removing any unused inputs to jump lambdas.
	RemoveUnusedInputs(lambda)
	CheckNode(lambda)

	/*
		blocks := FindBasicBlocks[*BlockT](lambda, MakeBlock)
		for _, block := range blocks {
			fmt.Printf("%s_%d:", block.Start.Name, block.Start.Id)
			for _, prev := range block.Previous {
				fmt.Printf(" %s_%d", prev.Start.Name, prev.Start.Id)
			}
			fmt.Printf("\n")
		}
	*/
}

// Handy debugging utility.

func printAst(tag string, node any) {
	fmt.Printf("%s\n", tag)
	ast.Fprint(os.Stdout, nil, node, nil)
}
