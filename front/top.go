// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Converting Go ASTs into CPS.

package front

import (
	"fmt"
	"go/ast"
	"go/build"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path"
	"path/filepath"
	"slices"

	"golang.org/x/tools/go/packages"

	. "github.com/s48/transform/cps"
	. "github.com/s48/transform/util"
)

// 'builtinPackage' means a package whose functions are implemented
// as primops.

type FrontEndT struct {
	Packages        []*PackageT // each pkg appears before all its imports
	BuiltinPackages []*PackageT
	FileSet         *token.FileSet
	TypesInfo       *types.Info

	defaultImporter types.ImporterFrom
	builtinPackages []string
	builtinDirs     SetT[string]
	packageMap      map[string]*PackageT
}

func MakeFrontEnd(builtinPackages []string) *FrontEndT {
	return &FrontEndT{
		defaultImporter: importer.Default().(types.ImporterFrom),
		builtinPackages: builtinPackages,
		builtinDirs:     NewSet[string](),
		packageMap:      map[string]*PackageT{},
		FileSet:         token.NewFileSet(),
		TypesInfo: &types.Info{
			Types:     map[ast.Expr]types.TypeAndValue{},
			Defs:      map[*ast.Ident]types.Object{},
			Uses:      map[*ast.Ident]types.Object{},
			Instances: map[*ast.Ident]types.Instance{}}}
}

// This our representation of a package, which contains both go/build
// and go/types packages.

type PackageT struct {
	PackagePath  string
	BuildPackage *build.Package
	AstFiles     []*ast.File
	TypesPackage *types.Package
	TypesChecker *types.Checker // in case someone wants to add more code
}

// Load a package for compilation, along with whatever it imports.

func (frontEnd *FrontEndT) LoadPackage(sourceDir string) {
	buildPkg, err := build.ImportDir(sourceDir, 0)
	if err != nil {
		panic(fmt.Sprintf("Error importing from directory '%s': %s", sourceDir, err))
	}
	if frontEnd.FindPackage(buildPkg.Name, buildPkg.Dir) != nil {
		return
	}
	frontEnd.addPackage(getPackagePath(sourceDir), buildPkg)
	frontEnd.loadImports(buildPkg)
}

func getPackagePath(directory string) string {
	mode := packages.NeedName
	fmt.Printf("load package %s\n", directory)
	packageConf := &packages.Config{Mode: mode, Dir: directory}
	pkgs, err := packages.Load(packageConf, directory)
	if err != nil {
		panic(err)
	}
	if 0 < packages.PrintErrors(pkgs) {
		panic("packages had errors")
	}
	return pkgs[0].PkgPath
}

func (frontEnd *FrontEndT) addPackage(pkgPath string, buildPkg *build.Package) {
	pkg := &PackageT{PackagePath: pkgPath, BuildPackage: buildPkg}
	fmt.Printf("Adding package %s from %s\n", buildPkg.Name, buildPkg.Dir)
	frontEnd.packageMap[buildPkg.Name+"#"+buildPkg.Dir] = pkg
	if slices.Contains(frontEnd.builtinPackages, pkgPath) {
		frontEnd.BuiltinPackages = append(frontEnd.BuiltinPackages, pkg)
		frontEnd.builtinDirs.Add(buildPkg.Dir)
	} else {
		frontEnd.Packages = append(frontEnd.Packages, pkg)
		frontEnd.loadImports(buildPkg)
	}
}

func (frontEnd *FrontEndT) loadImports(buildPkg *build.Package) {
	for _, imported := range buildPkg.Imports {
		sourceDir, pkg := frontEnd.findImportPackage(imported, buildPkg.Dir)
		if pkg == nil {
			importedPkg, err := build.ImportDir(sourceDir, 0)
			if err != nil {
				panic(fmt.Sprintf("Could not import package from '%s'", sourceDir))
			}
			frontEnd.addPackage(imported, importedPkg)
		}
	}
}

func (frontEnd *FrontEndT) FindPackage(packagePath string, sourceDir string) *PackageT {
	return frontEnd.packageMap[packagePath+"#"+sourceDir]
}

// Returns the source directory for the package and the package
// itself, if we have it.

func (frontEnd *FrontEndT) findImportPackage(packagePath string, importDir string) (string, *PackageT) {
	importDir, _ = filepath.Abs(importDir)
	context := build.Default
	context.Dir = importDir
	dirPkg, err := context.Import(packagePath, importDir, build.FindOnly)
	if err != nil {
		panic(fmt.Sprintf("Could not find package '%s' imported from '%s'", packagePath, importDir))
	}
	name := path.Base(packagePath)
	return dirPkg.Dir, frontEnd.packageMap[name+"#"+dirPkg.Dir]
}

//----------------------------------------------------------------
// These methods make this a types.Importer (old style) and a
// types.ImporterFrom (new style)

// They're supposed to call 'ImportFrom' instead.
func (frontEnd *FrontEndT) Import(path string) (*types.Package, error) {
	panic("Someone called FrontEndT's 'import' method")
}

// Returns the package for 'path' imported by a file in 'dir'.
// 'mode' is reserved for future use.
func (frontEnd *FrontEndT) ImportFrom(path string,
	importDir string,
	mode types.ImportMode) (*types.Package, error) {

	_, pkg := frontEnd.findImportPackage(path, importDir)
	if pkg != nil {
		return pkg.TypesPackage, nil
	} else if frontEnd.builtinDirs.Contains(importDir) {
		return frontEnd.defaultImporter.ImportFrom(path, importDir, mode)
	}
	panic(fmt.Sprintf("No package loaded for '%s' imported from '%s'", path, importDir))
}

//----------------------------------------------------------------

func (frontEnd *FrontEndT) ParseAndTypeCheck() {
	frontEnd.readFiles(frontEnd.BuiltinPackages)
	frontEnd.readFiles(frontEnd.Packages)
	conf := &types.Config{Importer: frontEnd}
	for _, pkg := range frontEnd.BuiltinPackages {
		frontEnd.typeCheckPackage(pkg, conf)
	}
	for _, pkg := range frontEnd.Packages {
		frontEnd.typeCheckPackage(pkg, conf)
	}
}

func (frontEnd *FrontEndT) readFiles(pkgs []*PackageT) {
	for _, pkg := range pkgs {
		for _, file := range pkg.BuildPackage.GoFiles {
			file = pkg.BuildPackage.Dir + "/" + file
			contents, err := os.ReadFile(file)
			if err != nil {
				if os.IsNotExist(err) {
					panic(fmt.Sprintf("%s: File not found.\n", file))
				} else {
					panic(fmt.Sprintf("Error reading file '%s': %v", file, err))
				}
			}
			fmt.Printf("Read file '%s'.\n", file)
			astFile := frontEnd.ParseFile(file, contents)
			pkg.AstFiles = append(pkg.AstFiles, astFile)
		}
	}
}

func (frontEnd *FrontEndT) ParseFile(filename string, contents []byte) *ast.File {
	// As recommended in the docs, we skip the old, pre-Generic type checking.
	parseOpts := parser.SkipObjectResolution | parser.ParseComments
	astFile, err := parser.ParseFile(frontEnd.FileSet, filename, contents, parseOpts)
	if err != nil {
		panic(err)
	}
	return astFile
}

func (frontEnd *FrontEndT) typeCheckPackage(pkg *PackageT, conf *types.Config) {
	if pkg.TypesPackage != nil {
		return
	}
	// Imports must be checked first.
	for _, imported := range pkg.BuildPackage.Imports {
		_, pkg := frontEnd.findImportPackage(imported, pkg.BuildPackage.Dir)
		if pkg != nil {
			frontEnd.typeCheckPackage(pkg, conf)
		}
	}
	typesPackage, err :=
		conf.Check(pkg.PackagePath, frontEnd.FileSet, pkg.AstFiles, frontEnd.TypesInfo)
	if err != nil {
		panic(err)
	}
	pkg.TypesPackage = typesPackage
	// So any added code can be type checked.
	pkg.TypesChecker =
		types.NewChecker(conf, frontEnd.FileSet, typesPackage, frontEnd.TypesInfo)
}

// ----------------------------------------------------------------

func ConvertFuncDecl(decl *ast.FuncDecl, env *envT) *CallNodeT {
	return CpsFunc(decl.Name.Name,
		decl.Type,
		decl.Body,
		env.typeInfo.Defs[decl.Name].Type(),
		env)
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

// Convert a token position to a file and line number
func source(pos token.Pos) string {
	return TheFileSet.Position(pos).String()
}

// Handy debugging utility.

func printAst(tag string, node any) {
	fmt.Printf("%s\n", tag)
	ast.Fprint(os.Stdout, nil, node, nil)
}
