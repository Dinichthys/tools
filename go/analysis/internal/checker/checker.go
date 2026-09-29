// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package internal/checker defines various implementation helpers for
// the singlechecker and multichecker packages, which provide the
// complete main function for an analysis driver executable
// based on go/packages.
//
// (Note: it is not used by the public 'checker' package, since the
// latter provides a set of pure functions for use as building blocks.)
package checker

// TODO(adonovan): publish the JSON schema in go/analysis or analysisjson.

import (
	"flag"
	"fmt"
	"io"
	"log"
	"os"
	"runtime"
	"runtime/debug"
	"runtime/pprof"
	"runtime/trace"
	"sort"
	"strings"
	"time"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/checker"
	"golang.org/x/tools/go/analysis/internal"
	"golang.org/x/tools/go/analysis/internal/analysisflags"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/internal/analysis/driverutil"
)

var (
	// Debug is a set of single-letter flags:
	//
	//	f	show [f]acts as they are created
	// 	p	disable [p]arallel execution of analyzers
	//	s	do additional [s]anity checks on fact types and serialization
	//	t	show [t]iming info (NB: use 'p' flag to avoid GC/scheduler noise)
	//	v	show [v]erbose logging
	//
	Debug = ""

	// Log files for optional performance tracing.
	CPUProfile, MemProfile, Trace string

	// IncludeTests indicates whether test files should be analyzed too.
	IncludeTests = true
)

// RegisterFlags registers command-line flags used by the analysis driver.
func RegisterFlags() {
	// When adding flags here, remember to update
	// the list of suppressed flags in analysisflags.

	flag.StringVar(&Debug, "debug", Debug, `debug flags, any subset of "fpstv"`)

	flag.StringVar(&CPUProfile, "cpuprofile", "", "write CPU profile to this file")
	flag.StringVar(&MemProfile, "memprofile", "", "write memory profile to this file")
	flag.StringVar(&Trace, "trace", "", "write trace log to this file")
	flag.BoolVar(&IncludeTests, "test", IncludeTests, "indicates whether test files should be analyzed, too")
}

// Run loads the packages specified by args using go/packages,
// then applies the specified analyzers to them.
// Analysis flags must already have been set.
// Analyzers must be valid according to [analysis.Validate].
// It provides most of the logic for the main functions of both the
// singlechecker and the multi-analysis commands.
// It returns the appropriate exit code.
//
// TODO(adonovan): tests should not call this function directly.
// Fiddling with global variables (flags such as [analysisflags.Fix])
// is error-prone and hostile to parallelism. Instead, use unit tests
// of the actual units (e.g. checker.Analyze) and integration tests
// (e.g. TestScript) of whole executables.
func Run(args []string, analyzers []*analysis.Analyzer) (exitcode int) {
	// Instead of returning a code directly,
	// call this function to monotonically increase the exit code.
	// This allows us to keep going in the face of some errors
	// without having to remember what code to return.
	//
	// TODO(adonovan): interpreting exit codes is like reading tea-leaves.
	// Instead of wasting effort trying to encode a multidimensional result
	// into 7 bits we should just emit structured JSON output, and
	// an exit code of 0 or 1 for success or failure.
	exitAtLeast := func(code int) {
		exitcode = max(code, exitcode)
	}

	// Since analysisflags is linked in (for {single,multi}checker),
	// the -v flag is registered for complex legacy reasons
	// related to cmd/vet CLI.
	// Treat it as an undocumented alias for -debug=v.
	if v := flag.CommandLine.Lookup("v"); v != nil &&
		v.Value.(flag.Getter).Get() == true &&
		!strings.Contains(Debug, "v") {
		Debug += "v"
	}

	if CPUProfile != "" {
		f, err := os.Create(CPUProfile)
		if err != nil {
			log.Fatal(err)
		}
		if err := pprof.StartCPUProfile(f); err != nil {
			log.Fatal(err)
		}
		// NB: profile won't be written in case of error.
		defer pprof.StopCPUProfile()
	}

	if Trace != "" {
		f, err := os.Create(Trace)
		if err != nil {
			log.Fatal(err)
		}
		if err := trace.Start(f); err != nil {
			log.Fatal(err)
		}
		// NB: trace log won't be written in case of error.
		defer func() {
			trace.Stop()
			log.Printf("To view the trace, run:\n$ go tool trace view %s", Trace)
		}()
	}

	if MemProfile != "" {
		f, err := os.Create(MemProfile)
		if err != nil {
			log.Fatal(err)
		}
		// NB: memprofile won't be written in case of error.
		defer func() {
			runtime.GC() // get up-to-date statistics
			if err := pprof.WriteHeapProfile(f); err != nil {
				log.Fatalf("Writing memory profile: %v", err)
			}
			f.Close()
		}()
	}

	// Load the packages.
	if dbg('v') {
		log.SetPrefix("")
		log.SetFlags(log.Lmicroseconds) // display timing
		log.Printf("load %s", args)
	}

	// Analyzers that don't use facts can analyze packages independently.
	// First discover the dependency graph without syntax, then load and
	// analyze each package using LoadSyntax. This bounds the number of
	// typed syntax trees simultaneously resident in memory.
	//
	// JSON must be emitted as one document, so retain the existing
	// all-at-once implementation for that mode.
	if !needFacts(analyzers) && !analysisflags.JSON {
		return runBatched(args, analyzers)
	}

	// Analyzers that use facts require a single dependency action graph
	// and consistent go/types object identities.
	initial, err := load(args, true)
	if err != nil {
		log.Print(err)
		exitAtLeast(1)
		return
	}

	initial = collectDeps(initial)

	// Print package and module errors regardless of RunDespiteErrors.
	// Do not exit if there are errors, yet.
	if n := packages.PrintErrors(initial); n > 0 {
		exitAtLeast(1)
	}

	var factLog io.Writer
	if dbg('f') {
		factLog = os.Stderr
	}

	// Run the analysis.
	opts := &checker.Options{
		SanityCheck: dbg('s'),
		Sequential:  dbg('p'),
		FactLog:     factLog,
	}
	if dbg('v') {
		log.Printf("building graph of analysis passes")
	}
	graph, err := checker.Analyze(analyzers, initial, opts)
	if err != nil {
		log.Print(err)
		exitAtLeast(1)
		return
	}

	// Don't print the diagnostics,
	// but apply all fixes from the root actions.
	if analysisflags.Fix {
		if err := applyGraphFixes(graph); err != nil {
			// Fail when applying fixes failed.
			log.Print(err)
			exitAtLeast(1)
			return
		}
		// Don't proceed to print text/JSON,
		// and don't report an error
		// just because there were diagnostics.
		return
	}

	// Print the results. If !RunDespiteErrors and there
	// are errors in the packages, this will have 0 exit
	// code. Otherwise, we prefer to return exit code
	// indicating diagnostics.
	exitAtLeast(printDiagnostics(graph))

	return
}

// runBatched analyzes all non-standard-library packages in the transitive
// dependency graph of patterns without retaining typed syntax for the entire
// graph at once.
//
// It must only be used when none of the analyzers uses facts. Facts contain
// go/types objects whose identities must be shared across package actions.
func runBatched(patterns []string, analyzers []*analysis.Analyzer) (exitcode int) {
	exitAtLeast := func(code int) {
		exitcode = max(code, exitcode)
	}

	// Discover the complete package graph without parsing or type-checking
	// source files. NeedForTest lets collectDependencyPaths distinguish
	// ordinary packages from synthetic test variants.
	const metaMode = packages.NeedName |
		packages.NeedImports |
		packages.NeedDeps |
		packages.NeedModule |
		packages.NeedForTest

	meta, err := packages.Load(&packages.Config{
		Mode:  metaMode,
		Tests: IncludeTests,
	}, patterns...)
	if err != nil {
		log.Print(err)
		return 1
	}
	if len(meta) == 0 {
		log.Printf("%s matched no packages", strings.Join(patterns, " "))
		return 1
	}

	if n := packages.PrintErrors(meta); n > 0 {
		exitAtLeast(1)
	}

	packagePaths := collectDependencyPaths(meta)
	if len(packagePaths) == 0 {
		log.Printf("%s matched no module packages", strings.Join(patterns, " "))
		return 1
	}

	// Only the package path strings are needed from this point onwards.
	// Release the metadata graph before loading syntax.
	meta = nil
	debug.FreeOSMemory()

	var factLog io.Writer
	if dbg('f') {
		factLog = os.Stderr
	}

	opts := &checker.Options{
		SanityCheck: dbg('s'),
		Sequential:  dbg('p'),
		FactLog:     factLog,
	}

	// One package path per batch gives the lowest peak RSS. Loading a package
	// with Tests enabled may still return its primary and test variants, which
	// must remain together so their duplicate diagnostics/fixes can be merged.
	const batchSize = 1

	for start := 0; start < len(packagePaths); start += batchSize {
		end := min(start+batchSize, len(packagePaths))
		batch := packagePaths[start:end]

		if dbg('v') {
			log.Printf(
				"load syntax batch %d/%d: %s",
				start/batchSize+1,
				(len(packagePaths)+batchSize-1)/batchSize,
				strings.Join(batch, " "),
			)
		}

		// LoadSyntax parses and type-checks only packages named by batch.
		// Their dependencies are represented using export data, without ASTs.
		pkgs, err := packages.Load(&packages.Config{
			Mode:  packages.LoadSyntax | packages.NeedModule,
			Tests: IncludeTests,
		}, batch...)
		if err != nil {
			log.Print(err)
			exitAtLeast(1)
			continue
		}
		if len(pkgs) == 0 {
			log.Printf("%s matched no packages", strings.Join(batch, " "))
			exitAtLeast(1)
			continue
		}

		if n := packages.PrintErrors(pkgs); n > 0 {
			exitAtLeast(1)
		}

		graph, err := checker.Analyze(analyzers, pkgs, opts)
		if err != nil {
			log.Print(err)
			exitAtLeast(1)

			pkgs = nil
			debug.FreeOSMemory()
			continue
		}

		if analysisflags.Fix {
			// Apply fixes before releasing the batch. ApplyFixes needs the
			// package syntax, type package, FileSet, and Pass.ReadFile.
			if err := applyGraphFixes(graph); err != nil {
				log.Print(err)
				exitAtLeast(1)

				graph = nil
				pkgs = nil
				debug.FreeOSMemory()
				return exitcode
			}
		} else {
			exitAtLeast(printDiagnostics(graph))
		}

		// Nothing outside this iteration retains graph or pkgs. The Go GC
		// can collect Action/Pass cycles, analyzer results, syntax trees,
		// types.Info maps, facts, and package type information.
		graph = nil
		pkgs = nil

		// This mode prioritizes bounded RSS over throughput. FreeOSMemory
		// performs a GC and asks the scavenger to return unused pages to
		// the operating system before loading the next package.
		debug.FreeOSMemory()
	}

	return exitcode
}

// applyGraphFixes applies all suggested fixes from graph.
//
// The graph and its packages must remain alive until this function returns:
// ApplyFixes uses Package.Types, Package.Syntax, Package.Fset, and
// analysis.Pass.ReadFile.
func applyGraphFixes(graph *checker.Graph) error {
	fixActions := make([]driverutil.FixAction, 0, len(graph.Roots))

	for _, act := range graph.Roots {
		pass := internal.ActionPass(act)
		if pass == nil {
			continue
		}

		fixActions = append(fixActions, driverutil.FixAction{
			Name:         act.String(),
			Pkg:          act.Package.Types,
			Files:        act.Package.Syntax,
			FileSet:      act.Package.Fset,
			ReadFileFunc: pass.ReadFile,
			Diagnostics:  act.Diagnostics,
		})
	}

	write := func(filename string, content []byte) error {
		return os.WriteFile(filename, content, 0644)
	}

	return driverutil.ApplyFixes(
		fixActions,
		write,
		analysisflags.Diff,
		dbg('v'),
	)
}

// collectDependencyPaths returns importable package paths in deterministic,
// dependency-first order.
//
// Packages without Module information are excluded. This matches the existing
// collectDeps behavior and prevents the standard library from being analyzed.
//
// Synthetic test variants are not returned as separate patterns. Loading the
// corresponding ordinary package with Tests enabled recreates those variants.
// Dependencies used only by tests are still reached while traversing Imports.
func collectDependencyPaths(roots []*packages.Package) []string {
	seenID := make(map[string]bool)
	seenPath := make(map[string]bool)
	var result []string

	var visit func(*packages.Package)
	visit = func(pkg *packages.Package) {
		if pkg == nil || seenID[pkg.ID] {
			return
		}
		seenID[pkg.ID] = true

		// Map iteration order is unspecified, so sort imports to make both
		// analysis and fix application deterministic.
		importPaths := make([]string, 0, len(pkg.Imports))
		for path := range pkg.Imports {
			importPaths = append(importPaths, path)
		}
		sort.Strings(importPaths)

		for _, path := range importPaths {
			visit(pkg.Imports[path])
		}

		if pkg.Module == nil ||
			pkg.ForTest != "" ||
			pkg.PkgPath == "" ||
			seenPath[pkg.PkgPath] {
			return
		}

		// Test-main packages are synthetic and cannot be loaded later as
		// ordinary import paths. The real package is loaded with Tests=true.
		if strings.HasSuffix(pkg.PkgPath, ".test") {
			return
		}

		seenPath[pkg.PkgPath] = true
		result = append(result, pkg.PkgPath)
	}

	for _, root := range roots {
		visit(root)
	}

	return result
}

func collectDeps(roots []*packages.Package) []*packages.Package {
	visited := make(map[string]bool)
	var result []*packages.Package

	var visit func(*packages.Package)
	visit = func(pkg *packages.Package) {
		if pkg == nil || visited[pkg.ID] {
			return
		}
		visited[pkg.ID] = true

		if pkg.Module == nil {
			return
		}

		for _, dep := range pkg.Imports {
			visit(dep)
		}

		result = append(result, pkg)
	}

	for _, root := range roots {
		visit(root)
	}

	return result
}

// printDiagnostics prints diagnostics in text or JSON form
// and returns the appropriate exit code.
func printDiagnostics(graph *checker.Graph) (exitcode int) {
	// Keep consistent with analogous logic in
	// processResults in ../../unitchecker/unitchecker.go.

	// Print the results.
	// With -json, the exit code is always zero.
	if analysisflags.JSON {
		if err := graph.PrintJSON(os.Stdout); err != nil {
			return 1
		}
	} else {
		if err := graph.PrintText(os.Stderr, analysisflags.Context); err != nil {
			return 1
		}

		// Compute the exit code.
		var numErrors, rootDiags int
		for act := range graph.All() {
			if act.Err != nil {
				numErrors++
			} else if act.IsRoot {
				rootDiags += len(act.Diagnostics)
			}
		}

		if numErrors > 0 {
			exitcode = 1 // analysis failed, at least partially
		} else if rootDiags > 0 {
			exitcode = 3 // successfully produced diagnostics
		}
	}

	// Print timing info.
	if dbg('t') {
		if !dbg('p') {
			log.Println("Warning: times are mostly GC/scheduler noise; use -debug=tp to disable parallelism")
		}

		var list []*checker.Action
		var total time.Duration
		for act := range graph.All() {
			list = append(list, act)
			total += act.Duration
		}

		// Print actions accounting for 90% of the total.
		sort.Slice(list, func(i, j int) bool {
			return list[i].Duration > list[j].Duration
		})
		var sum time.Duration
		for _, act := range list {
			fmt.Fprintf(os.Stderr, "%s\t%s\n", act.Duration, act)
			sum += act.Duration
			if sum >= total*9/10 {
				break
			}
		}
		if total > sum {
			fmt.Fprintf(os.Stderr, "%s\tall others\n", total-sum)
		}
	}

	return exitcode
}

// load loads the initial packages. Returns only top-level loading
// errors. Does not consider errors in packages.
func load(patterns []string, allSyntax bool) ([]*packages.Package, error) {
	mode := packages.LoadSyntax
	if allSyntax {
		mode = packages.LoadAllSyntax
	}
	mode |= packages.NeedModule
	conf := packages.Config{
		Mode: mode,
		// Ensure that child process inherits correct alias of PWD.
		// (See discussion at Dir field of [exec.Command].)
		// However, this currently breaks some tests.
		// TODO(adonovan): Investigate.
		//
		// Dir:   os.Getenv("PWD"),
		Tests: IncludeTests,
	}
	initial, err := packages.Load(&conf, patterns...)
	if err == nil && len(initial) == 0 {
		err = fmt.Errorf("%s matched no packages", strings.Join(patterns, " "))
	}
	return initial, err
}

// needFacts reports whether any analysis required by the specified set
// needs facts.  If so, we must load the entire program from source.
func needFacts(analyzers []*analysis.Analyzer) bool {
	seen := make(map[*analysis.Analyzer]bool)
	var q []*analysis.Analyzer // for BFS
	q = append(q, analyzers...)
	for len(q) > 0 {
		a := q[0]
		q = q[1:]
		if !seen[a] {
			seen[a] = true
			if len(a.FactTypes) > 0 {
				return true
			}
			q = append(q, a.Requires...)
		}
	}
	return false
}

func dbg(b byte) bool { return strings.IndexByte(Debug, b) >= 0 }
