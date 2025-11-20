package main

import (
	"bytes"
	"context"
	"encoding/csv"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log"
	"net/http"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/PuerkitoBio/goquery"
)

// Configuration holds the application configuration
type Config struct {
	PackageName      string
	ReleaseURL       string
	ReleaseBranch    string
	SingleRepoURL    string
	SingleRepoBranch string
	OutputCSV        string
	AnalyzerPath     string
	Workers          int
	FileWorkers      int
	SkipAnalysis     bool
	ForceRerun       bool
	CSVOnly          string
	ExtractCode      bool
	SignaturesOnly   bool
	Progress         bool
	LogFile          string
	VerboseLogging   bool
	DebugMode        bool
	OutputDir        string
}

// Logger provides thread-safe logging with timestamps
type Logger struct {
	mu     sync.Mutex
	writer io.Writer
}

func NewLogger(writer io.Writer) *Logger {
	return &Logger{writer: writer}
}

func (l *Logger) Printf(format string, args ...interface{}) {
	l.mu.Lock()
	defer l.mu.Unlock()
	timestamp := time.Now().Format("15:04:05.000")
	fmt.Fprintf(l.writer, "[%s] %s", timestamp, fmt.Sprintf(format, args...))
}

func (l *Logger) Errorf(format string, args ...interface{}) {
	l.mu.Lock()
	defer l.mu.Unlock()
	timestamp := time.Now().Format("15:04:05.000")
	fmt.Fprintf(l.writer, "[%s] ERROR: %s", timestamp, fmt.Sprintf(format, args...))
}

// ErrorSummary tracks errors for debugging and analysis
type ErrorSummary struct {
	Component    string
	ErrorType    string // "clone_failed", "analysis_failed", "invalid_component"
	ErrorMessage string
	Timestamp    time.Time
	Duration     time.Duration
}

// GoProject represents a Go project found during scraping
type GoProject struct {
	Name                 string        `json:"name"`
	RepoURL              string        `json:"repo_url"`
	GoModuleCount        int           `json:"go_module_count"`
	GoModDetected        bool          `json:"go_mod_detected"`
	GoModPaths           []string      `json:"go_mod_paths"`
	BranchesChecked      []string      `json:"branches_checked"`
	SelectedBranch       string        `json:"selected_branch"`
	ClonePath            string        `json:"-"`
	InitialCloneDuration time.Duration `json:"-"`
	IsGoProject          bool          `json:"is_go_project"`
}

type cloneResult struct {
	repoURL  string
	branch   string
	checked  []string
	path     string
	duration time.Duration
	err      error
}

type treeResult struct {
	repoURL       string
	branch        string
	checked       []string
	filePaths     []string
	goModPaths    []string
	path          string
	cloneDuration time.Duration
	err           error
}

func repoCacheKey(repoURL, branch string) string {
	base := strings.TrimSpace(repoURL)
	if base != "" {
		base = strings.TrimSuffix(base, ".git")
		base = strings.TrimSuffix(base, "/")
		base = strings.ToLower(base)
	}
	keyBranch := strings.TrimSpace(branch)
	return fmt.Sprintf("%s#%s", base, keyBranch)
}

func (ia *IntegratedAnalyzer) storeClonePath(repoURL, branch, path string) {
	if path == "" {
		return
	}
	key := repoCacheKey(repoURL, branch)
	ia.cloneCacheMux.Lock()
	ia.cloneCache[key] = path
	ia.cloneCacheMux.Unlock()
}

// TestCase represents a test case row in CSV
type TestCase struct {
	Serial         string `csv:"S.No."`
	Component      string `csv:"component"`
	Branch         string `csv:"branch"`
	Pkg            string `csv:"pkg"`
	Progress       string `csv:"progress"`
	Workers        string `csv:"workers"`
	FileWorkers    string `csv:"file-workers"`
	ExtractCode    string `csv:"extract-code"`
	OutputFile     string `csv:"output-file"`
	SignaturesOnly string `csv:"signatures-only"`
	GoModuleCount  string `csv:"Go Module Count"`
	GoModDetected  string `csv:"Go.mod Detected"`
	// Result columns
	Impacted             string        `csv:"Impacted"`
	TotalPackagesFound   string        `csv:"Total Packages Found"`
	DirectDependencies   string        `csv:"Direct Dependencies"`
	VendoredDeps         string        `csv:"Vendored Dependencies"`
	TotalImpactedFiles   string        `csv:"Total Impacted Files"`
	TotalUniqueSymbols   string        `csv:"Total Unique Symbols"`
	CloneDuration        string        `csv:"Clone Duration"`
	ExecutionTime        string        `csv:"Execution Time"`
	AnalysisRate         string        `csv:"Analysis Rate"`
	LocalClonePath       string        `csv:"-"`
	InitialCloneDuration time.Duration `csv:"-"`
}

// PackageResult represents analysis result for a package
type PackageResult struct {
	Package          string   `json:"package"`
	DirectDependency bool     `json:"directdependency"`
	Vendored         bool     `json:"vendored"`
	ImpactedFiles    []string `json:"impactedfiles"`
	UsedSymbols      []string `json:"usedsymbols"`
}

// AnalysisResult represents the result of analyzing a single repository
type AnalysisResult struct {
	TestCase      TestCase
	Success       bool
	ErrorMessage  string
	CloneDuration time.Duration
	ExecDuration  time.Duration
	Results       []PackageResult
	TotalPackages int
}

type PipelineSummary struct {
	Total   int
	Success int
	Failed  int
}

// deduplicatePackageResults removes duplicate packages and deduplicates impacted files within each package.
//
// This function addresses the issue where repo_analyzer may return duplicate packages:
// - A package can appear in both directImporters and impactedMainModules
// - A package can be both in vendor and in main module packages
//
// Deduplication strategy:
// 1. Use package import path as the unique key
// 2. Merge duplicate packages:
//   - DirectDependency: true if ANY instance is a direct dependency
//   - Vendored: true if ANY instance is vendored
//   - ImpactedFiles: union of all impacted files (deduplicated)
//   - UsedSymbols: union of all used symbols (deduplicated)
//
// 3. Within each package, deduplicate impacted files and symbols
//
// This ensures accurate counts for:
// - Total Packages Found
// - Total Impacted Files
// - Total Unique Symbols
func deduplicatePackageResults(results []PackageResult) []PackageResult {
	packageMap := make(map[string]*PackageResult)

	for _, pkg := range results {
		if existing, exists := packageMap[pkg.Package]; exists {
			// Merge with existing package
			// Keep DirectDependency as true if either is true
			existing.DirectDependency = existing.DirectDependency || pkg.DirectDependency
			// Keep Vendored as true if either is true
			existing.Vendored = existing.Vendored || pkg.Vendored

			// Deduplicate and merge impacted files
			fileSet := make(map[string]struct{})
			for _, file := range existing.ImpactedFiles {
				fileSet[file] = struct{}{}
			}
			for _, file := range pkg.ImpactedFiles {
				fileSet[file] = struct{}{}
			}
			existing.ImpactedFiles = make([]string, 0, len(fileSet))
			for file := range fileSet {
				existing.ImpactedFiles = append(existing.ImpactedFiles, file)
			}

			// Deduplicate and merge used symbols
			symbolSet := make(map[string]struct{})
			for _, symbol := range existing.UsedSymbols {
				symbolSet[symbol] = struct{}{}
			}
			for _, symbol := range pkg.UsedSymbols {
				symbolSet[symbol] = struct{}{}
			}
			existing.UsedSymbols = make([]string, 0, len(symbolSet))
			for symbol := range symbolSet {
				existing.UsedSymbols = append(existing.UsedSymbols, symbol)
			}
		} else {
			// New package - deduplicate its files and symbols
			pkgCopy := pkg

			// Deduplicate impacted files
			fileSet := make(map[string]struct{})
			for _, file := range pkg.ImpactedFiles {
				fileSet[file] = struct{}{}
			}
			pkgCopy.ImpactedFiles = make([]string, 0, len(fileSet))
			for file := range fileSet {
				pkgCopy.ImpactedFiles = append(pkgCopy.ImpactedFiles, file)
			}

			// Deduplicate used symbols
			symbolSet := make(map[string]struct{})
			for _, symbol := range pkg.UsedSymbols {
				symbolSet[symbol] = struct{}{}
			}
			pkgCopy.UsedSymbols = make([]string, 0, len(symbolSet))
			for symbol := range symbolSet {
				pkgCopy.UsedSymbols = append(pkgCopy.UsedSymbols, symbol)
			}

			packageMap[pkg.Package] = &pkgCopy
		}
	}

	// Convert map back to slice
	dedupedResults := make([]PackageResult, 0, len(packageMap))
	for _, pkg := range packageMap {
		dedupedResults = append(dedupedResults, *pkg)
	}

	return dedupedResults
}

// WorkerPool manages concurrent repository processing
type WorkerPool struct {
	workers       int
	jobs          chan TestCase
	results       chan AnalysisResult
	wg            sync.WaitGroup
	ctx           context.Context
	cancel        context.CancelFunc
	config        *Config
	tempDirs      map[string]string
	tempDirsMux   sync.RWMutex
	baseTempDir   string // Base temp directory for cloning
	cloneCache    map[string]string
	cloneCacheMux *sync.RWMutex
	logger        *Logger
	errors        []ErrorSummary
	errorsMux     sync.Mutex
}

// IntegratedAnalyzer is the main application struct
type IntegratedAnalyzer struct {
	config        *Config
	httpClient    *http.Client
	tempDir       string
	cleanupFunc   func()
	signalChan    chan os.Signal
	cloneCache    map[string]string
	cloneCacheMux sync.RWMutex
	logger        *Logger
	releaseBranch string
}

// NewIntegratedAnalyzer creates a new analyzer instance
func NewIntegratedAnalyzer(config *Config) *IntegratedAnalyzer {
	// Create temp directory in current working directory
	cwd, err := os.Getwd()
	if err != nil {
		log.Fatalf("Failed to get current working directory: %v", err)
	}

	releaseBranch := strings.TrimSpace(config.ReleaseBranch)
	if releaseBranch == "" {
		releaseBranch = parseBranchFromURL(config.ReleaseURL)
	}
	if (releaseBranch == "" || releaseBranch == "unknown-branch") && strings.TrimSpace(config.SingleRepoBranch) != "" {
		releaseBranch = strings.TrimSpace(config.SingleRepoBranch)
	}

	targetPackage := strings.TrimSpace(config.PackageName)
	if targetPackage == "" {
		targetPackage = "package"
	}
	packageParts := strings.Split(targetPackage, "/")
	packageSegment := packageParts[len(packageParts)-1]
	packageSafe := sanitizeForFilename(packageSegment)
	if packageSafe == "" {
		packageSafe = "package"
	}

	releaseSegment := strings.TrimSpace(releaseBranch)
	if releaseSegment == "" {
		releaseSegment = "unknown-branch"
	}
	releaseSafe := sanitizeForFilename(releaseSegment)
	if releaseSafe == "" {
		releaseSafe = "unknown-branch"
	}

	tempDirName := fmt.Sprintf("temp_repos_%s_%s", packageSafe, releaseSafe)
	tempDir := filepath.Join(cwd, tempDirName)
	if _, err := os.Stat(tempDir); err == nil {
		tempDir = fmt.Sprintf("%s_%d", tempDir, time.Now().UnixNano())
	}

	if strings.TrimSpace(config.OutputDir) == "" {
		config.OutputDir = filepath.Join(tempDir, "analysis_outputs")
	}
	if strings.TrimSpace(config.LogFile) == "" {
		config.LogFile = filepath.Join(tempDir, "integrated_analyzer.log")
	}

	// Create the temp directory
	if err := os.MkdirAll(tempDir, 0755); err != nil {
		log.Fatalf("Failed to create temp directory: %v", err)
	}

	fmt.Printf(" Created temporary directory: %s\n", tempDir)

	// Create cleanup function
	cleanupFunc := func() {
		fmt.Printf("🧹 Cleaning up temporary directory: %s\n", tempDir)

		// Deletion temporarily disabled for inspection purposes.
		fmt.Printf("ℹ️  Retaining %s for inspection (cleanup disabled)\n", tempDir)
	}

	// Set up signal channel for graceful shutdown
	signalChan := make(chan os.Signal, 1)
	signal.Notify(signalChan, os.Interrupt, syscall.SIGTERM, syscall.SIGQUIT)

	// Setup logger
	var writer io.Writer = os.Stdout
	if config.LogFile != "" {
		logFile, err := os.OpenFile(config.LogFile, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0666)
		if err != nil {
			log.Fatalf("Failed to open log file: %v", err)
		}
		writer = io.MultiWriter(os.Stdout, logFile)
	}

	ia := &IntegratedAnalyzer{
		config: config,
		httpClient: &http.Client{
			Timeout: 30 * time.Second,
		},
		tempDir:       tempDir,
		cleanupFunc:   cleanupFunc,
		signalChan:    signalChan,
		cloneCache:    make(map[string]string),
		logger:        NewLogger(writer),
		releaseBranch: releaseBranch,
	}

	// Start signal handler goroutine
	go ia.handleSignals()

	return ia
}

// handleSignals handles OS signals for graceful shutdown
func (ia *IntegratedAnalyzer) handleSignals() {
	sig := <-ia.signalChan
	fmt.Printf("\nReceived signal: %v\n", sig)
	fmt.Println("Performing graceful shutdown...")

	// Perform cleanup
	ia.cleanupFunc()

	// Exit gracefully
	fmt.Println("Goodbye!")
	os.Exit(0)
}

// Run executes the complete workflow
func (ia *IntegratedAnalyzer) Run() error {
	start := time.Now()

	defer ia.cleanupFunc()

	// Create output directory for analysis results
	outputDir := strings.TrimSpace(ia.config.OutputDir)
	if outputDir == "" {
		outputDir = filepath.Join(ia.tempDir, "analysis_outputs")
	}
	ia.config.OutputDir = outputDir
	if err := os.MkdirAll(outputDir, 0755); err != nil {
		return fmt.Errorf("failed to create output directory: %w", err)
	}

	fmt.Println("================================================================================")
	fmt.Println("INTEGRATED ANALYZER - GO CONCURRENT VERSION")
	fmt.Println("================================================================================")
	fmt.Printf("Release URL: %s\n", ia.config.ReleaseURL)
	fmt.Printf("Package: %s\n", ia.config.PackageName)
	fmt.Printf("Workers: %d\n", ia.config.Workers)
	fmt.Printf("Temp Directory: %s\n", ia.tempDir)
	fmt.Printf("Output Directory: %s\n", outputDir)
	if strings.TrimSpace(ia.config.SingleRepoURL) != "" {
		fmt.Printf("Single Repo URL: %s\n", ia.config.SingleRepoURL)
		if strings.TrimSpace(ia.config.SingleRepoBranch) != "" {
			fmt.Printf("Single Repo Branch: %s\n", ia.config.SingleRepoBranch)
		}
	}

	if strings.TrimSpace(ia.config.SingleRepoURL) != "" {
		summary, csvFile, analysisDuration, err := ia.runSingleRepo()
		if err != nil {
			return err
		}

		ia.logger.Printf("\n=== SINGLE REPOSITORY SUMMARY ===\n")
		ia.logger.Printf("✓ Processed %d repositories (%d succeeded, %d failed) in %v\n",
			summary.Total, summary.Success, summary.Failed, analysisDuration)
		ia.logger.Printf("✓ CSV saved to: %s\n", csvFile)

		totalDuration := time.Since(start)
		ia.logger.Printf("\n⏱️  Total Workflow Time: %v\n", totalDuration)
		if totalDuration.Minutes() > 0 {
			ia.logger.Printf("📊 Performance: %.2f repos/min\n", float64(summary.Total)*60.0/totalDuration.Minutes())
		}
		return nil
	}

	if ia.config.CSVOnly != "" {
		fmt.Println("\n=== ANALYSIS-ONLY MODE ===")
		analysisStart := time.Now()
		if err := ia.analyzeWithFanOut(ia.config.CSVOnly); err != nil {
			return fmt.Errorf("analysis failed: %w", err)
		}
		analysisDuration := time.Since(analysisStart)
		ia.logger.Printf("✓ Analysis completed in %v\n", analysisDuration)

		totalDuration := time.Since(start)
		ia.logger.Printf("\n  Total Workflow Time: %v\n", totalDuration)
		if totalDuration.Minutes() > 0 {
			ia.logger.Printf(" Performance: %.2f repos/min\n", float64(ia.config.Workers)*60.0/totalDuration.Minutes())
		}
		return nil
	}

	fmt.Println("\n=== PHASE 1: WEB SCRAPING & DISCOVERY ===")
	scrapingStart := time.Now()

	pipelineCtx, cancelPipeline := context.WithCancel(context.Background())
	defer cancelPipeline()

	projectCh := make(chan GoProject, ia.config.Workers)
	scrapeErrCh := make(chan error, 1)
	go func() {
		scrapeErrCh <- ia.scrapeWithFanOut(pipelineCtx, projectCh)
		close(projectCh)
	}()

	type testCaseSummary struct {
		count int
		err   error
	}

	testCaseCh := make(chan TestCase, ia.config.Workers)
	testCaseSummaryCh := make(chan testCaseSummary, 1)
	go func() {
		count := 0
		for project := range projectCh {
			if !project.IsGoProject {
				continue
			}
			testCase := ia.buildTestCaseFromProject(project)
			count++
			select {
			case testCaseCh <- testCase:
			case <-pipelineCtx.Done():
				testCaseSummaryCh <- testCaseSummary{count: count, err: pipelineCtx.Err()}
				close(testCaseCh)
				return
			}
		}
		close(testCaseCh)
		testCaseSummaryCh <- testCaseSummary{count: count, err: nil}
	}()

	csvFile := ia.config.OutputCSV
	if csvFile == "" {
		csvFile = fmt.Sprintf("integrated_test_cases_%d.csv", time.Now().Unix())
	}

	file, err := os.Create(csvFile)
	if err != nil {
		return fmt.Errorf("failed to create CSV: %w", err)
	}
	defer file.Close()

	writer := csv.NewWriter(file)
	header := []string{
		"S.No.", "component", "branch", "pkg", "progress", "workers", "file-workers", "extract-code",
		"output-file", "signatures-only", "Go.mod Detected", "Go Module Count",
		"Impacted", "Total Packages Found", "Direct Dependencies", "Vendored Dependencies",
		"Total Impacted Files", "Total Unique Symbols", "Clone Duration", "Execution Time", "Analysis Rate",
	}
	if err := writer.Write(header); err != nil {
		return fmt.Errorf("failed to write CSV header: %w", err)
	}
	writer.Flush()
	if err := writer.Error(); err != nil {
		return fmt.Errorf("failed to flush CSV header: %w", err)
	}

	analysisStart := time.Now()
	resultsCh := ia.analyzeStream(pipelineCtx, testCaseCh)

	type csvResult struct {
		summary PipelineSummary
		err     error
	}
	csvResultCh := make(chan csvResult, 1)
	go func() {
		summary, err := ia.writeResultsToCSV(writer, resultsCh)
		csvResultCh <- csvResult{summary: summary, err: err}
	}()

	scrapeErr := <-scrapeErrCh
	if scrapeErr != nil {
		cancelPipeline()
		<-csvResultCh
		return fmt.Errorf("scraping failed: %w", scrapeErr)
	}

	scrapingDuration := time.Since(scrapingStart)
	tcSummary := <-testCaseSummaryCh
	if tcSummary.err != nil && !errors.Is(tcSummary.err, context.Canceled) {
		cancelPipeline()
		<-csvResultCh
		return fmt.Errorf("test case preparation failed: %w", tcSummary.err)
	}
	if tcSummary.count == 0 {
		cancelPipeline()
		<-csvResultCh
		return fmt.Errorf("no Go projects found")
	}

	csvRes := <-csvResultCh
	if csvRes.err != nil {
		cancelPipeline()
		return fmt.Errorf("failed to write CSV: %w", csvRes.err)
	}

	analysisDuration := time.Since(analysisStart)
	if err := file.Sync(); err != nil {
		fmt.Printf("  Failed to sync CSV to disk: %v\n", err)
	}

	ia.logger.Printf("✓ Found %d Go projects in %v\n", tcSummary.count, scrapingDuration)
	ia.logger.Printf("\n=== PHASE 2: ANALYSIS & CSV WRITING ===\n")
	ia.logger.Printf("✓ Processed %d repositories (%d succeeded, %d failed) in %v\n",
		csvRes.summary.Total, csvRes.summary.Success, csvRes.summary.Failed, analysisDuration)
	ia.logger.Printf("✓ CSV saved to: %s\n", csvFile)

	totalDuration := time.Since(start)
	ia.logger.Printf("\n  Total Workflow Time: %v\n", totalDuration)
	if totalDuration.Minutes() > 0 {
		ia.logger.Printf(" Performance: %.2f repos/min\n", float64(ia.config.Workers)*60.0/totalDuration.Minutes())
	}

	return nil
}

func (ia *IntegratedAnalyzer) runSingleRepo() (PipelineSummary, string, time.Duration, error) {
	repoURL := strings.TrimSpace(ia.config.SingleRepoURL)
	if repoURL == "" {
		return PipelineSummary{}, "", 0, fmt.Errorf("single repository URL is required")
	}

	normalizedURL := ia.extractBaseRepositoryURL(repoURL)
	if normalizedURL != "" {
		repoURL = normalizedURL
	}

	fmt.Println("\n=== SINGLE REPOSITORY MODE ===")
	fmt.Printf("Analyzing repository: %s\n", repoURL)
	branchHint := strings.TrimSpace(ia.config.SingleRepoBranch)
	if branchHint != "" {
		fmt.Printf("Requested branch: %s\n", branchHint)
	}

	project, err := ia.inspectSingleRepository(repoURL, branchHint)
	if err != nil {
		return PipelineSummary{}, "", 0, err
	}
	if !project.IsGoProject {
		return PipelineSummary{}, "", 0, fmt.Errorf("repository %s does not appear to contain Go modules or non-vendored Go code", repoURL)
	}

	testCase := ia.buildTestCaseFromProject(project)
	testCase.Branch = project.SelectedBranch

	if ia.config.Progress {
		ia.logger.Printf("Prepared single repository test case: Component=%s, Branch=%s\n",
			testCase.Component, testCase.Branch)
	}

	csvFile := ia.config.OutputCSV
	if strings.TrimSpace(csvFile) == "" {
		csvFile = fmt.Sprintf("single_repo_test_cases_%d.csv", time.Now().Unix())
	}

	file, err := os.Create(csvFile)
	if err != nil {
		return PipelineSummary{}, "", 0, fmt.Errorf("failed to create CSV: %w", err)
	}
	defer file.Close()

	writer := csv.NewWriter(file)
	header := []string{
		"S.No.", "component", "branch", "pkg", "progress", "workers", "file-workers", "extract-code",
		"output-file", "signatures-only", "Go.mod Detected", "Go Module Count",
		"Impacted", "Total Packages Found", "Direct Dependencies", "Vendored Dependencies",
		"Total Impacted Files", "Total Unique Symbols", "Clone Duration", "Execution Time", "Analysis Rate",
	}
	if err := writer.Write(header); err != nil {
		return PipelineSummary{}, "", 0, fmt.Errorf("failed to write CSV header: %w", err)
	}
	writer.Flush()
	if err := writer.Error(); err != nil {
		return PipelineSummary{}, "", 0, fmt.Errorf("failed to flush CSV header: %w", err)
	}

	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Minute)
	defer cancel()

	analysisStart := time.Now()

	testCaseCh := make(chan TestCase, 1)
	resultsCh := ia.analyzeStream(ctx, testCaseCh)

	testCaseCh <- testCase
	close(testCaseCh)

	summary, err := ia.writeResultsToCSV(writer, resultsCh)
	analysisDuration := time.Since(analysisStart)
	if err != nil {
		return PipelineSummary{}, "", analysisDuration, fmt.Errorf("failed to write CSV: %w", err)
	}

	if err := file.Sync(); err != nil {
		fmt.Printf("⚠️  Failed to sync CSV to disk: %v\n", err)
	}

	return summary, csvFile, analysisDuration, nil
}

func (ia *IntegratedAnalyzer) inspectSingleRepository(repoURL, branchHint string) (GoProject, error) {
	normalizedURL := ia.extractBaseRepositoryURL(repoURL)
	if normalizedURL != "" {
		repoURL = normalizedURL
	}

	workCtx, cancel := context.WithTimeout(context.Background(), 20*time.Minute)
	defer cancel()

	candidates := ia.branchCandidates(branchHint)
	if len(candidates) == 0 {
		candidates = []string{"main", "master"}
	}

	checked := make([]string, 0, len(candidates))
	var lastErr error
	var repoPath string
	var selectedBranch string
	var cloneDuration time.Duration

	for _, candidate := range candidates {
		checked = append(checked, candidate)

		cacheKey := repoCacheKey(repoURL, candidate)
		ia.cloneCacheMux.RLock()
		cachedPath, exists := ia.cloneCache[cacheKey]
		ia.cloneCacheMux.RUnlock()
		if exists && strings.TrimSpace(cachedPath) != "" {
			repoPath = cachedPath
			selectedBranch = candidate
			cloneDuration = 0
			if ia.config != nil && ia.config.Progress {
				ia.logger.Printf("Using cached clone for %s (%s): %s\n", repoURL, candidate, cachedPath)
			}
			break
		}

		cloneStart := time.Now()
		path, err := ia.cloneRepositoryForInspection(workCtx, repoURL, candidate)
		duration := time.Since(cloneStart)
		if err != nil {
			lastErr = err
			if ia.config != nil && ia.config.Progress {
				ia.logger.Printf("Single repo clone failed for %s (%s): %v\n", repoURL, candidate, err)
			}
			continue
		}

		repoPath = path
		selectedBranch = candidate
		cloneDuration = duration
		break
	}

	if repoPath == "" {
		if lastErr == nil {
			lastErr = fmt.Errorf("no clone candidates succeeded")
		}
		return GoProject{}, fmt.Errorf("failed to clone %s (branches tried: %s): %w",
			repoURL, strings.Join(checked, ", "), lastErr)
	}

	filePaths, err := ia.listRepositoryFiles(workCtx, repoPath)
	if err != nil {
		return GoProject{}, fmt.Errorf("failed to list repository files: %w", err)
	}

	goModPaths := findGoModulesInTree(filePaths)

	project := GoProject{
		Name:                 ia.extractRepoName(repoURL),
		RepoURL:              repoURL,
		GoModuleCount:        len(goModPaths),
		GoModPaths:           goModPaths,
		BranchesChecked:      append([]string(nil), checked...),
		SelectedBranch:       selectedBranch,
		ClonePath:            repoPath,
		InitialCloneDuration: cloneDuration,
	}

	if project.Name == "unknown-repo" || !ia.isValidComponentName(project.Name) {
		return GoProject{}, fmt.Errorf("invalid component name derived from %s", repoURL)
	}

	if len(goModPaths) > 0 && ia.isValidGoProject(goModPaths) {
		project.IsGoProject = true
		project.GoModDetected = true
	} else if ia.hasSubstantialGoCode(filePaths) {
		project.IsGoProject = true
		project.GoModDetected = false
	}

	if project.IsGoProject {
		ia.storeClonePath(repoURL, selectedBranch, repoPath)
	}

	if ia.config != nil && ia.config.Progress {
		ia.logger.Printf("Single repo inspection: Component=%s, Branch=%s, GoModDetected=%t, Modules=%d\n",
			project.Name, project.SelectedBranch, project.GoModDetected, project.GoModuleCount)
	}

	return project, nil
}

// scrapeWithFanOut performs web scraping with concurrent repository analysis
func (ia *IntegratedAnalyzer) branchCandidates(target string) []string {
	target = strings.TrimSpace(target)
	candidates := make([]string, 0, 3)
	if target != "" && target != "unknown-branch" {
		candidates = append(candidates, target)
	}

	for _, fallback := range []string{"main", "master"} {
		if fallback != target {
			candidates = append(candidates, fallback)
		}
	}

	if len(candidates) == 0 {
		candidates = []string{"main", "master"}
	}

	return candidates
}

func (ia *IntegratedAnalyzer) scrapeWithFanOut(ctx context.Context, out chan<- GoProject) error {
	resp, err := ia.httpClient.Get(ia.config.ReleaseURL)
	if err != nil {
		return fmt.Errorf("failed to fetch release page: %w", err)
	}
	defer resp.Body.Close()

	doc, err := goquery.NewDocumentFromReader(resp.Body)
	if err != nil {
		return fmt.Errorf("failed to parse HTML: %w", err)
	}

	var repoURLs []string
	doc.Find("h3, h4").Each(func(i int, s *goquery.Selection) {
		if strings.Contains(s.Text(), "Rebuilt images without code change") {
			ul := s.Next()
			if ul.Is("ul") {
				ul.Find("li").Each(func(j int, li *goquery.Selection) {
					firstLink := li.Find("a").First()
					if firstLink.Length() == 0 {
						return
					}
					if href, exists := firstLink.Attr("href"); exists {
						baseURL := ia.extractBaseRepositoryURL(href)
						repoURLs = append(repoURLs, baseURL)
					}
				})
			}
		}
	})

	if len(repoURLs) == 0 {
		return fmt.Errorf("no repository URLs found")
	}

	totalRepositories := len(repoURLs)
	uniqueMap := make(map[string]struct{}, totalRepositories)
	uniqueRepositories := make([]string, 0, totalRepositories)
	for _, url := range repoURLs {
		if _, exists := uniqueMap[url]; exists {
			continue
		}
		uniqueMap[url] = struct{}{}
		uniqueRepositories = append(uniqueRepositories, url)
	}
	repoURLs = uniqueRepositories

	ia.logger.Printf("Found %d repositories (%d unique)\n", totalRepositories, len(repoURLs))

	branchHint := ia.releaseBranch
	workCtx, cancel := context.WithTimeout(ctx, 20*time.Minute)
	defer cancel()

	repoJobs := make(chan string, len(repoURLs))
	cloneResults := make(chan cloneResult, len(repoURLs))
	treeResults := make(chan treeResult, len(repoURLs))

	cloneWorkers := min(5, len(repoURLs))
	if cloneWorkers <= 0 {
		cloneWorkers = 1
	}
	treeWorkers := min(5, len(repoURLs))
	if treeWorkers <= 0 {
		treeWorkers = 1
	}

	var cloneWG sync.WaitGroup
	for workerID := 0; workerID < cloneWorkers; workerID++ {
		cloneWG.Add(1)
		go func(id int) {
			defer cloneWG.Done()
			for {
				select {
				case <-workCtx.Done():
					return
				case repoURL, ok := <-repoJobs:
					if !ok {
						return
					}

					candidates := ia.branchCandidates(branchHint)
					checked := make([]string, 0, len(candidates))
					var lastErr error
					var lastDuration time.Duration
					success := false

					for _, candidate := range candidates {
						checked = append(checked, candidate)
						if ia.config.Progress {
							fmt.Printf("    Clone worker %d: cloning %s (%s)\n", id, repoURL, candidate)
						}

						cloneStart := time.Now()
						repoPath, err := ia.cloneRepositoryForInspection(workCtx, repoURL, candidate)
						cloneDuration := time.Since(cloneStart)
						lastDuration = cloneDuration
						if err != nil {
							lastErr = err
							if ia.config.Progress {
								fmt.Printf("    Clone worker %d: ✗ clone failed for %s (%s): %v\n", id, repoURL, candidate, err)
							}
							continue
						}

						if ia.config.Progress {
							fmt.Printf("    Clone worker %d: ✓ cloned %s (%s) in %.2fs\n", id, repoURL, candidate, cloneDuration.Seconds())
						}

						cloneResults <- cloneResult{
							repoURL:  repoURL,
							branch:   candidate,
							checked:  append([]string(nil), checked...),
							path:     repoPath,
							duration: cloneDuration,
						}
						success = true
						break
					}

					if !success {
						cloneResults <- cloneResult{
							repoURL:  repoURL,
							branch:   branchHint,
							checked:  checked,
							duration: lastDuration,
							err:      fmt.Errorf("clone failed for %s: %w", repoURL, lastErr),
						}
					}
				}
			}
		}(workerID)
	}

	go func() {
		cloneWG.Wait()
		close(cloneResults)
	}()

	var treeWG sync.WaitGroup
	for workerID := 0; workerID < treeWorkers; workerID++ {
		treeWG.Add(1)
		go func(id int) {
			defer treeWG.Done()
			for {
				select {
				case <-workCtx.Done():
					return
				case cloneRes, ok := <-cloneResults:
					if !ok {
						return
					}

					if cloneRes.err != nil {
						treeResults <- treeResult{
							repoURL:       cloneRes.repoURL,
							branch:        cloneRes.branch,
							checked:       cloneRes.checked,
							path:          cloneRes.path,
							cloneDuration: cloneRes.duration,
							err:           cloneRes.err,
						}
						continue
					}

					filePaths, err := ia.listRepositoryFiles(workCtx, cloneRes.path)
					if err != nil {
						treeResults <- treeResult{
							repoURL:       cloneRes.repoURL,
							branch:        cloneRes.branch,
							checked:       cloneRes.checked,
							path:          cloneRes.path,
							cloneDuration: cloneRes.duration,
							err:           err,
						}
						continue
					}

					goModPaths := findGoModulesInTree(filePaths)
					treeResults <- treeResult{
						repoURL:       cloneRes.repoURL,
						branch:        cloneRes.branch,
						checked:       cloneRes.checked,
						filePaths:     filePaths,
						goModPaths:    goModPaths,
						path:          cloneRes.path,
						cloneDuration: cloneRes.duration,
					}
				}
			}
		}(workerID)
	}

	go func() {
		treeWG.Wait()
		close(treeResults)
	}()

	go func() {
		defer close(repoJobs)
		for _, url := range repoURLs {
			select {
			case repoJobs <- url:
			case <-workCtx.Done():
				return
			}
		}
	}()

	goProjectCount := 0
	ignoredProjects := 0

	for result := range treeResults {
		if result.err != nil {
			if ia.config.Progress {
				fmt.Printf("      ✗ Skipping %s: %v\n", result.repoURL, result.err)
			}
			ignoredProjects++
			continue
		}

		project := GoProject{
			Name:                 ia.extractRepoName(result.repoURL),
			RepoURL:              result.repoURL,
			GoModuleCount:        len(result.goModPaths),
			GoModPaths:           result.goModPaths,
			BranchesChecked:      append([]string(nil), result.checked...),
			SelectedBranch:       result.branch,
			ClonePath:            result.path,
			InitialCloneDuration: result.cloneDuration,
		}

		if project.Name == "unknown-repo" || !ia.isValidComponentName(project.Name) {
			if ia.config.Progress {
				fmt.Printf("      ✗ Skipping repository with invalid component name derived from %s\n", result.repoURL)
			}
			ignoredProjects++
			continue
		}

		if len(result.goModPaths) > 0 && ia.isValidGoProject(result.goModPaths) {
			project.IsGoProject = true
			project.GoModDetected = true
			ia.storeClonePath(result.repoURL, result.branch, result.path)
			goProjectCount++
			select {
			case out <- project:
			case <-ctx.Done():
				return ctx.Err()
			}
			continue
		}

		if ia.hasSubstantialGoCode(result.filePaths) {
			project.IsGoProject = true
			project.GoModDetected = false
			project.GoModuleCount = 0
			project.GoModPaths = []string{}
			ia.storeClonePath(result.repoURL, result.branch, result.path)
			goProjectCount++
			select {
			case out <- project:
			case <-ctx.Done():
				return ctx.Err()
			}
			continue
		}

		ignoredProjects++
	}

	ia.logger.Printf("✓ Found %d Go projects, ignored %d non-Go projects\n", goProjectCount, ignoredProjects)
	return nil
}

// isInVendorDirectory checks if a file path is inside a vendor directory
// Matches Python is_in_vendor_directory() function
func isInVendorDirectory(filePath string) bool {
	// Normalize path separators
	normalizedPath := strings.ReplaceAll(filePath, "\\", "/")

	// Check various vendor directory patterns
	vendorPatterns := []string{
		"/vendor/",       // Anywhere in path: some/path/vendor/module/go.mod
		"vendor/",        // At start of path: vendor/module/go.mod
		"/vendor/go.mod", // Direct vendor go.mod: vendor/go.mod
		"vendor/go.mod",  // Root vendor go.mod: vendor/go.mod (edge case)
	}

	for _, pattern := range vendorPatterns {
		if strings.Contains(normalizedPath, pattern) || strings.HasPrefix(normalizedPath, strings.TrimPrefix(pattern, "/")) {
			return true
		}
	}

	return false
}

func isInExcludedDirectory(filePath string) bool {
	segments := strings.Split(filePath, "/")

	if len(segments) > 1 {
		segments = segments[:len(segments)-1]
	}

	for _, segment := range segments {
		if segment == "test" || segment == "e2e" || segment == "tests" || segment == "tools" || segment == "hack" || segment == ".bingo" || segment == "scripts" || segment == "examples" || segment == "testdata" {
			return true
		}
	}

	return false
}

// findGoModulesInTree searches for go.mod files in a list of file paths, ignoring vendor directories
// Matches Python find_go_modules_in_tree() function
func findGoModulesInTree(filePaths []string) []string {
	var goModPaths []string

	for _, path := range filePaths {
		if filepath.Base(path) == "go.mod" && !isInVendorDirectory(path) {
			goModPaths = append(goModPaths, path)
		}
	}

	return goModPaths
}

// checkLegacyGoFilesInTree checks if repository contains Go files (for legacy GOPATH detection)
// Matches Python check_legacy_go_files_in_tree() function
func checkLegacyGoFilesInTree(filePaths []string) bool {
	for _, path := range filePaths {
		// Skip files living in excluded directories
		if isInExcludedDirectory(path) {
			continue
		}

		if strings.Contains(path, "vendor/") {
			continue
		}

		// Check for main.go specifically
		if path == "main.go" || strings.HasSuffix(path, "/main.go") {
			return true
		}

		// Check for any .go files (ignoring test files)
		if strings.HasSuffix(path, ".go") {
			if strings.Contains(path, "_test.go") {
				continue
			}
			return true
		}
	}

	return false
}

// isValidGoProject checks if the found go.mod files represent a valid Go project
// More strict than just finding any go.mod files
func (ia *IntegratedAnalyzer) isValidGoProject(goModPaths []string) bool {
	// Require at least one go.mod file
	if len(goModPaths) == 0 {
		return false
	}

	// Prefer projects with root go.mod
	for _, path := range goModPaths {
		if path == "go.mod" {
			return true // Root go.mod is always valid
		}
	}

	// If no root go.mod, be more selective
	// Allow projects with a reasonable number of modules (not too many nested ones)
	validPaths := 0
	for _, path := range goModPaths {
		// Count depth - reject deeply nested go.mod files
		depth := strings.Count(path, "/")
		if depth <= 2 { // Allow up to 2 levels deep (e.g., api/go.mod, client/go.mod)
			validPaths++
		}
	}

	// Require at least one reasonably placed go.mod and not too many scattered ones
	return validPaths > 0 && len(goModPaths) <= 10
}

// hasSubstantialGoCode checks if repository has substantial Go code (stricter than legacy check)
// More conservative than checkLegacyGoFilesInTree to match Python's selectivity
func (ia *IntegratedAnalyzer) hasSubstantialGoCode(filePaths []string) bool {
	goFileCount := 0
	hasMainGo := false

	for _, path := range filePaths {
		if strings.HasSuffix(path, ".go") {
			// Skip test files and vendor files for this check
			if strings.Contains(path, "_test.go") || strings.Contains(path, "vendor/") {
				continue
			}

			goFileCount++

			// Check for main.go specifically
			if path == "main.go" || strings.HasSuffix(path, "/main.go") {
				hasMainGo = true
			}
		}
	}

	// Require either main.go or substantial number of Go files (like Python's selectivity)
	return hasMainGo || goFileCount >= 5
}

// extractBaseRepoURL extracts the base repository URL from various URL formats
func (ia *IntegratedAnalyzer) extractBaseRepoURL(repoURL string) (string, string) {
	// // Handle commit-specific URLs like: https://github.com/owner/repo/commit/hash
	// if strings.Contains(repoURL, "/commit/") {
	// 	parts := strings.Split(repoURL, "/commit/")
	// 	if len(parts) == 2 {
	// 		return parts[0], parts[1] // base URL, commit hash
	// 	}
	// }

	// Handle pull request URLs or other formats - extract base repository
	re := regexp.MustCompile(`(https://github\.com/[^/]+/[^/]+)(?:/.*)?`)
	matches := re.FindStringSubmatch(repoURL)
	if len(matches) >= 2 {
		return matches[1], "" // base URL, no commit
	}

	// Return as-is if no special format detected
	return repoURL, ""
}

// analyzeWithFanOut performs repository analysis with concurrent processing
const integratedWorkers = 5
const integratedFileWorkers = 5
const integratedAnalyzerWorkers = 5

func (ia *IntegratedAnalyzer) analyzeStream(ctx context.Context, testCases <-chan TestCase) <-chan AnalysisResult {
	results := make(chan AnalysisResult, integratedAnalyzerWorkers)

	poolCtx, poolCancel := context.WithCancel(ctx)

	pool := &WorkerPool{
		workers:       integratedAnalyzerWorkers,
		jobs:          make(chan TestCase, integratedAnalyzerWorkers),
		results:       make(chan AnalysisResult, integratedAnalyzerWorkers),
		ctx:           poolCtx,
		cancel:        poolCancel,
		config:        ia.config,
		tempDirs:      make(map[string]string),
		tempDirsMux:   sync.RWMutex{},
		baseTempDir:   ia.tempDir,
		cloneCache:    ia.cloneCache,
		cloneCacheMux: &ia.cloneCacheMux,
		logger:        ia.logger,
		errors:        make([]ErrorSummary, 0),
		errorsMux:     sync.Mutex{},
	}

	for i := 0; i < pool.workers; i++ {
		pool.wg.Add(1)
		go pool.analysisWorker(i)
	}

	go func() {
		defer close(pool.jobs)
		for {
			select {
			case <-poolCtx.Done():
				return
			case testCase, ok := <-testCases:
				if !ok {
					return
				}
				select {
				case pool.jobs <- testCase:
				case <-poolCtx.Done():
					return
				}
			}
		}
	}()

	go func() {
		pool.wg.Wait()
		close(pool.results)
	}()

	go func() {
		defer close(results)
		defer poolCancel()
		for {
			select {
			case <-poolCtx.Done():
				return
			case res, ok := <-pool.results:
				if !ok {
					return
				}
				select {
				case results <- res:
				case <-poolCtx.Done():
					return
				}
			}
		}
	}()

	return results
}

func (ia *IntegratedAnalyzer) analyzeWithFanOut(csvFile string) error {
	// Read test cases from CSV
	testCases, err := ia.readTestCases(csvFile)
	if err != nil {
		return fmt.Errorf("failed to read test cases: %w", err)
	}

	ia.logger.Printf("Processing %d test cases with %d workers\n", len(testCases), integratedAnalyzerWorkers)

	// Create worker pool
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Minute)
	defer cancel()

	pool := &WorkerPool{
		workers:       integratedAnalyzerWorkers,
		jobs:          make(chan TestCase, len(testCases)),
		results:       make(chan AnalysisResult, len(testCases)),
		ctx:           ctx,
		cancel:        cancel,
		config:        ia.config,
		tempDirs:      make(map[string]string),
		tempDirsMux:   sync.RWMutex{},
		baseTempDir:   ia.tempDir, // Pass the analyzer's temp directory
		cloneCache:    ia.cloneCache,
		cloneCacheMux: &ia.cloneCacheMux,
		logger:        ia.logger,
		errors:        make([]ErrorSummary, 0),
		errorsMux:     sync.Mutex{},
	}

	// Start workers
	for i := 0; i < pool.workers; i++ {
		pool.wg.Add(1)
		go pool.analysisWorker(i)
	}

	// Send jobs
	go func() {
		defer close(pool.jobs)
		for _, testCase := range testCases {
			// Skip if already completed (unless force rerun)
			if !ia.config.ForceRerun && testCase.Impacted != "" && testCase.Impacted != "N/A" {
				// Send as completed job
				pool.results <- AnalysisResult{
					TestCase: testCase,
					Success:  true,
				}
				continue
			}

			select {
			case pool.jobs <- testCase:
			case <-ctx.Done():
				return
			}
		}
	}()

	// Collect results
	var results []AnalysisResult
	go func() {
		pool.wg.Wait()
		close(pool.results)
	}()

	for result := range pool.results {
		results = append(results, result)
		if len(results)%10 == 0 {
			ia.logger.Printf("  Completed: %d/%d\n", len(results), len(testCases))
		}
	}

	// Print error summary
	pool.printErrorSummary()

	// Update CSV with results
	return ia.updateCSVWithResults(csvFile, results)
}

// analysisWorker processes test cases concurrently
func (wp *WorkerPool) analysisWorker(workerID int) {
	defer wp.wg.Done()

	for {
		select {
		case testCase, ok := <-wp.jobs:
			if !ok {
				return
			}

			// Create a unique ID for this test case execution
			execID := fmt.Sprintf("W%d-TC%s-%d", workerID, testCase.Component, time.Now().UnixMilli()%10000)

			if wp.config.Progress {
				wp.logger.Printf("[%s] Starting analysis: Component=%s, Branch=%s\n",
					execID, testCase.Component, testCase.Branch)
			}

			result := wp.processTestCaseWithLogging(workerID, execID, testCase)

			if wp.config.Progress {
				if result.Success {
					wp.logger.Printf("[%s] ✓ SUCCESS: Packages=%d, Files=%d, Duration=%.2fs\n",
						execID, result.TotalPackages,
						wp.countTotalFiles(result.Results),
						result.ExecDuration.Seconds())
				} else {
					wp.logger.Errorf("[%s] ✗ FAILED: %s\n", execID, result.ErrorMessage)
				}
			}

			select {
			case wp.results <- result:
			case <-wp.ctx.Done():
				return
			}

		case <-wp.ctx.Done():
			return
		}
	}
}

// processTestCaseWithLogging processes a single test case with detailed logging
func (wp *WorkerPool) processTestCaseWithLogging(workerID int, execID string, testCase TestCase) AnalysisResult {
	start := time.Now()

	if wp.config.Progress {
		wp.logger.Printf("[%s] Processing: Component=%s, Branch=%s, Pkg=%s\n",
			execID, testCase.Component, testCase.Branch, testCase.Pkg)
	}

	result := AnalysisResult{
		TestCase: testCase,
		Success:  false,
	}
	extractCodeEnabled := strings.EqualFold(testCase.ExtractCode, "true")

	// Handle Git repository cloning
	var repoPath string
	var cloneDuration time.Duration

	// Validate component name first
	if !strings.HasPrefix(testCase.Component, "http") && !strings.HasPrefix(testCase.Component, "git@") && !strings.HasPrefix(testCase.Component, "/") {
		// Check if component name is valid (not a commit hash)
		ia := &IntegratedAnalyzer{} // Create temporary instance for validation
		if !ia.isValidComponentName(testCase.Component) {
			errorMsg := fmt.Sprintf("invalid component name '%s' (appears to be a commit hash or invalid format)", testCase.Component)
			result.ErrorMessage = errorMsg
			result.ExecDuration = time.Since(start)

			wp.recordError(testCase.Component, "invalid_component", errorMsg, time.Since(start))
			wp.logger.Errorf("[%s] Invalid component name: %s\n", execID, testCase.Component)

			return result
		}
	}

	// Convert component name to full URL if needed or reuse cached clone
	repoURL := ""
	if testCase.LocalClonePath != "" {
		repoPath = testCase.LocalClonePath
		cloneDuration = testCase.InitialCloneDuration
		if wp.config.Progress {
			wp.logger.Printf("[%s] Using cached clone: %s\n", execID, repoPath)
		}
	} else if strings.HasPrefix(testCase.Component, "http") || strings.HasPrefix(testCase.Component, "git@") {
		repoURL = testCase.Component
	} else if strings.HasPrefix(testCase.Component, "/") {
		repoPath = testCase.Component
		if wp.config.Progress {
			wp.logger.Printf("[%s] Using local path: %s\n", execID, repoPath)
		}
	} else {
		repoURL = fmt.Sprintf("https://github.com/openshift/%s", testCase.Component)
	}

	if repoPath == "" && repoURL != "" {
		if wp.config.Progress {
			wp.logger.Printf("[%s] Clone: Starting clone of %s\n", execID, repoURL)
		}

		cloneStart := time.Now()
		var err error
		repoPath, err = wp.cloneRepositoryWithLogging(workerID, execID, repoURL, testCase.Branch)
		cloneDuration = time.Since(cloneStart)

		if err != nil {
			errorMsg := fmt.Sprintf("clone failed for %s (branch: %s): %v", repoURL, testCase.Branch, err)
			result.ErrorMessage = errorMsg
			result.CloneDuration = cloneDuration
			result.ExecDuration = time.Since(start)

			wp.recordError(testCase.Component, "clone_failed", errorMsg, cloneDuration)
			wp.logger.Errorf("[%s] Clone failed: URL=%s, Branch=%s, Duration=%.2fs, Error=%v\n",
				execID, repoURL, testCase.Branch, cloneDuration.Seconds(), err)

			return result
		}

		if wp.config.Progress {
			wp.logger.Printf("[%s] Clone: ✓ Success in %.2fs to %s\n",
				execID, cloneDuration.Seconds(), repoPath)
		}
	}

	// Analysis phase with detailed logging
	if wp.config.Progress {
		wp.logger.Printf("[%s] Analysis: Starting analysis on %s\n", execID, repoPath)
	}

	execStart := time.Now()
	analysisResults, totalPackages, err := wp.runAnalysisWithLogging(execID, repoPath, testCase)
	execDuration := time.Since(execStart)

	if err != nil {
		errorMsg := fmt.Sprintf("analysis failed for %s: %v", testCase.Component, err)
		result.ErrorMessage = errorMsg
		result.CloneDuration = cloneDuration
		result.ExecDuration = execDuration

		wp.recordError(testCase.Component, "analysis_failed", errorMsg, execDuration)
		wp.logger.Errorf("[%s] Analysis failed: Component=%s, RepoPath=%s, Duration=%.2fs, Error=%v\n",
			execID, testCase.Component, repoPath, execDuration.Seconds(), err)

		return result
	}

	// Deduplicate packages and their impacted files
	originalPackageCount := len(analysisResults)
	analysisResults = deduplicatePackageResults(analysisResults)
	totalPackages = len(analysisResults)

	if wp.config.Progress {
		if originalPackageCount != totalPackages {
			wp.logger.Printf("[%s] Analysis: ✓ Success, Packages=%d (deduplicated from %d), Duration=%.2fs\n",
				execID, totalPackages, originalPackageCount, execDuration.Seconds())
		} else {
			wp.logger.Printf("[%s] Analysis: ✓ Success, Packages=%d, Duration=%.2fs\n",
				execID, totalPackages, execDuration.Seconds())
		}
	}

	result.Results = analysisResults
	result.TotalPackages = totalPackages
	result.CloneDuration = cloneDuration
	result.ExecDuration = execDuration

	// Code extraction is now handled directly in runAnalysisWithLogging
	// by specifying the -output-file flag, so no separate call needed
	if extractCodeEnabled && wp.resultsHaveImpact(analysisResults) {
		outputFileName := testCase.OutputFile
		if strings.TrimSpace(outputFileName) == "" {
			outputFileName = wp.buildOutputFileName(testCase)
		}
		result.TestCase.OutputFile = outputFileName
		result.TestCase.ExtractCode = "true"
	} else {
		result.TestCase.OutputFile = ""
		if !extractCodeEnabled {
			result.TestCase.ExtractCode = "false"
			result.TestCase.SignaturesOnly = "false"
		}
	}

	result.Success = true

	return result
}

// cloneRepository clones a Git repository for analysis
func (wp *WorkerPool) cloneRepository(workerID int, repoURL, branch string) (string, error) {
	baseURL := repoURL

	// Check cache first
	cacheKey := repoCacheKey(baseURL, branch)
	if wp.cloneCache != nil && wp.cloneCacheMux != nil {
		wp.cloneCacheMux.RLock()
		if path, exists := wp.cloneCache[cacheKey]; exists && path != "" {
			wp.cloneCacheMux.RUnlock()
			return path, nil
		}
		wp.cloneCacheMux.RUnlock()
	}
	wp.tempDirsMux.RLock()
	if path, exists := wp.tempDirs[cacheKey]; exists {
		wp.tempDirsMux.RUnlock()
		return path, nil
	}
	wp.tempDirsMux.RUnlock()

	// Create unique temp directory within the base temp directory
	tempDir := filepath.Join(wp.baseTempDir, fmt.Sprintf("repo_analyzer_%d_%d", workerID, time.Now().UnixNano()))

	// Execute clone
	ctx, cancel := context.WithTimeout(wp.ctx, 5*time.Minute)
	defer cancel()

	// Always clone the latest version of the specified branch
	err := wp.cloneWithBranch(ctx, baseURL, branch, tempDir)

	if err != nil {
		return "", err
	}

	// Cache the result
	wp.tempDirsMux.Lock()
	wp.tempDirs[cacheKey] = tempDir
	wp.tempDirsMux.Unlock()

	if wp.cloneCache != nil && wp.cloneCacheMux != nil {
		wp.cloneCacheMux.Lock()
		wp.cloneCache[cacheKey] = tempDir
		wp.cloneCacheMux.Unlock()
	}

	return tempDir, nil
}

// cloneRepositoryWithLogging clones a Git repository with detailed logging
func (wp *WorkerPool) cloneRepositoryWithLogging(workerID int, execID string, repoURL, branch string) (string, error) {
	baseURL := repoURL

	// Check cache first
	cacheKey := repoCacheKey(baseURL, branch)
	if wp.cloneCache != nil && wp.cloneCacheMux != nil {
		wp.cloneCacheMux.RLock()
		if path, exists := wp.cloneCache[cacheKey]; exists && path != "" {
			wp.cloneCacheMux.RUnlock()
			if wp.config.Progress {
				wp.logger.Printf("[%s] Clone: Using global cached clone: %s\n", execID, path)
			}
			return path, nil
		}
		wp.cloneCacheMux.RUnlock()
	}
	wp.tempDirsMux.RLock()
	if path, exists := wp.tempDirs[cacheKey]; exists {
		wp.tempDirsMux.RUnlock()
		if wp.config.Progress {
			wp.logger.Printf("[%s] Clone: Using worker cached clone: %s\n", execID, path)
		}
		return path, nil
	}
	wp.tempDirsMux.RUnlock()

	// Create unique temp directory within the base temp directory
	tempDir := filepath.Join(wp.baseTempDir, fmt.Sprintf("repo_analyzer_%d_%d", workerID, time.Now().UnixNano()))

	// Execute clone
	ctx, cancel := context.WithTimeout(wp.ctx, 5*time.Minute)
	defer cancel()

	// Always clone the latest version of the specified branch
	err := wp.cloneWithBranchLogging(ctx, execID, baseURL, branch, tempDir)

	if err != nil {
		return "", err
	}

	// Cache the result
	wp.tempDirsMux.Lock()
	wp.tempDirs[cacheKey] = tempDir
	wp.tempDirsMux.Unlock()

	if wp.cloneCache != nil && wp.cloneCacheMux != nil {
		wp.cloneCacheMux.Lock()
		wp.cloneCache[cacheKey] = tempDir
		wp.cloneCacheMux.Unlock()
	}

	return tempDir, nil
}

// cloneWithBranch clones a repository with a specific branch
func (wp *WorkerPool) cloneWithBranch(ctx context.Context, baseURL, branch string, tempDir string) error {
	// Build clone command with shallow clone to reduce memory usage
	args := []string{"clone", "--depth", "1", "--single-branch"}
	if branch != "" && branch != "unknown-branch" {
		args = append(args, "-b", branch)
	}
	args = append(args, baseURL, tempDir)

	cmd := exec.CommandContext(ctx, "git", args...)
	// Set git configurations for better handling of large repositories
	cmd.Env = append(os.Environ(),
		"GIT_HTTP_LOW_SPEED_LIMIT=1000", // Minimum transfer speed (bytes/sec)
		"GIT_HTTP_LOW_SPEED_TIME=300",   // Time limit for low speed (seconds)
		"GIT_HTTP_MAX_REQUESTS=3",       // Max concurrent HTTP requests per git process
	)
	if err := cmd.Run(); err != nil {
		// Try without branch if branch-specific clone failed
		if branch != "" && branch != "unknown-branch" {
			args = []string{"clone", "--depth", "1", "--single-branch", baseURL, tempDir}
			cmd = exec.CommandContext(ctx, "git", args...)
			cmd.Env = append(os.Environ(),
				"GIT_HTTP_LOW_SPEED_LIMIT=1000",
				"GIT_HTTP_LOW_SPEED_TIME=300",
				"GIT_HTTP_MAX_REQUESTS=3",
			)
			if err := cmd.Run(); err != nil {
				return fmt.Errorf("failed to clone repository %s: %w", baseURL, err)
			}
		} else {
			return fmt.Errorf("failed to clone repository %s: %w", baseURL, err)
		}
	}

	return nil
}

// cloneWithBranchLogging clones a repository with a specific branch and detailed logging
func (wp *WorkerPool) cloneWithBranchLogging(ctx context.Context, execID, baseURL, branch string, tempDir string) error {
	// Build clone command with shallow clone to reduce memory usage
	args := []string{"clone", "--depth", "1", "--single-branch"}
	if branch != "" && branch != "unknown-branch" {
		args = append(args, "-b", branch)
	}
	args = append(args, baseURL, tempDir)

	if wp.config.Progress {
		wp.logger.Printf("[%s] Clone: Executing git %s\n", execID, strings.Join(args, " "))
	}

	cmd := exec.CommandContext(ctx, "git", args...)
	// Set git configurations for better handling of large repositories
	cmd.Env = append(os.Environ(),
		"GIT_HTTP_LOW_SPEED_LIMIT=1000", // Minimum transfer speed (bytes/sec)
		"GIT_HTTP_LOW_SPEED_TIME=300",   // Time limit for low speed (seconds)
		"GIT_HTTP_MAX_REQUESTS=3",       // Max concurrent HTTP requests per git process
	)
	if err := cmd.Run(); err != nil {
		// Try without branch if branch-specific clone failed
		if branch != "" && branch != "unknown-branch" {
			if wp.config.Progress {
				wp.logger.Printf("[%s] Clone: Branch-specific clone failed, trying default branch\n", execID)
			}
			args = []string{"clone", "--depth", "1", "--single-branch", baseURL, tempDir}
			cmd = exec.CommandContext(ctx, "git", args...)
			cmd.Env = append(os.Environ(),
				"GIT_HTTP_LOW_SPEED_LIMIT=1000",
				"GIT_HTTP_LOW_SPEED_TIME=300",
				"GIT_HTTP_MAX_REQUESTS=3",
			)
			if err := cmd.Run(); err != nil {
				return fmt.Errorf("failed to clone repository %s: %w", baseURL, err)
			}
		} else {
			return fmt.Errorf("failed to clone repository %s: %w", baseURL, err)
		}
	}

	return nil
}

// runAnalysis runs the Go analyzer on a repository
func (wp *WorkerPool) runAnalysis(repoPath string, testCase TestCase) ([]PackageResult, int, error) {
	// Build analyzer command
	args := []string{
		"-repo", repoPath,
		"-pkg", testCase.Pkg,
	}

	if testCase.Workers != "" {
		args = append(args, "-workers", testCase.Workers)
	}
	if testCase.FileWorkers != "" {
		args = append(args, "-file-workers", testCase.FileWorkers)
	}
	if testCase.Progress == "true" {
		args = append(args, "-progress")
	}
	if testCase.SignaturesOnly == "true" {
		args = append(args, "-signatures-only")
	}
	// If extract-code is enabled, specify output file to prevent creation in CWD
	if testCase.ExtractCode == "true" {
		args = append(args, "-extract-code")
		// Build output file path in analysis_outputs directory
		outputDir := strings.TrimSpace(wp.config.OutputDir)
		if outputDir == "" {
			outputDir = filepath.Join(wp.baseTempDir, "analysis_outputs")
		}
		outputFileName := testCase.OutputFile
		if strings.TrimSpace(outputFileName) == "" {
			outputFileName = wp.buildOutputFileName(testCase)
		}
		outputPath := filepath.Join(outputDir, outputFileName)
		args = append(args, "-output-file", outputPath)
	}

	// Run analyzer
	ctx, cancel := context.WithTimeout(wp.ctx, 5*time.Minute)
	defer cancel()

	cmd := exec.CommandContext(ctx, wp.config.AnalyzerPath, args...)
	var stdoutBuf, stderrBuf bytes.Buffer
	cmd.Stdout = &stdoutBuf
	cmd.Stderr = &stderrBuf

	if err := cmd.Run(); err != nil {
		if ctx.Err() == context.DeadlineExceeded {
			return nil, 0, fmt.Errorf("analyzer timed out after 5 minutes")
		}

		errorMsg := strings.TrimSpace(stderrBuf.String())
		if errorMsg != "" {
			return nil, 0, fmt.Errorf("analyzer failed: %s (exit code: %v)", errorMsg, err)
		}
		return nil, 0, fmt.Errorf("analyzer failed with exit code: %v", err)
	}

	// Parse JSON output
	var results []PackageResult
	output := stdoutBuf.Bytes()
	if len(output) > 0 {
		if err := json.Unmarshal(output, &results); err != nil {
			outputStr := strings.TrimSpace(string(output))
			if len(outputStr) > 200 {
				outputStr = outputStr[:200] + "..."
			}
			return nil, 0, fmt.Errorf("failed to parse JSON (output: %q): %w", outputStr, err)
		}
	}

	// Extract total packages from stderr (if available)
	totalPackages := len(results)

	return results, totalPackages, nil
}

// runAnalysisWithLogging runs the Go analyzer on a repository with detailed logging
func (wp *WorkerPool) runAnalysisWithLogging(execID, repoPath string, testCase TestCase) ([]PackageResult, int, error) {
	// Build analyzer command
	args := []string{
		"-repo", repoPath,
		"-pkg", testCase.Pkg,
	}

	if testCase.Workers != "" {
		args = append(args, "-workers", testCase.Workers)
	}
	if testCase.FileWorkers != "" {
		args = append(args, "-file-workers", testCase.FileWorkers)
	}
	if testCase.Progress == "true" {
		args = append(args, "-progress")
	}
	if testCase.SignaturesOnly == "true" {
		args = append(args, "-signatures-only")
	}
	// If extract-code is enabled, specify output file to prevent creation in CWD
	if testCase.ExtractCode == "true" {
		args = append(args, "-extract-code")
		// Build output file path in analysis_outputs directory
		outputDir := strings.TrimSpace(wp.config.OutputDir)
		if outputDir == "" {
			outputDir = filepath.Join(wp.baseTempDir, "analysis_outputs")
		}
		outputFileName := testCase.OutputFile
		if strings.TrimSpace(outputFileName) == "" {
			outputFileName = wp.buildOutputFileName(testCase)
		}
		outputPath := filepath.Join(outputDir, outputFileName)
		args = append(args, "-output-file", outputPath)
	}

	// Check if analyzer binary exists and is executable
	if _, err := os.Stat(wp.config.AnalyzerPath); err != nil {
		if wp.config.Progress {
			wp.logger.Errorf("[%s] Analysis: Analyzer binary not found: %s\n", execID, wp.config.AnalyzerPath)
		}
		return nil, 0, fmt.Errorf("analyzer binary not found: %s", wp.config.AnalyzerPath)
	}

	if wp.config.Progress {
		wp.logger.Printf("[%s] Analysis: Executing %s %s\n", execID, wp.config.AnalyzerPath, strings.Join(args, " "))
		wp.logger.Printf("[%s] Analysis: Working directory: %s\n", execID, repoPath)
	}

	// Run analyzer
	ctx, cancel := context.WithTimeout(wp.ctx, 10*time.Minute)
	defer cancel()

	cmd := exec.CommandContext(ctx, wp.config.AnalyzerPath, args...)
	// Set working directory to the repository path (if needed by analyzer)
	// cmd.Dir = repoPath
	var stdoutBuf, stderrBuf bytes.Buffer
	cmd.Stdout = &stdoutBuf
	cmd.Stderr = &stderrBuf

	if err := cmd.Run(); err != nil {
		// Check if it's a timeout error
		if ctx.Err() == context.DeadlineExceeded {
			if wp.config.Progress {
				wp.logger.Errorf("[%s] Analysis: Command timed out after 5 minutes\n", execID)
				if stderr := strings.TrimSpace(stderrBuf.String()); stderr != "" {
					wp.logger.Errorf("[%s] Analysis: Stderr before timeout: %s\n", execID, stderr)
				}
			}
			return nil, 0, fmt.Errorf("analyzer timed out after 5 minutes")
		}

		errorMsg := strings.TrimSpace(stderrBuf.String())
		if wp.config.Progress {
			if errorMsg != "" {
				wp.logger.Errorf("[%s] Analysis: Command failed: %s (exit code: %v)\n", execID, errorMsg, err)
			} else {
				wp.logger.Errorf("[%s] Analysis: Command failed with exit code: %v\n", execID, err)
			}
		}

		if errorMsg != "" {
			return nil, 0, fmt.Errorf("analyzer failed: %s (exit code: %v)", errorMsg, err)
		}
		return nil, 0, fmt.Errorf("analyzer failed with exit code: %v", err)
	}

	// Parse JSON output
	var results []PackageResult
	output := stdoutBuf.Bytes()
	if len(output) > 0 {
		if err := json.Unmarshal(output, &results); err != nil {
			outputStr := strings.TrimSpace(string(output))
			if len(outputStr) > 200 {
				outputStr = outputStr[:200] + "..."
			}
			if wp.config.Progress {
				wp.logger.Errorf("[%s] Analysis: Failed to parse JSON output (output: %q): %v\n", execID, outputStr, err)
			}
			return nil, 0, fmt.Errorf("failed to parse JSON (output: %q): %w", outputStr, err)
		}
	}

	// Extract total packages from stderr (if available)
	totalPackages := len(results)

	return results, totalPackages, nil
}

func (wp *WorkerPool) resultsHaveImpact(results []PackageResult) bool {
	for _, pkg := range results {
		if len(pkg.ImpactedFiles) > 0 || len(pkg.UsedSymbols) > 0 {
			return true
		}
	}
	return false
}

func sanitizeForFilename(value string) string {
	replacer := strings.NewReplacer(
		" ", "_",
		"/", "_",
		"\\", "_",
		"@", "_",
		":", "_",
	)
	return replacer.Replace(value)
}

func (wp *WorkerPool) buildOutputFileName(testCase TestCase) string {
	component := sanitizeForFilename(testCase.Component)
	branch := testCase.Branch
	if branch == "" {
		branch = "unknown-branch"
	}
	branchSafe := sanitizeForFilename(strings.ReplaceAll(branch, "-", "_"))
	return fmt.Sprintf("%s_%s_out.go", component, branchSafe)
}

func (wp *WorkerPool) generateCodeExtraction(execID, repoPath string, testCase TestCase, outputFile string) error {
	outputDir := strings.TrimSpace(wp.config.OutputDir)
	if outputDir == "" {
		outputDir = filepath.Join(wp.baseTempDir, "analysis_outputs")
	}
	if err := os.MkdirAll(outputDir, 0755); err != nil {
		return fmt.Errorf("failed to create output directory: %w", err)
	}

	outputPath := filepath.Join(outputDir, outputFile)

	if _, err := os.Stat(wp.config.AnalyzerPath); err != nil {
		return fmt.Errorf("analyzer binary not found: %w", err)
	}

	args := []string{
		"-repo", repoPath,
		"-pkg", testCase.Pkg,
		"-extract-code",
		"-output-file", outputPath,
	}

	if testCase.Workers != "" {
		args = append(args, "-workers", testCase.Workers)
	}
	if testCase.FileWorkers != "" {
		args = append(args, "-file-workers", testCase.FileWorkers)
	}
	if testCase.Progress == "true" {
		args = append(args, "-progress")
	}
	if testCase.SignaturesOnly == "true" {
		args = append(args, "-signatures-only")
	}

	ctx, cancel := context.WithTimeout(wp.ctx, 5*time.Minute)
	defer cancel()

	cmd := exec.CommandContext(ctx, wp.config.AnalyzerPath, args...)
	var stdoutBuf, stderrBuf bytes.Buffer
	cmd.Stdout = &stdoutBuf
	cmd.Stderr = &stderrBuf

	if wp.config.Progress {
		wp.logger.Printf("[%s] Extraction: Executing %s %s\n", execID, wp.config.AnalyzerPath, strings.Join(args, " "))
		wp.logger.Printf("[%s] Extraction: Output file: %s\n", execID, outputPath)
	}

	if err := cmd.Run(); err != nil {
		if ctx.Err() == context.DeadlineExceeded {
			if wp.config.Progress {
				wp.logger.Errorf("[%s] Extraction: Command timed out after 5 minutes\n", execID)
				if stderr := strings.TrimSpace(stderrBuf.String()); stderr != "" {
					wp.logger.Errorf("[%s] Extraction: Stderr before timeout: %s\n", execID, stderr)
				}
			}
			return fmt.Errorf("code extraction timed out after 5 minutes")
		}

		errorMsg := strings.TrimSpace(stderrBuf.String())
		if errorMsg != "" {
			return fmt.Errorf("%s (exit code: %v)", errorMsg, err)
		}
		return fmt.Errorf("exit code: %v", err)
	}

	if wp.config.Progress {
		wp.logger.Printf("[%s] Extraction: ✓ Code saved to %s\n", execID, outputPath)
	}

	return nil
}

// recordError records an error for debugging and analysis
func (wp *WorkerPool) recordError(component, errorType, message string, duration time.Duration) {
	wp.errorsMux.Lock()
	defer wp.errorsMux.Unlock()

	wp.errors = append(wp.errors, ErrorSummary{
		Component:    component,
		ErrorType:    errorType,
		ErrorMessage: message,
		Timestamp:    time.Now(),
		Duration:     duration,
	})
}

// printErrorSummary prints a summary of all errors encountered
func (wp *WorkerPool) printErrorSummary() {
	wp.errorsMux.Lock()
	defer wp.errorsMux.Unlock()

	if len(wp.errors) == 0 {
		return
	}

	wp.logger.Printf("\n=== ERROR SUMMARY ===\n")
	errorTypes := make(map[string]int)

	for _, err := range wp.errors {
		errorTypes[err.ErrorType]++
		wp.logger.Printf("[%s] %s: %s (%s)\n",
			err.ErrorType, err.Component, err.ErrorMessage,
			err.Timestamp.Format("15:04:05"))
	}

	wp.logger.Printf("\nError Breakdown:\n")
	for errType, count := range errorTypes {
		wp.logger.Printf("  %s: %d\n", errType, count)
	}
	wp.logger.Printf("Total Errors: %d\n", len(wp.errors))
}

// countTotalFiles counts total impacted files across all results
func (wp *WorkerPool) countTotalFiles(results []PackageResult) int {
	totalFiles := 0
	for _, pkg := range results {
		totalFiles += len(pkg.ImpactedFiles)
	}
	return totalFiles
}

// Helper functions
func (ia *IntegratedAnalyzer) extractBaseRepositoryURL(fullURL string) string {
	cleanURL := strings.TrimSpace(fullURL)
	cleanURL = strings.TrimSuffix(cleanURL, ".git")
	cleanURL = strings.TrimSuffix(cleanURL, "/")

	// Expect URLs in the form https://github.com/openshift/<component>
	if regexp.MustCompile(`^https://github\.com/[^/]+/[^/]+$`).MatchString(cleanURL) {
		return cleanURL
	}

	re := regexp.MustCompile(`(https://github\.com/[^/]+/[^/]+)`)
	matches := re.FindStringSubmatch(cleanURL)
	if len(matches) >= 2 {
		return matches[1]
	}

	return cleanURL
}

func (ia *IntegratedAnalyzer) extractRepoName(repoURL string) string {
	// Expect URLs in the form: https://github.com/openshift/<component>
	cleanURL := strings.TrimSuffix(repoURL, ".git")
	cleanURL = strings.TrimSuffix(cleanURL, "/")

	re := regexp.MustCompile(`github\.com/[^/]+/([^/]+)$`)
	matches := re.FindStringSubmatch(cleanURL)
	if len(matches) == 2 {
		repoName := matches[1]
		if ia.isValidComponentName(repoName) {
			return repoName
		}
	}

	return "unknown-repo"
}

// isValidComponentName checks if a component name is valid (not a commit hash)
func (ia *IntegratedAnalyzer) isValidComponentName(component string) bool {
	// Skip if it looks like a commit hash (all hex characters, 7+ chars)
	if len(component) >= 7 && len(component) <= 40 {
		isHex := true
		for _, char := range component {
			if !((char >= '0' && char <= '9') || (char >= 'a' && char <= 'f') || (char >= 'A' && char <= 'F')) {
				isHex = false
				break
			}
		}
		if isHex {
			return false // This looks like a commit hash
		}
	}

	// Valid component names should contain letters/hyphens (like "cloud-provider-aws")
	hasLetter := false
	for _, char := range component {
		if (char >= 'a' && char <= 'z') || (char >= 'A' && char <= 'Z') {
			hasLetter = true
			break
		}
	}

	return hasLetter
}

// convertComponentToURL converts a component name back to a full GitHub URL
// For backward compatibility and cloning purposes
func (ia *IntegratedAnalyzer) convertComponentToURL(component string) string {
	// If it's already a full URL, return as is
	if strings.HasPrefix(component, "http") || strings.HasPrefix(component, "git@") {
		return component
	}

	// Convert component name to OpenShift GitHub URL
	return fmt.Sprintf("https://github.com/openshift/%s", component)
}

func parseBranchFromURL(url string) string {
	re := regexp.MustCompile(`release/(\d+)\.(\d+)\.\d+`)
	matches := re.FindStringSubmatch(url)
	if len(matches) >= 3 {
		return fmt.Sprintf("release-%s.%s", matches[1], matches[2])
	}
	return "unknown-branch"
}

func (ia *IntegratedAnalyzer) parseGitHubURL(repoURL string) (string, string) {
	re := regexp.MustCompile(`github\.com/([^/]+)/([^/]+)`)
	matches := re.FindStringSubmatch(repoURL)
	if len(matches) >= 3 {
		return matches[1], strings.TrimSuffix(matches[2], ".git")
	}
	return "", ""
}

func (ia *IntegratedAnalyzer) cloneRepositoryForInspection(ctx context.Context, repoURL, branch string) (string, error) {
	repoName := ia.extractRepoName(repoURL)
	if repoName == "" || repoName == "unknown-repo" {
		repoName = "repo"
	}
	replacer := strings.NewReplacer("/", "_", "\\", "_", ":", "_", "@", "_")
	safeName := replacer.Replace(repoName)
	repoPath := filepath.Join(ia.tempDir, fmt.Sprintf("%s", safeName))

	cloneCtx, cancel := context.WithTimeout(ctx, 5*time.Minute)
	defer cancel()

	args := []string{"clone", "--depth", "1", "--single-branch"}
	if branch != "" && branch != "unknown-branch" {
		args = append(args, "-b", branch)
	}
	args = append(args, repoURL, repoPath)

	cmd := exec.CommandContext(cloneCtx, "git", args...)
	// Set git configurations for better handling of large repositories
	cmd.Env = append(os.Environ(),
		"GIT_HTTP_LOW_SPEED_LIMIT=1000", // Minimum transfer speed (bytes/sec)
		"GIT_HTTP_LOW_SPEED_TIME=300",   // Time limit for low speed (seconds)
		"GIT_HTTP_MAX_REQUESTS=3",       // Max concurrent HTTP requests per git process
	)
	if err := cmd.Run(); err != nil {
		os.RemoveAll(repoPath)
		return "", fmt.Errorf("git clone failed: %w", err)
	}

	return repoPath, nil
}

func (ia *IntegratedAnalyzer) listRepositoryFiles(ctx context.Context, repoPath string) ([]string, error) {
	lsCtx, cancel := context.WithTimeout(ctx, 2*time.Minute)
	defer cancel()

	baseArgs := []string{"ls-tree", "-r", "--full-tree", "--name-only", "HEAD"}
	output, err := ia.runGitListCommand(lsCtx, repoPath, baseArgs)
	if err != nil {
		return nil, fmt.Errorf("git ls-tree failed: %w", err)
	}

	trimmedOutput := strings.TrimSpace(string(output))
	if trimmedOutput == "" {
		return []string{}, nil
	}

	lines := strings.Split(trimmedOutput, "\n")
	filePaths := make([]string, 0, len(lines))
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		if isInVendorDirectory(line) || isInExcludedDirectory(line) {
			continue
		}
		filePaths = append(filePaths, line)
	}

	return filePaths, nil
}

func (ia *IntegratedAnalyzer) runGitListCommand(ctx context.Context, repoPath string, args []string) ([]byte, error) {
	cmd := exec.CommandContext(ctx, "git", args...)
	cmd.Dir = repoPath
	output, err := cmd.CombinedOutput()
	if err != nil {
		trimmed := strings.TrimSpace(string(output))
		if trimmed != "" {
			return nil, fmt.Errorf("%s", trimmed)
		}
		return nil, err
	}
	return output, nil
}

func (ia *IntegratedAnalyzer) buildTestCaseFromProject(project GoProject) TestCase {
	componentName := ia.extractRepoName(project.RepoURL)
	branch := project.SelectedBranch
	if branch == "" || branch == "unknown-branch" {
		branch = ia.releaseBranch
	}

	extractCode := ia.config.ExtractCode
	signaturesOnly := ia.config.SignaturesOnly && extractCode

	return TestCase{
		Serial:               "",
		Component:            componentName,
		Branch:               branch,
		Pkg:                  ia.config.PackageName,
		Progress:             "true",
		Workers:              strconv.Itoa(ia.config.Workers),
		FileWorkers:          strconv.Itoa(ia.config.FileWorkers),
		ExtractCode:          strconv.FormatBool(extractCode),
		OutputFile:           "",
		SignaturesOnly:       strconv.FormatBool(signaturesOnly),
		GoModDetected:        strconv.FormatBool(project.GoModDetected),
		GoModuleCount:        strconv.Itoa(project.GoModuleCount),
		LocalClonePath:       project.ClonePath,
		InitialCloneDuration: project.InitialCloneDuration,
		Impacted:             "",
		TotalPackagesFound:   "",
		DirectDependencies:   "",
		VendoredDeps:         "",
		TotalImpactedFiles:   "",
		TotalUniqueSymbols:   "",
		CloneDuration:        "",
		ExecutionTime:        "",
		AnalysisRate:         "",
	}
}

func decorateTestCaseWithResult(result *AnalysisResult) {
	testCase := &result.TestCase
	if !strings.EqualFold(testCase.ExtractCode, "true") {
		testCase.SignaturesOnly = "false"
	}
	effectiveClone := result.CloneDuration
	if effectiveClone == 0 && testCase.InitialCloneDuration > 0 {
		effectiveClone = testCase.InitialCloneDuration
	}
	result.CloneDuration = effectiveClone

	if result.Success {
		// Deduplicate packages and their impacted files
		dedupedResults := deduplicatePackageResults(result.Results)

		directDeps := 0
		vendoredDeps := 0
		totalFiles := 0
		symbolSet := make(map[string]bool)
		impacted := false

		for _, pkg := range dedupedResults {
			if pkg.DirectDependency {
				directDeps++
			}
			if pkg.Vendored {
				vendoredDeps++
			}
			totalFiles += len(pkg.ImpactedFiles)
			for _, symbol := range pkg.UsedSymbols {
				symbolSet[symbol] = true
			}
			if len(pkg.ImpactedFiles) > 0 || len(pkg.UsedSymbols) > 0 {
				impacted = true
			}
		}

		// Update TotalPackages with deduplicated count
		result.TotalPackages = len(dedupedResults)

		testCase.Impacted = "FALSE"
		if impacted {
			testCase.Impacted = "TRUE"
		}
		testCase.TotalPackagesFound = strconv.Itoa(result.TotalPackages)
		testCase.DirectDependencies = strconv.Itoa(directDeps)
		testCase.VendoredDeps = strconv.Itoa(vendoredDeps)
		testCase.TotalImpactedFiles = strconv.Itoa(totalFiles)
		testCase.TotalUniqueSymbols = strconv.Itoa(len(symbolSet))
		testCase.CloneDuration = fmt.Sprintf("%.2f seconds", effectiveClone.Seconds())
		testCase.ExecutionTime = fmt.Sprintf("%.2f seconds", result.ExecDuration.Seconds())
		if result.ExecDuration.Seconds() > 0 {
			rate := float64(result.TotalPackages) / result.ExecDuration.Seconds()
			testCase.AnalysisRate = fmt.Sprintf("%.2f packages/sec", rate)
		} else {
			testCase.AnalysisRate = "0.00 packages/sec"
		}
	} else {
		testCase.Impacted = "ERROR"
		testCase.TotalPackagesFound = "0"
		testCase.DirectDependencies = "0"
		testCase.VendoredDeps = "0"
		testCase.TotalImpactedFiles = "0"
		testCase.TotalUniqueSymbols = "0"
		if effectiveClone > 0 {
			testCase.CloneDuration = fmt.Sprintf("%.2f seconds", effectiveClone.Seconds())
		} else {
			testCase.CloneDuration = "ERROR"
		}
		testCase.ExecutionTime = "ERROR"
		testCase.AnalysisRate = "ERROR"
	}
}

func buildCSVRow(testCase TestCase) []string {
	return []string{
		testCase.Serial,
		testCase.Component,
		testCase.Branch,
		testCase.Pkg,
		testCase.Progress,
		testCase.Workers,
		testCase.FileWorkers,
		testCase.ExtractCode,
		testCase.OutputFile,
		testCase.SignaturesOnly,
		testCase.GoModDetected,
		testCase.GoModuleCount,
		testCase.Impacted,
		testCase.TotalPackagesFound,
		testCase.DirectDependencies,
		testCase.VendoredDeps,
		testCase.TotalImpactedFiles,
		testCase.TotalUniqueSymbols,
		testCase.CloneDuration,
		testCase.ExecutionTime,
		testCase.AnalysisRate,
	}
}

func (ia *IntegratedAnalyzer) writeResultsToCSV(writer *csv.Writer, results <-chan AnalysisResult) (PipelineSummary, error) {
	summary := PipelineSummary{}
	serial := 1
	for result := range results {
		summary.Total++
		if result.Success {
			summary.Success++
		} else {
			summary.Failed++
		}

		decorateTestCaseWithResult(&result)
		result.TestCase.Serial = strconv.Itoa(serial)
		serial++
		if err := writer.Write(buildCSVRow(result.TestCase)); err != nil {
			return summary, err
		}
	}

	writer.Flush()
	if err := writer.Error(); err != nil {
		return summary, err
	}

	return summary, nil
}

func (ia *IntegratedAnalyzer) generateCSV(goProjects []GoProject) (string, error) {
	if ia.config.OutputCSV == "" {
		ia.config.OutputCSV = fmt.Sprintf("integrated_test_cases_%d.csv", time.Now().Unix())
	}

	file, err := os.Create(ia.config.OutputCSV)
	if err != nil {
		return "", err
	}
	defer file.Close()

	writer := csv.NewWriter(file)
	defer writer.Flush()

	// Write header
	header := []string{
		"S.No.", "component", "branch", "pkg", "progress", "workers", "file-workers", "extract-code",
		"output-file", "signatures-only", "Go.mod Detected", "Go Module Count",
		"Impacted", "Total Packages Found", "Direct Dependencies", "Vendored Dependencies",
		"Total Impacted Files", "Total Unique Symbols", "Clone Duration", "Execution Time", "Analysis Rate",
	}
	writer.Write(header)

	defaultBranch := ia.releaseBranch
	extractCode := ia.config.ExtractCode
	signaturesOnly := ia.config.SignaturesOnly && extractCode

	// Write rows
	rowNum := 1
	for _, project := range goProjects {
		branch := project.SelectedBranch
		if branch == "" || branch == "unknown-branch" {
			branch = defaultBranch
		}

		componentName := ia.extractRepoName(project.RepoURL)

		// Debug logging for component name extraction
		if ia.config.Progress {
			fmt.Printf("  CSV Generation: URL='%s' -> Component='%s'\n", project.RepoURL, componentName)
		}

		// Validate component name before adding to CSV
		if !ia.isValidComponentName(componentName) {
			fmt.Printf("  Warning: Invalid component name '%s' from URL '%s' - skipping\n", componentName, project.RepoURL)
			continue
		}

		row := []string{
			strconv.Itoa(rowNum), // Serial number (1-based)
			componentName,        // Component name instead of full URL
			branch,
			ia.config.PackageName,
			"true",
			strconv.Itoa(ia.config.Workers),
			strconv.Itoa(ia.config.FileWorkers),
			strconv.FormatBool(extractCode),
			"",
			strconv.FormatBool(signaturesOnly),
			strconv.FormatBool(project.GoModDetected),
			strconv.Itoa(project.GoModuleCount),
			"", "", "", "", "", "", "", "", "", // Result columns (empty initially)
		}
		writer.Write(row)
		rowNum++
	}

	return ia.config.OutputCSV, nil
}

func (ia *IntegratedAnalyzer) readTestCases(csvFile string) ([]TestCase, error) {
	file, err := os.Open(csvFile)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	reader := csv.NewReader(file)
	records, err := reader.ReadAll()
	if err != nil {
		return nil, err
	}

	if len(records) < 2 {
		return nil, fmt.Errorf("CSV file has no data rows")
	}

	header := records[0]
	var testCases []TestCase

	for _, record := range records[1:] {
		testCase := TestCase{}
		for i, value := range record {
			if i < len(header) {
				switch header[i] {
				case "component":
					testCase.Component = value
				case "repo": // Backward compatibility
					testCase.Component = value
				case "branch":
					testCase.Branch = value
				case "pkg":
					testCase.Pkg = value
				case "progress":
					testCase.Progress = value
				case "workers":
					testCase.Workers = value
				case "file-workers":
					testCase.FileWorkers = value
				case "extract-code":
					testCase.ExtractCode = value
				case "output-file":
					testCase.OutputFile = value
				case "signatures-only":
					testCase.SignaturesOnly = value
				case "Go Module Count":
					testCase.GoModuleCount = value
				case "Go.mod Detected":
					testCase.GoModDetected = value
				case "Impacted":
					testCase.Impacted = value
				case "Total Packages Found":
					testCase.TotalPackagesFound = value
				case "Direct Dependencies":
					testCase.DirectDependencies = value
				case "Vendored Dependencies":
					testCase.VendoredDeps = value
				case "Total Impacted Files":
					testCase.TotalImpactedFiles = value
				case "Total Unique Symbols":
					testCase.TotalUniqueSymbols = value
				case "Clone Duration":
					testCase.CloneDuration = value
				case "Execution Time":
					testCase.ExecutionTime = value
				case "Analysis Rate":
					testCase.AnalysisRate = value
				}
			}
		}
		if !strings.EqualFold(testCase.ExtractCode, "true") {
			testCase.SignaturesOnly = "false"
		}
		testCases = append(testCases, testCase)
	}

	return testCases, nil
}

func (ia *IntegratedAnalyzer) updateCSVWithResults(csvFile string, results []AnalysisResult) error {
	// Create updated test cases
	var updatedTestCases []TestCase

	for _, result := range results {
		testCase := result.TestCase
		if !strings.EqualFold(testCase.ExtractCode, "true") {
			testCase.SignaturesOnly = "false"
		}

		if result.Success {
			// Deduplicate packages and their impacted files
			dedupedResults := deduplicatePackageResults(result.Results)

			// Calculate metrics
			var directDeps, vendoredDeps, totalFiles, totalSymbols int
			symbolSet := make(map[string]bool)
			impacted := false

			for _, pkg := range dedupedResults {
				if pkg.DirectDependency {
					directDeps++
				}
				if pkg.Vendored {
					vendoredDeps++
				}
				totalFiles += len(pkg.ImpactedFiles)

				for _, symbol := range pkg.UsedSymbols {
					symbolSet[symbol] = true
				}

				if len(pkg.ImpactedFiles) > 0 || len(pkg.UsedSymbols) > 0 {
					impacted = true
				}
			}

			totalSymbols = len(symbolSet)

			// Update TotalPackages with deduplicated count
			result.TotalPackages = len(dedupedResults)

			// Update test case with results
			if impacted {
				testCase.Impacted = "TRUE"
			} else {
				testCase.Impacted = "FALSE"
			}
			testCase.TotalPackagesFound = strconv.Itoa(result.TotalPackages)
			testCase.DirectDependencies = strconv.Itoa(directDeps)
			testCase.VendoredDeps = strconv.Itoa(vendoredDeps)
			testCase.TotalImpactedFiles = strconv.Itoa(totalFiles)
			testCase.TotalUniqueSymbols = strconv.Itoa(totalSymbols)
			testCase.CloneDuration = fmt.Sprintf("%.2f seconds", result.CloneDuration.Seconds())
			testCase.ExecutionTime = fmt.Sprintf("%.2f seconds", result.ExecDuration.Seconds())

			if result.ExecDuration.Seconds() > 0 {
				rate := float64(result.TotalPackages) / result.ExecDuration.Seconds()
				testCase.AnalysisRate = fmt.Sprintf("%.2f packages/sec", rate)
			}
		} else {
			testCase.Impacted = "ERROR"
			testCase.TotalPackagesFound = "0"
			testCase.DirectDependencies = "0"
			testCase.VendoredDeps = "0"
			testCase.TotalImpactedFiles = "0"
			testCase.TotalUniqueSymbols = "0"
			testCase.CloneDuration = "ERROR"
			testCase.ExecutionTime = "ERROR"
			testCase.AnalysisRate = "ERROR"
		}

		updatedTestCases = append(updatedTestCases, testCase)
	}

	// Write updated CSV
	file, err := os.Create(csvFile)
	if err != nil {
		return err
	}
	defer file.Close()

	writer := csv.NewWriter(file)
	defer writer.Flush()

	// Write header
	header := []string{
		"S.No.", "component", "branch", "pkg", "progress", "workers", "file-workers", "extract-code",
		"output-file", "signatures-only", "Go.mod Detected", "Go Module Count",
		"Impacted", "Total Packages Found", "Direct Dependencies", "Vendored Dependencies",
		"Total Impacted Files", "Total Unique Symbols", "Clone Duration", "Execution Time", "Analysis Rate",
	}
	writer.Write(header)

	// Write data rows
	for i, testCase := range updatedTestCases {
		row := []string{
			strconv.Itoa(i + 1), // Serial number (1-based)
			testCase.Component, testCase.Branch, testCase.Pkg, testCase.Progress,
			testCase.Workers, testCase.FileWorkers, testCase.ExtractCode, testCase.OutputFile,
			testCase.SignaturesOnly, testCase.GoModDetected, testCase.GoModuleCount,
			testCase.Impacted, testCase.TotalPackagesFound, testCase.DirectDependencies,
			testCase.VendoredDeps, testCase.TotalImpactedFiles, testCase.TotalUniqueSymbols,
			testCase.CloneDuration, testCase.ExecutionTime, testCase.AnalysisRate,
		}
		writer.Write(row)
	}

	return nil
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func main() {
	runtime.GOMAXPROCS(16)

	config := &Config{
		Workers:        4,  // Default number of concurrent workers
		FileWorkers:    10, // Default file workers
		AnalyzerPath:   "./repo_analyzer_exe",
		ExtractCode:    false, // Disable code extraction by default
		SignaturesOnly: false, // Signatures-only requires extract-code
	}

	// Parse command line arguments (simplified)
	args := os.Args[1:]
	for i := 0; i < len(args); i++ {
		switch args[i] {
		case "--package", "-p":
			if i+1 < len(args) {
				config.PackageName = args[i+1]
				i++
			}
		case "--url", "-u":
			if i+1 < len(args) {
				config.ReleaseURL = args[i+1]
				i++
			}
		case "--repo-url":
			if i+1 < len(args) {
				config.SingleRepoURL = args[i+1]
				i++
			}
		case "--repo-branch":
			if i+1 < len(args) {
				config.SingleRepoBranch = args[i+1]
				i++
			}
		case "--output", "-o":
			if i+1 < len(args) {
				config.OutputCSV = args[i+1]
				i++
			}
		case "--analyzer", "-a":
			if i+1 < len(args) {
				config.AnalyzerPath = args[i+1]
				i++
			}
		case "--workers", "-w":
			if i+1 < len(args) {
				if w, err := strconv.Atoi(args[i+1]); err == nil {
					config.Workers = w
				}
				i++
			}
		case "--skip-analysis":
			config.SkipAnalysis = true
		case "--force-rerun":
			config.ForceRerun = true
		case "--csv-only":
			if i+1 < len(args) {
				config.CSVOnly = args[i+1]
				i++
			}
		case "--progress":
			config.Progress = true
		case "--extract-code":
			config.ExtractCode = true
		case "--log-file":
			if i+1 < len(args) {
				config.LogFile = args[i+1]
				i++
			}
		case "--verbose":
			config.VerboseLogging = true
		case "--debug":
			config.DebugMode = true
		case "--output-dir":
			if i+1 < len(args) {
				config.OutputDir = args[i+1]
				i++
			}
		case "--signatures-only":
			config.SignaturesOnly = true
		case "--help", "-h":
			printUsage()
			return
		}
	}

	config.SingleRepoURL = strings.TrimSpace(config.SingleRepoURL)
	config.SingleRepoBranch = strings.TrimSpace(config.SingleRepoBranch)
	config.ReleaseBranch = strings.TrimSpace(config.ReleaseBranch)

	if config.ReleaseBranch == "" {
		config.ReleaseBranch = parseBranchFromURL(config.ReleaseURL)
	}
	if (config.ReleaseBranch == "" || config.ReleaseBranch == "unknown-branch") && config.SingleRepoBranch != "" {
		config.ReleaseBranch = config.SingleRepoBranch
	}

	if config.SingleRepoURL != "" && config.CSVOnly != "" {
		fmt.Println("Error: --repo-url cannot be combined with --csv-only")
		printUsage()
		os.Exit(1)
	}

	if config.SingleRepoURL == "" && config.ReleaseURL == "" && config.CSVOnly == "" {
		fmt.Println("Error: Release URL or --repo-url is required")
		printUsage()
		os.Exit(1)
	}

	if config.SignaturesOnly && !config.ExtractCode {
		fmt.Println("Warning: --signatures-only requires --extract-code. Disabling signatures-only.")
		config.SignaturesOnly = false
	}

	if config.PackageName == "" && config.CSVOnly == "" {
		fmt.Println("Error: Package name is required (use --package flag)")
		printUsage()
		os.Exit(1)
	}

	analyzer := NewIntegratedAnalyzer(config)
	if err := analyzer.Run(); err != nil {
		log.Fatalf("Error: %v", err)
	}
}

func printUsage() {
	fmt.Println(`
Usage: integrated_analyzer [OPTIONS]

OPTIONS:
  --package, -p     Package name to analyze (required)
  --url, -u         OpenShift release URL
  --repo-url URL    Analyze a single repository (skips scraping)
  --repo-branch BR  Branch to use with --repo-url
  --output, -o      Output CSV filename
  --analyzer, -a    Path to Go analyzer binary
  --workers, -w     Number of concurrent workers (default: 4)
  --skip-analysis   Skip analysis phase
  --force-rerun     Force rerun all tests
  --csv-only FILE   Run analysis only on existing CSV
  --progress        Show progress during execution
  --extract-code    Enable code extraction (default: false)
  --signatures-only Extract only function/method signatures (requires --extract-code)
  --log-file FILE   Write logs to specified file in addition to stdout
  --verbose         Enable verbose logging
  --debug           Enable debug mode
  --output-dir DIR  Directory to store analysis output files (default: temp_repos_<ts>/analysis_outputs)
  --help, -h        Show this help

Examples:
  integrated_analyzer --package golang.org/x/crypto/ssh
  integrated_analyzer --package golang.org/x/crypto/ssh --workers 16
  integrated_analyzer --package golang.org/x/crypto/ssh --skip-analysis
  integrated_analyzer --package golang.org/x/crypto/ssh --repo-url https://github.com/openshift/cluster-cloud-controller-manager-operator --repo-branch release-4.14
  integrated_analyzer --csv-only existing.csv --workers 12
  integrated_analyzer --package golang.org/x/crypto/ssh --output-dir ./crypto_analysis_results
  integrated_analyzer --csv-only existing.csv --extract-code  # Enable code extraction
`)
}
