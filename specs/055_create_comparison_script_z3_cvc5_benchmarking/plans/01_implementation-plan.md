# Implementation Plan: Task 55

- **Task**: 55 - Create comparison.py script for z3 vs cvc5 benchmarking
- **Status**: [NOT STARTED]
- **Effort**: 2.5 hours
- **Dependencies**: None (existing infrastructure supports all requirements)
- **Research Inputs**: specs/055_create_comparison_script_z3_cvc5_benchmarking/reports/01_comparison-script-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Create a standalone `comparison.py` script that imports examples from the logos theory examples module and systematically runs each example against both z3 and cvc5 solvers. The script will record results and timing data to `output.json` for analysis. The existing test infrastructure in `test_solver_comparison.py` provides proven patterns for solver switching, example execution, and result collection.

### Research Integration

Key findings from the research report:
- **Solver switching**: Requires three-step reset (clear_cli_backend, reset_registry, z3_shim._reset_backend)
- **Example structure**: All examples available via `all_subtheory_examples` dict organized by subtheory
- **Execution API**: Use `BuildExample` with mock module for running examples
- **Result extraction**: Use `example.model_structure.z3_model_status` and `z3_model_runtime`
- **Recommended location**: `code/src/model_checker/theory_lib/logos/comparison.py`

## Goals & Non-Goals

**Goals**:
- Create comparison.py script that benchmarks all logos examples against z3 and cvc5
- Output structured JSON with metadata, per-example results, and disagreement tracking
- Handle errors gracefully with per-example isolation
- Provide summary statistics by solver and subtheory

**Non-Goals**:
- Not adding this as a pytest test (already exists as `test_solver_comparison.py`)
- Not implementing parallel execution (sequential is safer for solver switching)
- Not adding visualization or plotting (output.json is for analysis)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Solver switching cache issues | H | L | Use proven three-step reset pattern from test_solver_comparison.py |
| Example timeout during benchmarking | M | M | Per-example try/except with timeout tracking |
| CVC5 not installed on target system | M | L | Graceful check with clear error message at start |
| Memory/performance issues with many examples | L | L | Sequential execution, progress reporting |

## Implementation Phases

### Phase 1: Core Script Structure [NOT STARTED]

**Goal**: Create the basic script skeleton with imports, dataclasses, and main() entry point

**Tasks**:
- [ ] Create `comparison.py` with file header and docstring
- [ ] Add all required imports (solver, theory, examples, builder)
- [ ] Define dataclasses for `ExampleResult`, `SolverSummary`, `BenchmarkOutput`
- [ ] Create main() function skeleton with argument parsing (--output flag)
- [ ] Add solver availability check at startup

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/comparison.py` - Create new file

**Verification**:
- Script runs without import errors
- `python comparison.py --help` shows usage
- Script exits with error if cvc5 not available

---

### Phase 2: Solver Switching and Example Running [NOT STARTED]

**Goal**: Implement the core functions for switching solvers and running examples

**Tasks**:
- [ ] Implement `switch_solver(backend: str)` function with three-step reset
- [ ] Implement `create_test_module(theory)` function (from test_solver_comparison.py)
- [ ] Implement `get_required_subtheories(subtheory: str)` function
- [ ] Implement `flatten_examples()` to enumerate all examples
- [ ] Implement `run_example_with_timing(example_case, theory)` with error handling

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/comparison.py` - Add functions

**Verification**:
- Can switch between z3 and cvc5 solvers
- Can run a single example and get result with timing
- Error handling works (bad example doesn't crash script)

---

### Phase 3: Benchmark Loop and JSON Output [NOT STARTED]

**Goal**: Implement the main benchmark loop and JSON output generation

**Tasks**:
- [ ] Implement main benchmark loop (iterate examples, run with both solvers)
- [ ] Build output structure with metadata (versions, platform, timestamp)
- [ ] Calculate summary statistics (passed, failed, times by solver)
- [ ] Calculate by-subtheory statistics
- [ ] Identify and record disagreements between solvers
- [ ] Write output to JSON file with proper formatting

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/comparison.py` - Add benchmark logic

**Verification**:
- Running script produces `output.json`
- JSON contains all required sections (metadata, summary, by_subtheory, results, disagreements)
- Results are correct for known examples

---

### Phase 4: Progress Reporting and Polish [NOT STARTED]

**Goal**: Add progress output, handle edge cases, and finalize script

**Tasks**:
- [ ] Add progress bar or status messages during benchmark
- [ ] Add timeout tracking (separate from errors)
- [ ] Add command-line flag to filter by subtheory (--subtheory flag)
- [ ] Add --verbose flag for detailed output
- [ ] Add version detection for z3 and cvc5 in metadata
- [ ] Test complete end-to-end run

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/comparison.py` - Polish and flags

**Verification**:
- Progress shown during execution
- `--subtheory modal` runs only modal examples
- `--verbose` shows per-example output
- Metadata includes solver versions

## Testing & Validation

- [ ] Script runs without errors: `python comparison.py`
- [ ] Output.json is valid JSON and parseable
- [ ] All subtheories are tested (extensional, modal, constitutive, counterfactual, relevance, first_order)
- [ ] Results match expectations from test_solver_comparison.py
- [ ] Disagreements section correctly identifies any solver differences
- [ ] Script handles cvc5-not-installed gracefully

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/logos/comparison.py` - Main script
- `output.json` - Generated benchmark results (when script runs)

## Rollback/Contingency

Since this is a new standalone script:
- No existing functionality affected
- If issues found, simply delete the script
- Existing test_solver_comparison.py continues to work for testing
