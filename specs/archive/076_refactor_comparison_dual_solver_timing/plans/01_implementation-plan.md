# Implementation Plan: Refactor comparison.py for Curated Dual-Solver Timing

- **Task**: 76 - refactor_comparison_dual_solver_timing
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_comparison-refactor-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/context/formats/plan-format.md
- **Type**: z3
- **Lean Intent**: false

## Overview

Refactor comparison.py to run a curated selection of 24 examples (4 per subtheory: 2 theorems + 2 countermodels) rather than all 100+ examples. For each example, run both z3 and cvc5, compare results (model found, no model, timeout), and record timing. The implementation follows a clean-break approach with a `--curated` flag to preserve existing full-benchmark capability.

### Research Integration

- Dual-solver infrastructure already exists in comparison.py with full cache invalidation
- Countermodel printing already suppressed in comparison mode (mock module uses `print_constraints: False`)
- Recommended curated examples identified by prefix pattern (EXT_, MOD_, CL_, CF_, REL_, FO_)
- Clean-break approach recommended: new `--curated` flag rather than modifying default behavior

## Goals & Non-Goals

**Goals**:
- Add `COMPARISON_EXAMPLES` constant with curated 24-example selection
- Add `get_curated_examples()` function for example retrieval
- Add `--curated` CLI flag to run curated examples instead of all
- Create simplified timing-focused output format
- Record per-solver timing with comparison metrics

**Non-Goals**:
- Changing the default behavior (all examples without flags)
- Modifying countermodel printing behavior (already suppressed)
- Adding new solver backends beyond z3/cvc5
- Changing the underlying BuildExample or theory infrastructure

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Example names changed | M | L | Verify all 24 example names exist before implementing |
| Timing inconsistency | L | L | Use existing `time.perf_counter()` approach |
| Output format breaks consumers | M | L | Keep JSON backward compatible, add new fields |

## Implementation Phases

### Phase 1: Add Curated Example Selection [COMPLETED]

**Goal**: Create `COMPARISON_EXAMPLES` constant and `get_curated_examples()` function

**Tasks**:
- [ ] Add `COMPARISON_EXAMPLES` dictionary at module level in `code/src/model_checker/theory_lib/logos/comparison.py`
- [ ] Implement `get_curated_examples()` function that filters `all_subtheory_examples`
- [ ] Add `--curated` argument to argument parser in `main()` function
- [ ] Update `run_benchmarks()` to use curated examples when `--curated` flag is set

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/comparison.py` - Add constant, function, and argument

**Verification**:
- Run `./code/comparison.py --curated --verbose` and verify 24 examples are executed
- Confirm examples are from all 6 subtheories (4 each)

---

### Phase 2: Simplified Timing Output [COMPLETED]

**Goal**: Create focused timing comparison output format with per-solver metrics

**Tasks**:
- [ ] Add `TimingSummary` dataclass for timing-specific statistics
- [ ] Add `faster_solver` and `time_ratio` fields to result records
- [ ] Create `compute_timing_comparison()` function for solver comparison stats
- [ ] Add `--format {full|timing}` argument to control output verbosity
- [ ] Update JSON output structure with `timing_summary` and `comparison_stats` sections

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/comparison.py` - Add timing dataclass, comparison logic, format flag

**Verification**:
- Run `./code/comparison.py --curated --format timing` and verify simplified output
- Confirm `timing_summary` includes per-solver stats (total, avg, fastest, slowest)
- Confirm `comparison_stats` includes agreement counts and z3/cvc5 faster counts

---

### Phase 3: CLI Enhancements and Documentation [COMPLETED]

**Goal**: Polish CLI interface and update docstrings

**Tasks**:
- [ ] Add `--table` flag for ASCII table output
- [ ] Implement `format_as_table()` function for human-readable console output
- [ ] Update module docstring with new flag documentation
- [ ] Update wrapper script docstring in `code/comparison.py`
- [ ] Test all flag combinations work correctly

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/comparison.py` - Add table output, update docstring
- `code/comparison.py` - Update usage docstring

**Verification**:
- Run `./code/comparison.py --curated --table` and verify ASCII table output
- Run `./code/comparison.py --help` and verify all new flags are documented
- Run all flag combinations and verify no errors

## Testing & Validation

- [ ] Run `./code/comparison.py` (no flags) - verify existing behavior unchanged
- [ ] Run `./code/comparison.py --curated` - verify 24 examples execute
- [ ] Run `./code/comparison.py --curated --verbose` - verify per-example output
- [ ] Run `./code/comparison.py --curated --format timing` - verify simplified JSON
- [ ] Run `./code/comparison.py --curated --table` - verify ASCII table
- [ ] Verify JSON output is valid and parseable with `jq`
- [ ] Verify both z3 and cvc5 results are recorded for each example

## Artifacts & Outputs

- `plans/01_implementation-plan.md` (this file)
- Modified `code/src/model_checker/theory_lib/logos/comparison.py`
- Modified `code/comparison.py` (docstring only)
- `summaries/01_implementation-summary.md` (after completion)

## Rollback/Contingency

- If implementation breaks existing behavior, revert changes to comparison.py
- All changes are additive (new constant, new function, new flags) - existing code paths unchanged
- Git commit at end of each phase enables granular rollback if needed
