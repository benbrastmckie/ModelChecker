# Implementation Plan: Cross-Oracle Differential Testing Infrastructure

- **Task**: 109 - Cross-oracle differential testing infrastructure
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: 103 (OracleProvider implementation, completed)
- **Research Inputs**: specs/109_cross_oracle_differential_testing/reports/01_differential-testing.md
- **Artifacts**: plans/01_differential-testing-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Build a cross-oracle differential testing infrastructure that systematically compares the ModelChecker Z3OracleProvider against reference oracles across enumerated formulas. The primary test file implements a self-contained primitive formula enumerator (no BimodalHarness dependency for CI), a differential harness comparing MC oracle results against known-valid/invalid baselines and (optionally) the BimodalHarness Z3 oracle on temporal-only formulas, a JSON report generator for disagreement forensics, and CI integration via GitHub Actions workflow. The key semantic constraint is that the MC oracle and BH Z3 oracle disagree on box/diamond formulas (different accessibility semantics), so BH Z3 comparison is restricted to temporal-only formulas (atom, bot, imp, untl, snce only).

### Research Integration

Key findings integrated from the research report:
- BimodalHarness is available at `/home/benjamin/Projects/BimodalHarness` but must NOT be a CI dependency
- MC oracle uses universal-over-all-worlds box semantics; BH Z3 uses Kripke accessibility -- 4/18 disagreements at complexity <=3 are expected and correct
- `enumerate_up_to_complexity(5, ["p"])` yields ~150 formulas; temporal-only subset is ~50-80 formulas
- MockOracleProvider provides 10 hardcoded known-invalid formulas for spot-check validation
- Self-contained primitive formula enumerator recommended for CI independence
- Atom field name mismatch: MC uses `{"name": str}`, BH uses `{"base": str}` -- harness must normalize

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Self-contained primitive formula enumerator that generates all primitive-tag formulas up to a given complexity without external dependencies
- Differential test harness comparing MC oracle against reference baselines (known tautologies and known-invalid formulas from the 42-example regression suite)
- Optional BimodalHarness integration for temporal-only formula comparison, gracefully skipped when BH is unavailable
- JSON differential report format documenting agreements, disagreements, and metadata per formula
- CI workflow that runs the self-contained differential tests on every bimodal code change
- Pytest markers (`differential`, `slow`) for test selection

**Non-Goals**:
- Lean subprocess validation (requires Lean toolchain, not available in CI)
- Full BimodalHarness Z3 oracle comparison on box/diamond formulas (known semantic divergence)
- Performance benchmarking of oracle speed
- Modifying the MC oracle implementation itself

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Self-contained enumerator diverges from BH enumerator logic | M | M | Validate by cross-checking counts against BH at complexities 1-5 locally before CI deployment |
| Temporal-only filter misses formulas with nested box/diamond | H | L | Recursive `_is_temporal_only()` checks all child fields; unit test the filter itself |
| CI runner lacks Z3 dependency | H | M | `pip install -e .` in CI installs z3-solver from pyproject.toml; verify in workflow |
| Oracle API changes between tasks | M | L | Import `Z3OracleProvider` from `bimodal_logic` which is stable; test imports first |
| Formula enumeration at complexity 7 is slow (~18k formulas) | L | M | Mark complexity-7 tests as `@pytest.mark.slow`; CI runs only complexity <=5 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Self-Contained Formula Enumerator and Test Infrastructure [COMPLETED]

**Goal**: Implement a self-contained primitive formula enumerator and establish the test file skeleton with pytest markers.

**Tasks**:
- [ ] Create test file `code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py` with module docstring and imports
- [ ] Implement `_enumerate_primitive_formulas(max_complexity: int, atoms: list[str]) -> list[dict]` as a module-level helper that generates all primitive-tag JSON formulas (atom, bot, imp, box, untl, snce) up to the given structural complexity
- [ ] Implement `_formula_complexity(formula_json: dict) -> int` to compute structural node count
- [ ] Implement `_is_temporal_only(formula_json: dict) -> bool` to filter out box/diamond-containing formulas
- [ ] Write `TestFormulaEnumerator` class with tests:
  - [ ] `test_complexity_1_atoms_and_bot`: verify complexity-1 formulas are exactly the atoms plus bot
  - [ ] `test_complexity_counts_1_atom`: verify formula counts at complexities 1-3 with 1 atom match expected values
  - [ ] `test_all_formulas_valid_json`: verify every enumerated formula has valid `tag` field from the 6 primitive tags
  - [ ] `test_temporal_only_filter`: verify `_is_temporal_only` correctly identifies formulas with/without box
  - [ ] `test_complexity_function`: verify `_formula_complexity` returns correct counts for known formulas
- [ ] Add `differential` and `slow` pytest markers to `code/pyproject.toml`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py` - Create new file with enumerator and infrastructure tests
- `code/pyproject.toml` - Add `differential` and `slow` pytest markers

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py::TestFormulaEnumerator -v` passes all tests
- Formula counts at complexity 1 with 1 atom = 2 (atom_p, bot)
- `_is_temporal_only` returns False for `{"tag": "box", "child": {"tag": "atom", "name": "p"}}` and True for `{"tag": "untl", "left": {"tag": "atom", "name": "p"}, "right": {"tag": "bot"}}`

---

### Phase 2: Differential Test Harness with Known-Formula Baselines [COMPLETED]

**Goal**: Build the core differential harness that compares MC oracle results against known-valid and known-invalid formula baselines from the existing 42-example regression suite.

**Tasks**:
- [ ] Write `TestDifferentialInfrastructure` class with smoke tests:
  - [ ] `test_oracle_import`: verify `Z3OracleProvider` can be imported from `bimodal_logic`
  - [ ] `test_oracle_instantiation`: verify oracle can be instantiated and has `find_countermodel` method
  - [ ] `test_enumerator_produces_formulas`: verify enumerator produces non-empty list at complexity 3
- [ ] Extract known-tautology and known-invalid formula lists from the existing `examples.py` regression suite (use `countermodel_examples` and `theorem_examples` imports)
- [ ] Write `TestKnownFormulaBaseline` class:
  - [ ] `test_known_tautologies_return_none`: for each known tautology, verify MC oracle returns None (UNSAT)
  - [ ] `test_known_invalid_return_countermodel`: for each known-invalid formula, verify MC oracle returns a dict (SAT)
  - [ ] `test_baseline_coverage`: verify at least 20 formulas are tested in each category
- [ ] Implement `_run_differential_comparison(oracle, formula_json, reference_result) -> dict` helper that returns a structured comparison record with formula_json, mc_result (SAT/UNSAT/TIMEOUT), reference_result, agreement flag, and metadata (complexity, temporal_depth, has_box)
- [ ] Write `TestDifferentialComparison` class:
  - [ ] `test_comparison_record_structure`: verify the comparison record has all required fields
  - [ ] `test_agreement_on_known_tautology`: verify agreement=True for a known tautology
  - [ ] `test_agreement_on_known_invalid`: verify agreement=True for a known-invalid formula

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py` - Add harness classes and comparison helper

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py::TestDifferentialInfrastructure -v` passes
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py::TestKnownFormulaBaseline -v` passes
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py::TestDifferentialComparison -v` passes

---

### Phase 3: BimodalHarness Integration (Optional, Conditional Import) [COMPLETED]

**Goal**: Add conditional BimodalHarness integration for temporal-only formula comparison, with graceful skip when BH is unavailable.

**Tasks**:
- [ ] Implement BH import mechanism using `pytest.importorskip` with sys.path extension:
  ```python
  BH_SRC = Path("/home/benjamin/Projects/BimodalHarness/src")
  ```
- [ ] Write `_try_import_bimodal_harness() -> tuple[bool, module | None]` helper that returns (available, module) without raising
- [ ] Write `TestBimodalHarnessIntegration` class marked with `@pytest.mark.differential`:
  - [ ] `test_bh_available` (skip if not): verify BimodalHarness can be imported
  - [ ] `test_bh_enumerate_matches_self_contained`: compare BH `enumerate_up_to_complexity(3, ["p"])` counts against self-contained enumerator counts
  - [ ] `test_temporal_only_agreement_complexity_3`: enumerate temporal-only formulas at complexity <=3, run through both MC oracle and BH Z3 oracle, assert agreement on all
  - [ ] `test_temporal_only_agreement_complexity_5`: enumerate temporal-only formulas at complexity <=5, assert agreement (mark `@pytest.mark.slow` if >50 formulas)
  - [ ] `test_box_disagreements_documented`: enumerate box-containing formulas at complexity <=3, run both oracles, verify that disagreements exist (positive test that semantic divergence is handled)
- [ ] Implement `_atom_names(atoms: list[dict]) -> set[str]` helper to normalize MC `{"name": str}` vs BH `{"base": str}` atom dicts
- [ ] Write `TestMockOracleSpotCheck` class (uses BH MockOracleProvider, skip if BH unavailable):
  - [ ] `test_spot_check_all_10`: for each of 10 `SPOT_CHECK_FORMULAS`, verify MC oracle also returns SAT (finds countermodel)

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py` - Add BH integration classes

**Verification**:
- When BH is available: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py::TestBimodalHarnessIntegration -v` passes (all temporal-only formulas agree)
- When BH is unavailable: tests are skipped with clear skip reason
- `TestMockOracleSpotCheck::test_spot_check_all_10` passes when BH is present

---

### Phase 4: Differential Report Format and Generation [COMPLETED]

**Goal**: Implement JSON differential report generation for systematic scans, with forensic detail for disagreements.

**Tasks**:
- [ ] Define `DifferentialReport` dataclass or TypedDict with fields: timestamp, mc_oracle_id, ref_oracle_id, total_formulas, agreements, disagreements, timeout_count, entries (list of comparison records)
- [ ] Implement `_generate_differential_report(oracle, formulas, reference_oracle_fn, oracle_ids) -> dict` that runs all formulas through both oracles and returns the report dict
- [ ] Implement `_write_report_json(report: dict, output_path: Path) -> None` that writes the JSON report file
- [ ] Write `TestDifferentialReport` class:
  - [ ] `test_report_structure`: verify report dict has all required top-level fields
  - [ ] `test_report_entries_complete`: verify each entry has formula_json, complexity, temporal_depth, mc_result, ref_result, agreement
  - [ ] `test_report_counts_consistent`: verify agreements + disagreements + timeouts == total_formulas
  - [ ] `test_report_json_serializable`: verify `json.dumps(report)` succeeds without error
- [ ] Write `TestFullScanReport` class marked `@pytest.mark.slow`:
  - [ ] `test_complexity_5_scan`: enumerate all primitive formulas at complexity <=5 with 1 atom, generate report, verify zero unexpected disagreements (box disagreements with BH are expected, known-formula baselines must agree)
  - [ ] `test_report_writes_to_file`: verify report writes to a temp file and can be read back as valid JSON

**Timing**: 1 hour

**Depends on**: 2, 3

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py` - Add report generation and report tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py::TestDifferentialReport -v` passes
- Report JSON is valid and parseable
- Report counts are self-consistent

---

### Phase 5: CI Integration and Gate Validation [COMPLETED]

**Goal**: Add GitHub Actions workflow for differential tests and validate the full test gate.

**Tasks**:
- [ ] Create `.github/workflows/differential-tests.yml` with:
  - Trigger on push/PR to paths `code/src/bimodal_logic/**` and `code/src/model_checker/theory_lib/bimodal/**`
  - Python 3.12 setup
  - `pip install -e code/` to install bimodal-logic with z3-solver dependency
  - Run only non-slow, non-BH-dependent tests: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py -v -m "not slow" --ignore-glob="*bh*"`
- [ ] Write `TestCIGate` class (always runs, no BH dependency):
  - [ ] `test_self_contained_enumerator_complexity_5`: enumerate with self-contained enumerator, verify all formulas are valid JSON
  - [ ] `test_oracle_baseline_agreement`: run full known-formula baseline, verify 100% agreement
  - [ ] `test_temporal_only_self_consistency`: for all temporal-only formulas at complexity <=5, verify MC oracle returns consistent results (same result on repeated calls) -- state isolation check
- [ ] Run full test suite gate: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` to verify no regressions
- [ ] Verify the differential test file runs independently: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py -v -m "not slow"`

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `.github/workflows/differential-tests.yml` - Create new CI workflow
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py` - Add CI gate tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py -v -m "not slow"` passes all non-slow tests
- Full bimodal test suite passes with no regressions
- `.github/workflows/differential-tests.yml` is valid YAML

## Testing & Validation

- [ ] All `TestFormulaEnumerator` tests pass (Phase 1)
- [ ] All `TestDifferentialInfrastructure` and `TestKnownFormulaBaseline` tests pass (Phase 2)
- [ ] All `TestBimodalHarnessIntegration` tests pass when BH is available, skip cleanly when not (Phase 3)
- [ ] All `TestDifferentialReport` tests pass (Phase 4)
- [ ] All `TestCIGate` tests pass without BimodalHarness (Phase 5)
- [ ] Full bimodal test suite (`PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`) passes with no regressions
- [ ] Zero unexpected disagreements between MC oracle and known-formula baselines
- [ ] Temporal-only formulas show 100% agreement between MC oracle and BH Z3 oracle (when BH available)

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py` - Main differential test suite
- `.github/workflows/differential-tests.yml` - CI workflow for differential tests
- `code/pyproject.toml` - Updated with `differential` and `slow` pytest markers
- `specs/109_cross_oracle_differential_testing/plans/01_differential-testing-plan.md` - This plan
- `specs/109_cross_oracle_differential_testing/summaries/01_differential-testing-summary.md` - Implementation summary (generated on completion)

## Rollback/Contingency

All changes are additive (new test file, new CI workflow, new pytest markers). Rollback is straightforward:
- Delete `test_cross_oracle_differential.py` to remove all differential tests
- Delete `.github/workflows/differential-tests.yml` to remove CI workflow
- Remove `differential` and `slow` markers from `pyproject.toml`
- No existing code is modified; no regressions possible from rollback
