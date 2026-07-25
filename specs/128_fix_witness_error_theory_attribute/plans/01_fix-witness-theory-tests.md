# Implementation Plan: Fix Witness Error `.theory` Contract Tests

- **Task**: 128 - Resolve the contradiction between the witness error classes and their tests
- **Status**: [COMPLETED]
- **Effort**: 0.75 hours
- **Dependencies**: None
- **Research Inputs**: specs/128_fix_witness_error_theory_attribute/reports/01_witness-error-theory-contract.md
- **Artifacts**: plans/01_fix-witness-theory-tests.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Two tests in `code/src/model_checker/theory_lib/tests/unit/test_error_handling.py` assert that
`WitnessRegistryError(...).theory` and `WitnessConstraintError(...).theory` equal `"exclusion"`,
but neither class sets a `theory` default, so both assertions receive `None` and fail. Research
established that the tests encode a stale pre-refactor contract: the hardcoded
`theory="exclusion"` default was deliberately removed because these classes are raised by BOTH
the exclusion and bimodal theories, and no theory-name plumbing exists at any raise site. The fix
is therefore in the tests, not in `errors.py`: construct the errors with an explicit `theory=`
kwarg, matching the pattern the sibling `test_witness_error_construction` in the same class
already uses, and record the reasoning in the test docstrings so the contract is not re-broken.

### Research Integration

Key findings carried into this plan (established, not re-litigated):

- `WitnessError -> TheoryError` sets no `theory` default; `TheoryError.__init__` defaults
  `theory=None` (`code/src/model_checker/theory_lib/errors.py:29-43`, `163-194`). No class in the
  hierarchy hardcodes a theory — every class is theory-agnostic and only call sites supply a
  `theory=` string.
- Five production raise sites exist across TWO theories — three under
  `theory_lib/exclusion/semantic/` (`registry.py`, `constraints.py`, `core.py`) and two under
  `theory_lib/bimodal/semantic/` (`witness_registry.py`, `witness_constraints.py`). None passes a
  `theory=` kwarg. Re-adding a `theory="exclusion"` class default would mislabel every bimodal
  witness error.
- The correct contract is already modelled one test above the broken pair
  (`test_witness_error_construction`, line 62-66) and in the sibling imposition test
  (`test_semantic_error_with_imposition_theory`, line 96-100): explicit `theory=` kwarg at
  construction, asserted back.
- Verified during planning: no other test in the repository asserts on `.theory` for any witness
  error class. The only `.theory` assertions live in this one file (lines 39, 66, 80, 86, 99, 136,
  155); lines 80 and 86 are the two failures, and the rest already pass. Phase 1 re-confirms this
  as a gate rather than trusting the planning-time grep.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No roadmap context provided in the delegation; no roadmap phases included.

## Goals & Non-Goals

**Goals**:
- `test_witness_registry_error_basic` and `test_witness_constraint_error_basic` pass.
- The full `test_error_handling.py` module passes (12 tests, 0 failures).
- The reasoning for the absence of a class-level `theory` default is recorded in the test file
  itself (docstrings), so a future reader does not "restore" the hardcoded default.
- No regressions in the exclusion and bimodal witness test suites.

**Non-Goals**:
- Any change to `code/src/model_checker/theory_lib/errors.py`. It is currently correct.
- Threading a theory identifier through the five production raise sites
  (`WitnessRegistry`/`WitnessConstraintGenerator` call chains). Architecturally reasonable but a
  separately-scoped change requiring new theory-name plumbing that does not exist today.
- Re-adding a `WitnessSemanticError`-style intermediate class with a bound theory.
- Touching any file outside the declared `file_scope`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Another test elsewhere depends on witness `.theory` being `None` or `"exclusion"` | M | L | Phase 1 runs an explicit repo-wide grep gate for `.theory` assertions and witness-error imports before any edit; Phase 3 runs the exclusion + bimodal witness suites |
| Fix is applied to `errors.py` instead of the tests, reintroducing the bimodal mislabeling bug | H | L | `errors.py` is explicitly a non-goal; Phase 3 verifies `errors.py` is unmodified via `git diff --stat` |
| Reasoning recorded as a task-number citation, violating repo rules | L | L | Phase 2 records reasoning as prose naming the two theories that share the classes; no task numbers anywhere outside `specs/**` (`.claude/rules/no-task-references-in-deliverables.md`) |
| Broader theory_lib suite has pre-existing unrelated failures, obscuring the result | L | M | Phase 1 captures a pre-edit baseline of the broader suites for before/after comparison |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Confirm RED baseline and audit dependents [COMPLETED]

**Goal**: Reproduce the exact two failures, and prove no other test in the repository depends on
witness-error `.theory` being either `None` or `"exclusion"`, before editing anything.

**Tasks**:
- [x] Run the TDD verification command and record the failure count and messages:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/unit/test_error_handling.py -v`
      Expected: 2 failed, 10 passed; both failures `AssertionError: assert None == 'exclusion'`
      in `test_witness_registry_error_basic` and `test_witness_constraint_error_basic`.
      Actual: exactly as expected — `2 failed, 10 passed in 0.57s`, both failures
      `AssertionError: assert None == 'exclusion'` in the two named tests.
- [x] Audit for other dependents — run all three greps and record their output:
      `grep -rn "\.theory" --include=*.py code/ | grep -E "assert|assertEqual"`
      `grep -rn "WitnessRegistryError\|WitnessConstraintError\|WitnessPredicateError\|WitnessNotFoundError\|WitnessError" --include=*.py code/`
      `grep -rn "WitnessSemanticError" --include=*.py code/`
      Output recorded: the `.theory`/`assertEqual` grep hits several unrelated `.theory_name` /
      `.theory` fields (builder, jupyter, settings tests) plus the seven witness-error
      `.theory` assertions in `test_error_handling.py` (lines 39, 66, 80, 86, 99, 136, 155). The
      witness-class-usage grep confirms five production raise sites (exclusion `registry.py`,
      `constraints.py`, `core.py`; bimodal `witness_registry.py`, `witness_constraints.py`), none
      passing `theory=`. The `WitnessSemanticError` grep returned no matches.
- [x] Gate: confirm the ONLY assertions on a witness error's `.theory` are in
      `theory_lib/tests/unit/test_error_handling.py`. If any other file asserts witness `.theory`
      is `None` or `"exclusion"`, STOP and report — the contract decision would need to cover it
      and it may fall outside `file_scope`.
      Gate passed: confirmed the only witness-error `.theory` assertions are the seven lines in
      `test_error_handling.py`; no other file in the repo asserts on a witness error's `.theory`.
- [x] Capture pre-edit baselines for the Phase 3 comparison (record pass/fail counts):
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/exclusion/tests/unit/test_witness_registry.py code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py -q`
      Baseline recorded: `47 passed in 0.78s`, 0 failed.

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- None (read-only baseline and audit phase)

**Verification**:
- The pytest run shows exactly 2 failures, both `assert None == 'exclusion'`.
- Grep output recorded, and the gate passes: no witness `.theory` assertion outside
  `theory_lib/tests/unit/test_error_handling.py`.
- Baseline pass/fail counts for the exclusion/bimodal witness suites recorded.

---

### Phase 2: Fix the two tests and record the contract reasoning [COMPLETED]

**Goal**: Make both tests assert the actual (and correct) contract — explicit `theory=` kwarg at
construction — and record in the file why no class-level default exists.

**Tasks**:
- [x] Edit `test_witness_registry_error_basic` (currently lines 77-81) to pass the theory
      explicitly and explain why, replacing:
      ```python
      def test_witness_registry_error_basic(self):
          """Test basic WitnessRegistryError."""
          error = WitnessRegistryError("Registry operation failed")
          assert error.theory == "exclusion"
          assert "Registry operation failed" in str(error)
      ```
      with:
      ```python
      def test_witness_registry_error_basic(self):
          """Test WitnessRegistryError constructed with an explicit theory.

          The class itself deliberately sets no theory default: it is shared by
          the exclusion and bimodal theories, both of which raise it from their
          own witness-registry modules, so a baked-in theory label would
          mislabel one of them. Callers that know their theory pass it in.
          """
          error = WitnessRegistryError("Registry operation failed", theory="exclusion")
          assert error.theory == "exclusion"
          assert "Registry operation failed" in str(error)
      ```
- [x] Apply the analogous change to `test_witness_constraint_error_basic` (currently lines 83-87):
      add `theory="exclusion"` to the `WitnessConstraintError(...)` call and a docstring recording
      the same shared-class reasoning (naming exclusion's `constraints.py` and bimodal's
      `witness_constraints.py` as the two raise sites).
- [x] Update the `TestWitnessErrorHandling` class docstring (currently
      `"""Test witness theory (exclusion) error handling."""`, line 60) so it no longer implies the
      witness errors are exclusion-specific — state that the witness error hierarchy is shared by
      the exclusion and bimodal theories and carries no default theory tag.
- [x] Confirm `code/src/model_checker/theory_lib/errors.py` remains untouched.
      Confirmed: `git diff -- code/src/model_checker/theory_lib/errors.py` is empty.
- [x] Confirm no task-number strings were introduced into the test file (per
      `.claude/rules/no-task-references-in-deliverables.md`, the reasoning must be recorded as
      durable prose naming the theories/modules, never as a task citation).
      Confirmed: `grep -niE "task [0-9]+"` matches one pre-existing line (28, unrelated to this
      diff, referencing a prior refactor) which predates this change and is outside its scope; no
      new task-number citations were introduced by this edit.

**Timing**: 0.25 hours

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/tests/unit/test_error_handling.py` - add explicit
  `theory="exclusion"` kwarg to the two error constructions; expand both test docstrings and the
  `TestWitnessErrorHandling` class docstring to record the shared-class rationale.

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/unit/test_error_handling.py -v`
  reports 12 passed, 0 failed.
- `git diff --stat` shows exactly one changed file: the test file. `errors.py` is absent from the
  diff.
- `grep -niE "task [0-9]+" code/src/model_checker/theory_lib/tests/unit/test_error_handling.py`
  returns nothing.

---

### Phase 3: Regression check and reasoning trail [COMPLETED]

**Goal**: Confirm the change is inert with respect to every other consumer of the witness error
classes, and that the recorded reasoning survives in the codebase.

**Tasks**:
- [x] Run the witness-specific suites for both theories that raise these classes and compare
      against the Phase 1 baseline:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/exclusion/tests/unit/test_witness_registry.py code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py -q`
      Result: `47 passed in 0.64s` — identical to the Phase 1 baseline (47 passed), no new
      failures.
- [x] Run the broader theory_lib unit suite to catch anything the targeted greps missed:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/unit/ -q`
      Result: `12 passed in 0.49s` (the only test module in this directory is
      `test_error_handling.py`).
- [x] Re-run the primary TDD command one final time to confirm green.
      Result: `12 passed in 0.45s`, 0 failed.
- [x] Confirm the final diff is confined to the declared `file_scope` and that `errors.py` carries
      no changes (`git diff --stat`, `git diff -- code/src/model_checker/theory_lib/errors.py`
      empty).
      Confirmed: `git diff --stat -- code/src/model_checker/theory_lib/` lists exactly one file,
      `tests/unit/test_error_handling.py` (26 insertions, 5 deletions); the `errors.py` diff is
      empty.
- [x] Note in the implementation summary the contract that was chosen and why: the witness error
      hierarchy stays theory-agnostic because exclusion and bimodal both raise it; the tests, not
      `errors.py`, encoded the stale contract. Record that threading per-raise-site theory names
      remains an available future improvement, deliberately out of scope here.
      Recorded in `specs/128_fix_witness_error_theory_attribute/summaries/01_fix-witness-theory-tests-summary.md`.

**Timing**: 0.25 hours

**Depends on**: 2

**Files to modify**:
- None (verification phase; summary artifact written by the implementer at wrap-up)

**Verification**:
- Exclusion/bimodal witness suites show no new failures versus the Phase 1 baseline.
- `theory_lib/tests/unit/` shows no new failures versus baseline.
- Primary TDD command: 12 passed, 0 failed.
- `git diff --stat` lists only `test_error_handling.py`.

## Testing & Validation

- [x] Primary TDD command green:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/unit/test_error_handling.py -v`
      (12 passed, 0 failed)
- [x] `test_witness_registry_error_basic` passes with an explicit `theory="exclusion"` construction
- [x] `test_witness_constraint_error_basic` passes with an explicit `theory="exclusion"` construction
- [x] Exclusion witness suite unchanged:
      `code/src/model_checker/theory_lib/exclusion/tests/unit/test_witness_registry.py`
- [x] Bimodal witness suites unchanged:
      `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py`,
      `.../test_witness_constraints.py`
- [x] Broader `theory_lib/tests/unit/` suite shows no new failures
- [x] `code/src/model_checker/theory_lib/errors.py` unmodified
- [x] No task-number citations anywhere in the modified test file

## Artifacts & Outputs

- `specs/128_fix_witness_error_theory_attribute/plans/01_fix-witness-theory-tests.md` (this file)
- `code/src/model_checker/theory_lib/tests/unit/test_error_handling.py` (modified: two test
  constructions plus three docstrings recording the shared-class contract)
- `specs/128_fix_witness_error_theory_attribute/summaries/01_fix-witness-theory-tests-summary.md`
  (implementation summary, recording the contract decision and its reasoning)

## Rollback/Contingency

The change touches a single test file with no production-code impact, so rollback is
`git checkout HEAD -- code/src/model_checker/theory_lib/tests/unit/test_error_handling.py` (from a
clean tree, or after `bash .claude/scripts/git-snapshot.sh` if other uncommitted work exists).

Contingency: if the Phase 1 audit gate discovers another test that requires witness `.theory` to be
`None` (i.e. asserting the no-default contract directly), that test is compatible with this fix —
it constrains `errors.py`, which is unchanged — and the plan proceeds unchanged. If instead a test
outside `file_scope` requires `.theory == "exclusion"` from a bare construction, stop and report:
that would mean the stale contract has more than two call sites and the scope decision needs the
orchestrator, since satisfying it without editing that file would require the rejected
`theory="exclusion"` class default.
