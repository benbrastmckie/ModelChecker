# Implementation Plan: Eliminate Wall-Clock-Sensitive Test Flakes

- **Task**: 169 - Eliminate wall-clock-sensitive test flakes and undiagnosable hangs
- **Status**: [COMPLETED]
- **Effort**: 10.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/169_eliminate_wall_clock_sensitive_test_flakes/reports/01_wall-clock-flake-root-causes.md`
- **Artifacts**: plans/01_eliminate-wall-clock-test-flakes.md (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/context/standards/status-markers.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/no-task-references-in-deliverables.md`
  - `code/docs/core/TESTING_GUIDE.md`
- **Type**: python
- **Lean Intent**: false

## Overview

Three defect families make the general CI suite non-deterministic in both `tests.yml`'s Python
3.10-3.12 matrix and `flake.nix`'s `checks.default`, which run textually identical pytest
invocations under two toolchains. This plan fixes each at its root: a Z3 UNKNOWN result is made
distinguishable from a genuine UNSAT everywhere `BuildExample` reports results (plus a
deterministic `rlimit` budget alongside the load-dependent `max_time`); the unbounded max/min
ratio assertion in `TestPerformanceAndScalabilityScenarios` is replaced with cold-start-discarding
absolute budgets; and both CI invocations gain `--timeout` with `--timeout-method=thread` so a
hang names its test and dumps stacks instead of dying to an opaque job-level cancellation. A
marker taxonomy plus a serial second CI pass removes every remaining wall-clock-asserting test
from the contended `-n 6` worker pool, and three executable regression guards plus TESTING_GUIDE
documentation prevent silent regression of all three classes.

**Definition of done**: no test in the gating `-n 6` pass asserts a wall-clock bound; both CI
files carry identical `--timeout`/`--timeout-method`/`-n`/marker-expression values enforced by a
test; `BuildExample.get_result()` always carries a `timeout` key; the full suite is green in both
toolchains.

### Research Integration

The research report is fully integrated. Key findings driving this plan:

- `models/structure.py`'s `solve()`/`re_solve()` already classify **every** Z3 UNKNOWN as
  `is_timeout=True` and `_process_solver_results()` already populates `self.timeout`. The break
  is entirely in `builder/example.py`, which never reads it — so this is a plumbing fix, not a
  solver fix.
- No `rlimit` mechanism exists anywhere in the production path; every `rlimit` hit in the repo is
  a comment recording an ad hoc measurement. This is genuinely new capability.
- `BuildProject.generate()` is pure filesystem work — the 17.4-vs-5.0 ratio failure is a
  structural assertion-design bug (cold first iteration retained, no floor on `min_time`), and it
  gets *worse* as the code gets faster.
- `pytest-timeout>=2.0.0` is already declared in `code/pyproject.toml` and installed in both
  toolchains; neither CI invocation ever passes `--timeout`.
- `oracle/conftest.py`'s `xdist_serial` marker plus `oracle/run-oracle-suite.sh`'s two-pass
  parallel/serial pattern is the established in-repo isolation precedent.
- `code/tests/packaging/test_parity.py` is the style precedent for making a comment-only
  cross-file invariant executable.

### Resolution of the Report's Five Open Design Decisions

These are settled here; the implementer must not re-litigate them.

**D1 — rlimit plumbing depth: full `ExampleSettings` + solver-abstraction integration.**
The task requires deterministic budgets "alongside `max_time`", and `max_time` already flows
settings-dict -> `ModelDefaults.solve()` -> `solver.set_timeout()`. A test-local helper would not
satisfy "at their root rather than per-test" and would leave every theory's application path
untouched. Blast radius is controlled by making the field **optional with a `None` default that
skips the `set()` call entirely**, so no existing example changes behavior.

**D2 — timeout-key shape: additive boolean `"timeout"` key, plus a three-value `check_result()`.**
`get_result()` and `_get_model_structure_data()` gain a `"timeout": bool` key alongside the
existing `"model_found"` (minimal, additive, only one non-test production consumer). Separately,
`check_result()` moves from a boolean to a three-value string enum
`"match"` / `"mismatch"` / `"inconclusive"`, because a boolean structurally cannot express
"we ran out of time". Grounding fact: `BuildExample.check_result()`'s existing signature is
**already annotated `-> str`** while its body returns a bool — this change fixes that
long-standing annotation/behavior mismatch rather than introducing a new inconsistency.

**D2a — timeout reporting from `check_result()`: a third enum value, not a raise or a sentinel.**
A raise would convert an inconclusive run into a hard error in the six Jupyter call sites; `None`
is falsy and would silently collapse back into the mismatch branch, reproducing the exact defect.

**D2b — `utils/testing.py` is fixed in the same pass, not deferred.** It is the same conflation
(`model_found = model_structure_obj.z3_model is not None`, no timeout field) on a second surface
used by theory-level example suites; deferring it leaves a live path by which the flake still
surfaces.

**D3 — isolation mechanism: adopt `xdist_serial` in `code/pyproject.toml` following the oracle
precedent, and assign every wall-clock-asserting test exactly one of two markers.**
Folding all six files under `@pytest.mark.performance` alone is rejected: `performance` is
deselected outright by both CI invocations, so it would silently delete gating coverage of the
very tests being fixed (including the redesigned scalability class). The taxonomy is:

| Marker | Meaning | CI treatment |
|---|---|---|
| `performance` | Budget too tight for any shared CI runner (sub-10ms class) | Deselected from both passes, as today |
| `xdist_serial` | Real wall-clock assertion with adequate headroom that should keep gating | Deselected from the `-n 6` pass; run in a new serial second pass with no `-n` flag |

This closes the marker gap the task names — after this change **no** wall-clock-asserting test is
left unmarked in the `-n 6` pool — while preserving coverage.

**D4 — `--timeout` budget: 300 seconds, with `--timeout-method=thread`, identical in both files.**
Rationale: it matches the figure `differential-tests.yml` already uses for its comparably-scoped
invocation, sits far below the `general-tests` job's `timeout-minutes: 20` backstop (so the
per-test timeout fires first and produces the diagnostic), and leaves large headroom over the
slowest observed single test. This number carries a Scope Hypothesis in Phase 6 requiring
empirical confirmation before the value is committed.

**D5 — regression-guard scope: three targeted guards across two new modules plus one extension**,
following `test_parity.py`'s one-module-per-invariant-family style rather than one omnibus module:
1. `code/tests/ci/test_workflow_parity.py` — `tests.yml` and `flake.nix` agree on marker
   expression, worker count, and timeout flags (both passes).
2. `code/tests/ci/test_timing_marker_coverage.py` — AST scan proving no test function that both
   reads a clock and asserts on the elapsed value is left unmarked.
3. An extension to `code/src/model_checker/builder/tests/unit/test_example.py` — `get_result()`
   always carries a `timeout` key, and a forced-UNKNOWN structure yields
   `timeout=True` with `model_found=False`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` supplied and no ROADMAP.md consultation was requested for this dispatch.

## Goals & Non-Goals

**Goals**:
- A Z3 UNKNOWN is never reported as `model_found=False` without an accompanying, readable
  `timeout` signal, on both the `BuildExample` and `utils/testing.py` surfaces.
- Deterministic, machine-load-independent Z3 `rlimit` budgets available alongside `max_time`
  through the existing settings plumbing, opt-in and default-off.
- `TestPerformanceAndScalabilityScenarios`'s timing assertions no longer degrade as the code gets
  faster.
- Both CI pytest invocations produce a named test plus a stack dump on a hang.
- Zero wall-clock-asserting tests remaining in the `-n 6` contended pool.
- `tests.yml` and `flake.nix` kept in sync by an executable test, not by a comment.
- TESTING_GUIDE.md documents the fixed state, the marker taxonomy, and the timeout convention.

**Non-Goals**:
- Tuning any individual test's `max_time` value to make it pass (the per-test remedy this task
  explicitly rejects).
- Changing `models/structure.py`'s UNKNOWN classification — it is already correct.
- Changing the `-n 6` worker count, the `packaging`/`unstable` deselections, or either job's
  `timeout-minutes` backstop.
- Re-scoping which tests either CI job runs, beyond the marker-driven parallel/serial split.
- Adding `rlimit` values to any existing example or theory default (the field ships default-off).
- Touching `oracle/` — it already implements the reference pattern correctly.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `check_result()` enum change breaks the six Jupyter call sites that treat it as a boolean | H | H | Phase 2 migrates all call sites in the same commit; `"inconclusive"` is a non-empty truthy string, so a missed site fails loudly in tests rather than silently inverting. Enumerate sites by grep before editing, not from this plan's list |
| Chosen `--timeout=300` is below some real test's runtime under `-n 6`, turning a flake into a hard CI failure | H | M | Phase 6 Scope Hypothesis requires an empirical `--durations=0` measurement in both toolchains before committing the value; raise the number if measured max exceeds 100s |
| New serial CI pass pushes `general-tests` past its `timeout-minutes: 20` | M | L | Only a handful of tests carry `xdist_serial`; measure the serial pass wall time in Phase 6 and record it. Do not raise `timeout-minutes` to compensate without evidence |
| `rlimit` plumbing changes solve behavior for existing examples | H | L | Field is optional, defaults to `None`, and the `set("rlimit", ...)` call is skipped entirely when unset; verified by a test asserting no `rlimit` is set by default |
| AST-based marker-coverage guard produces false positives on mocked-clock tests | M | M | Restrict the scan to real-clock calls (`time.time`, `time.perf_counter`, `time.monotonic`) and exclude modules that patch them; carry an explicit, commented allowlist for known-safe exceptions |
| `flake.nix` edit breaks the Nix derivation in a way local `pytest` cannot catch | M | M | Run `nix flake check` locally in Phase 6 before considering the phase green |
| Marking a currently-gating test `performance` silently removes CI coverage | M | M | D3's taxonomy forbids it except for the sub-10ms class; the Phase 7 marker guard asserts the taxonomy, and Phase 5 records a before/after selected-test count |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3, 4 | -- |
| 2 | 2, 5 | 1, 4 |
| 3 | 6 | 5 |
| 4 | 7, 8 | 2, 3, 5, 6 |

Phases within the same wave can execute in parallel. Wave 2's Phase 2 is blocked by Phase 1 only;
Phase 5 is blocked by Phase 4 only (both edit `test_project_edge_cases.py`).

---

### Phase 1: Surface `timeout` in Result Dictionaries [COMPLETED]

**Goal**: Make an inconclusive Z3 UNKNOWN readable as such by every consumer of a result dict,
without changing any existing key's meaning.

**Tasks**:
- [x] Write failing tests first (RED): a test asserting `BuildExample.get_result()` contains a
      `"timeout"` key; a test asserting that a `ModelStructure` with `timeout=True` and
      `z3_model_status=False` yields `{"model_found": False, "timeout": True}`; the same pair for
      `_get_model_structure_data()`.
- [x] Add `"timeout": self.model_structure.timeout` to `get_result()`'s returned dict and update
      its docstring's documented structure block.
- [x] Add the same key to `_get_model_structure_data()`.
- [x] Add a `timeout` field (default `False`) to `TestResultData.__init__` in
      `utils/testing.py` and populate it in `run_enhanced_test()` from
      `model_structure_obj.timeout`, immediately alongside the existing
      `result_data.model_found = ...` assignment.
- [x] Make `TestResultData.is_valid_countermodel()` return `False` on a timeout without implying
      a semantic negative, and document that distinction in its docstring.
- [x] Fix `get_result()`'s stale return annotation (`Tuple[bool, Optional[Any], str]`) to
      `Dict[str, Any]`, which is what it has always actually returned.
- [x] Run the builder unit suite to GREEN.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts exactly two production files change
(`code/src/model_checker/builder/example.py`, `code/src/model_checker/utils/testing.py`) and that
`BuildExample.get_result()` has exactly one non-test production caller (`print_model()`).
Confirm at implementation time with `grep -rn "\.get_result()" code/ --include=*.py` and
`grep -rn "TestResultData\|run_enhanced_test" code/ --include=*.py` before editing; if additional
production consumers appear, extend this phase rather than silently proceeding.

**Files to modify**:
- `code/src/model_checker/builder/example.py` — add `timeout` key to `get_result()` and
  `_get_model_structure_data()`; fix return annotation
- `code/src/model_checker/utils/testing.py` — add `timeout` to `TestResultData`, populate in
  `run_enhanced_test()`, adjust `is_valid_countermodel()` docstring
- `code/src/model_checker/builder/tests/unit/test_example.py` — new RED-first tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/unit/ -v` green
- `PYTHONPATH=code/src pytest code/src/model_checker/utils -v` green
- New tests fail before the production edit and pass after (record both in the phase notes)

---

### Phase 2: Three-Way `check_result()` and Call-Site Migration [COMPLETED]

**Goal**: Replace the boolean match/mismatch verdict with an explicit three-value result so a
timeout is never reported as a semantic mismatch.

**Tasks**:
- [x] Write failing tests first (RED) covering all three returns of both `check_result()` methods.
- [x] Change `BuildExample.check_result()` to return `"match"`, `"mismatch"`, or `"inconclusive"`,
      returning `"inconclusive"` whenever `self.model_structure.timeout` is truthy, checked
      **before** the expectation comparison (mirroring `run_differential_scan()`'s
      timeout-checked-first ordering in
      `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`).
- [x] Apply the identical three-way change to `ModelDefaults.check_result()` in
      `code/src/model_checker/models/structure.py`.
- [x] Migrate every call site: `jupyter/display.py`, `jupyter/interactive.py`,
      `utils/testing.py` (both the module-level helper and `run_enhanced_test()`), and
      `models/tests/unit/test_structure.py::test_check_result`.
- [x] At each Jupyter call site, render `"inconclusive"` as a distinct user-visible state
      ("solver budget exhausted -- result unknown"), never as invalid.
- [x] Store the enum on `TestResultData.check_result` and update its default from `False` to
      `"inconclusive"`.
- [x] Update the `test_iteration_via_iterate_api` assertion in
      `builder/tests/unit/test_example.py` to branch on `timeout` first and skip (not fail) on an
      inconclusive solve, with a comment naming the 30.62s-vs-`max_time=30` observation as the
      motivating case.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts eight non-test call sites (six in `jupyter/`, two in
`utils/testing.py`) plus one test module. Confirm with
`grep -rn "check_result" code/ --include=*.py` and reconcile against the iterate-package hits,
which are a **different, unrelated local variable also named `check_result`** in
`iterate/iterator.py` and `iterate/core.py` and must not be edited. Report the confirmed count in
the phase notes.

**Files to modify**:
- `code/src/model_checker/builder/example.py` — three-way `check_result()`
- `code/src/model_checker/models/structure.py` — three-way `check_result()`
- `code/src/model_checker/jupyter/display.py` — two call sites
- `code/src/model_checker/jupyter/interactive.py` — four call sites
- `code/src/model_checker/utils/testing.py` — two call sites plus `TestResultData` default
- `code/src/model_checker/models/tests/unit/test_structure.py` — update `test_check_result`
- `code/src/model_checker/builder/tests/unit/test_example.py` — timeout-first branch

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/builder code/src/model_checker/models code/src/model_checker/jupyter -v` green
- `grep -rn "check_result" code/ --include=*.py` shows no remaining site treating the value as a
  bare boolean

---

### Phase 3: Deterministic Z3 `rlimit` Budgets [COMPLETED]

**Goal**: Add a machine-load-independent resource budget alongside the wall-clock `max_time`,
through the plumbing `max_time` already uses, default-off.

**Tasks**:
- [x] Write failing tests first (RED): a test that `Z3SolverAdapter.set_rlimit(n)` sets the
      solver parameter; a test that a settings dict without the new field results in **no**
      `rlimit` being set; a test that a settings dict with the field set produces a solver whose
      `rlimit` parameter matches.
- [x] Add `set_rlimit(self, units: int) -> None` to `Z3SolverAdapter`, implemented as
      `self._solver.set("rlimit", units)`, directly alongside the existing `set_timeout()`.
- [x] Declare `set_rlimit` on `SolverProtocol`/`TrackedSolverProtocol` in
      `code/src/model_checker/solver/protocols.py`, matching how `set_timeout` is declared.
- [x] Add `max_rlimit: int` (optional; `total=False` already applies) to `ExampleSettings` in
      `code/src/model_checker/settings/types.py`, documented as "deterministic Z3 resource-unit
      budget; independent of machine load, unlike `max_time`".
- [x] Wire it in `ModelDefaults.solve()` and `ModelDefaults.re_solve()`: call `set_rlimit` only
      when the setting is present and truthy, immediately after the existing `set_timeout` call.
- [x] Confirm the existing UNKNOWN-as-timeout branch already covers an rlimit-exhausted UNKNOWN
      (it treats *any* UNKNOWN as `is_timeout=True` regardless of `reason_unknown()`); add a test
      pinning that behavior so a future narrowing of the branch cannot silently regress it.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that no `rlimit` mechanism exists in the production path
today and that every current `rlimit` occurrence under `code/` and `oracle/` is a comment.
Confirm with `grep -rn rlimit code/ oracle/` before adding the capability; if a live call site
exists, integrate with it rather than adding a parallel path.

**Files to modify**:
- `code/src/model_checker/solver/z3_adapter.py` — `set_rlimit()`
- `code/src/model_checker/solver/protocols.py` — protocol declaration
- `code/src/model_checker/settings/types.py` — `max_rlimit` in `ExampleSettings`
- `code/src/model_checker/models/structure.py` — conditional wiring in `solve()` and `re_solve()`
- `code/src/model_checker/solver/tests/` — new adapter/protocol tests
- `code/src/model_checker/models/tests/unit/test_structure.py` — default-off and UNKNOWN-pinning
  tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/solver code/src/model_checker/models code/src/model_checker/settings -v` green
- Full suite green: `PYTHONPATH=code/src pytest code/tests code/src/model_checker -m "not packaging" -n 6 -q`
- A test proves the default path sets no `rlimit`

---

### Phase 4: Redesign the Repeated-Operation Timing Assertions [COMPLETED]

**Goal**: Make `TestPerformanceAndScalabilityScenarios`'s assertions stable and
monotonically-improving-friendly instead of degrading as the code gets faster.

**Tasks**:
- [x] Write the redesigned assertion first and confirm it fails on a synthetic cold-start-heavy
      sample and passes on a realistic one (RED then GREEN, using injected sample times).
- [x] In `test_repeated_project_operations_maintain_consistent_performance`, run one explicit
      discarded warm-up iteration before the measured loop, so no cold-cache/cold-import
      measurement enters any statistic.
- [x] Delete the `max_time / min_time` ratio assertion entirely — it has no floor on `min_time`
      and is the assertion whose bound tightens as the implementation improves.
- [x] Replace it with two bounds: every warm iteration under a fixed absolute ceiling, and
      `max(warm_times) < median(warm_times) + FIXED_SLACK_SECONDS`, with `FIXED_SLACK_SECONDS`
      defined as a named module constant carrying a comment explaining why a fixed slack, not a
      ratio, is used.
- [x] Add a comment at the assertion recording the observed failure (ratio 17.4 against a 5.0
      bound while the companion `max < 10.0s` absolute bound passed comfortably) as the
      motivating evidence — cite the file and class, never a task number.
- [x] Review `test_multiple_project_generation_completes_within_reasonable_time` in the same
      class: it already uses an absolute-only bound and needs no assertion redesign, only the
      marker applied in Phase 5. Record that as a deliberate no-op rather than skipping it
      silently.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts the ratio assertion is the only unbounded
ratio-over-time assertion in the repository. Confirm with a repo-wide grep for `max(` / `min(`
combined with a time-derived list before closing the phase; extend the phase if others exist.

**Files to modify**:
- `code/src/model_checker/builder/tests/e2e/test_project_edge_cases.py` — warm-up discard,
  ratio removal, absolute + median-plus-slack bounds, motivating comment

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/e2e/test_project_edge_cases.py -v` green
- Run the class 10 consecutive times under concurrent load (`-n 6` on the rest of the suite) with
  zero failures
- `grep -n "time_variation_ratio" code/` returns nothing

---

### Phase 5: Marker Taxonomy and Full Inventory Marking [COMPLETED]

**Goal**: Ensure no wall-clock-asserting test is left unmarked in the contended `-n 6` pool, per
D3's two-marker taxonomy.

**Tasks**:
- [x] Register `xdist_serial` in `code/pyproject.toml`'s `[tool.pytest.ini_options].markers`,
      reusing `oracle/conftest.py`'s wording so the two declarations stay recognizably the same
      concept.
- [x] Record a before-state: the selected-test count of
      `pytest tests/ src/model_checker -m "not packaging and not performance and not unstable" -n 6 --collect-only -q | tail -1`.
      Result: 2295 selected (via `git stash` of the marking edits to get a pristine collect).
- [x] Apply `@pytest.mark.xdist_serial` to the wall-clock-asserting tests in:
      `builder/tests/e2e/test_project_edge_cases.py` (the whole
      `TestPerformanceAndScalabilityScenarios` class), `builder/tests/integration/test_performance.py`,
      `builder/tests/unit/test_project_version.py`, `builder/tests/unit/test_serialize.py`, and
      `builder/tests/unit/test_progress_bar_ordering.py`.
- [x] Leave `builder/tests/test_refactoring_target_behavior.py::test_performance_improvement`
      on `@pytest.mark.performance` — its 0.01s budget is the sub-10ms class D3 assigns to that
      marker. Do not add `xdist_serial` to it. Confirmed unchanged by diff.
- [x] Add a one-line comment at each newly marked location stating why the test is
      contention-sensitive, so the marker is self-documenting at the site.
- [x] Record the after-state selected-test count and the delta; the delta must equal the number of
      newly `xdist_serial`-marked tests, no more.
      Result: `-m "xdist_serial"` collects exactly 7 tests (2 in
      `TestPerformanceAndScalabilityScenarios`, 2 in `test_performance.py`, 1 each in
      `test_progress_bar_ordering.py`, `test_project_version.py`, `test_serialize.py`); the
      gating selection with `and not xdist_serial` added collects 2288 = 2295 - 7. Delta matches
      exactly.

**Timing**: 1 hour

**Depends on**: 4

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts exactly six files assert wall-clock bounds (five to newly
mark, one already marked). Before marking, re-derive the inventory from source rather than
trusting this list: grep for `assertLess`/`assertGreater`/`assert` against variables named
`*time*`/`*elapsed*`/`*duration*` across `code/src/model_checker/**/tests/**` and `code/tests/**`,
excluding modules that patch the clock (e.g. `models/tests/unit/test_structure.py`'s mocked
cases). Report the confirmed file list and any additions in the phase notes.

**Files to modify**:
- `code/pyproject.toml` — `xdist_serial` marker registration
- `code/src/model_checker/builder/tests/e2e/test_project_edge_cases.py`
- `code/src/model_checker/builder/tests/integration/test_performance.py`
- `code/src/model_checker/builder/tests/unit/test_project_version.py`
- `code/src/model_checker/builder/tests/unit/test_serialize.py`
- `code/src/model_checker/builder/tests/unit/test_progress_bar_ordering.py`

**Verification**:
- `pytest ... -m "xdist_serial" --collect-only -q` lists exactly the intended tests
- `pytest ... -m "not packaging and not performance and not unstable and not xdist_serial" --collect-only -q`
  count equals the recorded before-count minus the newly marked count
- No unknown-marker warnings in pytest output

---

### Phase 6: CI Wiring — Timeout Flags and the Serial Second Pass [COMPLETED]

**Goal**: Give both CI jobs a diagnostic per-test hang guard and remove `xdist_serial` tests from
the parallel pass, with the two files kept byte-for-byte consistent on every shared value.

**Tasks**:
- [x] **Measure before choosing the number**: run the gating selection locally under `-n 6` in
      both toolchains (`pytest` directly, and `nix flake check`) and read the `--durations=0`
      output already enabled by `addopts` to find the slowest single test. Record the figure.
      Result: PyPI toolchain slowest single test was 82.34s
      (`bimodal/tests/integration/test_iterate.py::TestBimodalIteratorReal::test_iterate_two_produces_distinct_models`),
      full parallel-pass run: 2287 passed, 1 skipped in 186.93s.
- [x] Confirm or revise the D4 budget of `--timeout=300` against that measurement: keep 300 if the
      measured max is under 100s (>=3x headroom); otherwise choose 3x the measured max, rounded
      up, and record the revised figure and its justification.
      Kept 300: 82.34s is under the 100s threshold (>=3.6x headroom).
- [x] Edit `.github/workflows/tests.yml`'s `general-tests` "Run general test suite" step: append
      `--timeout=<budget> --timeout-method=thread` to the existing invocation and add
      `and not xdist_serial` to the marker expression.
- [x] Add a second serial pass to the same step: the same paths with
      `-m "xdist_serial and not packaging and not unstable"`, **no `-n` flag at all**, and the
      same `--timeout`/`--timeout-method` values — following
      `oracle/run-oracle-suite.sh`'s two-pass structure.
- [x] Apply the identical two changes to `flake.nix`'s `checks.default` `checkPhase`.
- [x] Add a comment above each invocation explaining `--timeout-method=thread` specifically: the
      default `signal` method cannot interrupt or diagnose a hang blocked inside a C extension
      call such as a stuck Z3 solve, whereas `thread` runs a watcher that dumps every thread's
      stack via `faulthandler` regardless. Reference the observed incident by its CI run id and
      symptom (94% progress, 17 minutes of zero output, killed by `timeout-minutes: 20` with only
      orphaned workers in the cleanup log), and by the prior in-repo
      `--timeout=N --timeout-method=thread` precedent — cite durable anchors, never a task number.
      Cited CI run 32897405646 and
      `specs/archive/129_triage_preexisting_test_failure_backlog/plans/01_verify-fixes-baseline-doc.md`
      (lines 134, 143, 359) in both files.
- [x] Measure the serial pass's wall time and confirm the combined two-pass runtime leaves
      headroom under `general-tests`' `timeout-minutes: 20`. Do not raise `timeout-minutes`.
      Serial pass: 1.91s (PyPI), 1.56s (nix). Combined two-pass runtime ~181s (PyPI) / ~161s
      (nix, `checkPhase completed in 2 minutes 40 seconds`), both far under the 1200s
      (`timeout-minutes: 20`) backstop.
- [x] Verify the Nix derivation still evaluates and the check passes: `nix flake check`.
      `nix flake check -L`: "all checks passed!", exit 0.

**Timing**: 1.5 hours

**Depends on**: 5

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts the `--timeout=300` budget and that `pytest-timeout` is
already installed in both toolchains without a dependency change. Confirm the budget by the
measurement sub-step above (this is the confirmation, and the phase may not close without the
recorded figure), and confirm the dependency with `grep -n pytest-timeout code/pyproject.toml
.github/workflows/tests.yml flake.nix` — all three already carry it, so no install-step edit is
expected. Report any deviation.

**Commit-mode note**: `atomic-batch` is declared because `tests.yml` and `flake.nix` must change
together — a commit with only one edited is a real, shippable divergence of exactly the kind the
Phase 7 parity guard exists to forbid.

**Files to modify**:
- `.github/workflows/tests.yml` — marker expression, timeout flags, serial second pass, comments
- `flake.nix` — the identical changes in `checks.default`'s `checkPhase`

**Verification**:
- Both files' parallel-pass marker expressions are textually identical
- Both files' `--timeout` value, `--timeout-method`, and `-n 6` are identical
- `nix flake check` passes locally
- A deliberately hung scratch test (never committed) is confirmed to produce a named test and a
  stack dump rather than a silent stall

---

### Phase 7: Executable Regression Guards [COMPLETED]

**Goal**: Convert all three invariants from prose into tests, so none of the three defect classes
can silently return.

**Tasks**:
- [x] Create `code/tests/ci/` with an `__init__`-free pytest layout matching `code/tests/packaging/`.
      Deviation: `code/tests/packaging/` itself (and every other `code/tests/**`/
      `code/src/model_checker/**/tests/**` subdirectory, confirmed by inventory) DOES carry an
      `__init__.py`, contradicting the plan's literal premise. Followed the actual, confirmed
      repo-wide convention instead and added `code/tests/ci/__init__.py` with a short module
      docstring, matching `packaging/__init__.py`'s style.
- [x] Write `code/tests/ci/test_workflow_parity.py`, modeled on `code/tests/packaging/test_parity.py`:
      parse `.github/workflows/tests.yml` with `yaml.safe_load` and extract `flake.nix`'s
      `checkPhase` pytest lines by targeted regex; assert both files agree on the parallel-pass
      marker expression, the serial-pass marker expression, the `-n` worker count, the
      `--timeout` value, and `--timeout-method`. Each assertion carries a message naming the two
      source locations so a failure is self-explanatory.
      Deviation: used targeted regex for BOTH files, not `yaml.safe_load` for `tests.yml`.
      Confirmed `PyYAML` is not an installed dependency in either CI toolchain (neither
      `tests.yml`'s "Install test dependencies" step's package list nor `flake.nix`'s
      `devPython` list requires it) -- adding one is out of this phase's declared scope, and
      `flake.nix` must be regex-parsed regardless since it is not YAML, so both files are handled
      the same way for consistency.
- [x] Add an assertion to the same module that every marker named in either invocation's `-m`
      expression is registered in `code/pyproject.toml`'s `markers` list, so a typo in a marker
      name cannot silently deselect nothing.
- [x] Write `code/tests/ci/test_timing_marker_coverage.py`: walk `code/src/model_checker/**/tests/**`
      and `code/tests/**` with `ast`, find functions that both call a real clock
      (`time.time`, `time.perf_counter`, `time.monotonic`) and assert a comparison on the derived
      elapsed value, and assert each carries `performance` or `xdist_serial`. Carry an explicit,
      commented allowlist for mocked-clock modules.
      Finding: the AST scan surfaced two genuinely unmarked cases Phase 5's scope hypothesis
      missed -- `code/tests/integration/test_timeout_resources.py::test_z3_solver_timeout` and
      `::test_cli_command_timeout` (both real `time.time()` reads with `assert elapsed < N`
      hang-guard bounds, in `code/tests/**` which Phase 5's own handoff had claimed contributed
      no candidates). Marked both `@pytest.mark.xdist_serial` with a contention-sensitivity
      comment, in this phase rather than reopening the closed Phase 5, since finding exactly this
      kind of gap is this guard's purpose. xdist_serial inventory is now 9 (was 7); gating
      selection recount: 2291 selected (2413 total collected, up from 2408 -- the +5 is this
      phase's own 5 new `test_workflow_parity.py` tests, unmarked and therefore themselves part
      of the gating pool, which is correct: they do not read a wall clock).
- [x] Extend `code/src/model_checker/builder/tests/unit/test_example.py` with the timeout-key
      guard: `get_result()` always contains `"timeout"`, and a forced-UNKNOWN model structure
      yields `timeout=True` with `model_found=False` — asserting the two are independently
      readable, mirroring the three-way partition assertion style in
      `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`.
      Finding: Phase 1 already added exactly this guard (`TestTimeoutSurfacing` class:
      `test_get_result_contains_timeout_key` and `test_get_result_timeout_true_on_unknown`, using
      a mock model_structure to simulate a forced UNKNOWN). No further extension was needed; this
      task's verification requirement (task 6 below) was satisfied against the existing tests.
- [x] Confirm each guard actually fails when its invariant is broken: temporarily revert one
      value in each of the three cases, observe the failure, restore. Record all three
      observations.
      (1) `test_workflow_parity.py`: changed both `tests.yml` `--timeout=300` occurrences to
      `999` -> `test_timeout_value_and_method_match` failed with `assert 2 == 1` naming both
      source lines and values; restored, 5 passed.
      (2) `test_timing_marker_coverage.py`: removed `@pytest.mark.performance` from
      `test_refactoring_target_behavior.py::test_performance_improvement` ->
      `test_all_wall_clock_timing_assertions_are_marked` failed naming exactly that
      function/line; restored, 2 passed, `git diff --stat` on the file confirmed zero net change.
      (3) `TestTimeoutSurfacing`: renamed `get_result()`'s `"timeout"` key to
      `"timeout_DISABLED_FOR_GUARD_CHECK"` -> `test_get_result_contains_timeout_key` and
      `test_get_result_timeout_true_on_unknown` both failed (`KeyError: 'timeout'`); restored,
      full `test_example.py` suite green (17 passed), `git diff --stat` confirmed zero net change.
- [x] Confirm the new `code/tests/ci/` module is selected by both CI invocations' path arguments
      (`tests/` in `tests.yml`, `tests` in `flake.nix`) and carries no marker that deselects it.
      Confirmed via `--collect-only` under the gating marker expression: `<Package ci>` with its
      five `test_workflow_parity.py` tests plus the two `test_timing_marker_coverage.py` tests
      all appear in the selected tree; neither module carries `packaging`/`performance`/
      `unstable`/`xdist_serial`.

**Timing**: 1.5 hours

**Depends on**: 1, 5, 6

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts three guards across two new modules plus one extension,
and that no existing test parses `tests.yml` or `flake.nix`. Confirm the latter with
`grep -rn "tests.yml\|flake.nix" code/tests code/scripts code/src` before writing, and integrate
with any existing guard rather than duplicating it.

**Files to modify**:
- `code/tests/ci/test_workflow_parity.py` (new)
- `code/tests/ci/test_timing_marker_coverage.py` (new)
- `code/src/model_checker/builder/tests/unit/test_example.py` — timeout-key guard

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ci -v` green
- Each guard demonstrated failing on a deliberately broken invariant, then restored
- Guards are collected by both CI selections (verify with `--collect-only`)

---

### Phase 8: TESTING_GUIDE Documentation [COMPLETED]

**Goal**: Document the fixed state, the marker taxonomy, and the timeout convention so the
guide stops modeling the anti-pattern this task removes.

**Tasks**:
- [x] Add a new subsection under section 8.5 ("Repeated-Operation Timing: Discard Cold Starts,
      Avoid Unbounded Ratios") with a worked before/after example: the unbounded `max/min` ratio
      as the anti-pattern, and the warm-up-discard plus absolute/median-plus-slack form as the
      correct pattern, with an explicit note that a ratio bound tightens as the implementation
      gets faster.
      Added as `#### Repeated-Operation Timing: ...` nested under `### 8.5`, not a new top-level
      `###` section, so 8.6-8.10's existing numbers were not disturbed.
- [x] Update section 8.6 ("Solver Timing Budgets and Machine Variance") to describe the **fixed**
      state: it currently reads as if `max_time`-tuning is the only remedy. Document the new
      `timeout` key in `BuildExample` results, the three-value `check_result()` return, and the
      new `max_rlimit` setting as the deterministic complement to `max_time`.
- [x] Add a new subsection documenting the `--timeout` / `--timeout-method=thread` CI convention,
      opening with the observed hang incident as its motivating case (matching how 8.6 opens with
      a concrete measured incident), and stating why `thread` rather than the default `signal`.
      Added as new `### 8.11`, appended after 8.10 (before `## Quick Reference`) rather than
      inserted mid-sequence, so no existing section number changed.
- [x] Add a marker subsection for `xdist_serial` modeled structurally on section 8.9's `unstable`
      treatment: meaning, entry criteria, and a per-workflow inventory of where the deselection
      and the serial pass are wired.
      Added as new `### 8.12`. "Entry criteria" for `xdist_serial` is the two-marker taxonomy
      table (D3, distinguishing it from `performance`) rather than 8.9's four-item severity
      checklist, since `xdist_serial` is a routine structural classification, not a quarantine
      for an investigated residual defect -- stated explicitly in the subsection's opening
      paragraph.
- [x] Cross-reference the three regression guards by path so a future reader knows the invariants
      are executable, not aspirational.
      `code/tests/ci/test_workflow_parity.py` and `code/tests/ci/test_timing_marker_coverage.py`
      cited in 8.11/8.12; `TestTimeoutSurfacing`/`TestThreeWayCheckResult` in
      `builder/tests/unit/test_example.py` cited in 8.6.
- [x] Verify every file path, section number, and cross-reference in the new prose resolves.
      All 17 distinct backtick-quoted file paths in the new prose confirmed to exist via `test -e`;
      all `8.N` cross-references (8.5-8.12) confirmed to match real headings via
      `grep -n "^### 8\."`.
- [x] Confirm no task numbers appear anywhere in the added prose — cite filenames, class names,
      section headings, and the CI run id instead
      (`.claude/rules/no-task-references-in-deliverables.md`).
      `grep -inE "task [0-9]|tasks [0-9]+-[0-9]|\(task [0-9]"` over the new prose: no matches.

**Timing**: 1 hour

**Depends on**: 2, 3, 5, 6

**Verification Tier**: prose

**Commit Mode**: per-substep

**Files to modify**:
- `code/docs/core/TESTING_GUIDE.md` — new 8.5 subsection, revised 8.6, new timeout-convention
  subsection, new `xdist_serial` marker subsection

**Verification**:
- Diff read-through confirms every changed hunk is prose within `TESTING_GUIDE.md`
- Every referenced path exists (`while read -r p; do test -e "$p" || echo "MISSING $p"; done`)
- `bash .claude/scripts/check-task-references.sh` (or the equivalent lint) reports no task-number
  references in the changed file

---

## Testing & Validation

- [x] Full gating selection green in the PyPI toolchain:
      `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 6 --timeout=<budget> --timeout-method=thread -q`
      Result: 2292 passed, 1 skipped, 0 failed in 168.93s.
- [x] Serial pass green: same paths with `-m "xdist_serial and not packaging and not unstable"`,
      no `-n` flag
      Result: 9 passed, 0 failed in 3.19s.
- [x] Full check green in the Nix toolchain: `nix flake check`
      Result: "all checks passed!" (parallel: 2033 passed, 256 skipped, 0 failed in 152.81s;
      serial: 9 passed, 1 skipped, 0 failed in 1.84s). Required one bugfix (see Phase 8 handoff):
      `code/tests/ci/test_workflow_parity.py` unconditionally read `.github/workflows/tests.yml`
      and `flake.nix` from the repo root, but `flake.nix`'s `checks.default` derivation sets
      `src = ./code`, so that sandboxed build never contains either file (both live outside
      `code/`). Added a clean `pytest.skip(..., allow_module_level=True)` when either file is
      absent, with a comment explaining why and noting the guard still runs for real in
      `tests.yml`'s `general-tests` job, where `actions/checkout@v4` provides the full repo.
      Verified by simulating the sandbox's layout locally (a `code/`-only copy with no repo-root
      siblings): the module now skips cleanly instead of erroring.
- [x] `code/tests/ci/` guards green and each demonstrated to fail on a broken invariant
      (see Phase 7 handoff for the three fail-then-restore observations)
- [x] `test_iteration_via_iterate_api` reports an inconclusive solve as inconclusive, not as
      "no model found" — verified by forcing a short `max_time`
      (Phase 2; covered by the full-suite passes above and `TestThreeWayCheckResult`)
- [x] `TestPerformanceAndScalabilityScenarios` passes 10 consecutive runs under concurrent `-n 6`
      load
      Ran 10 consecutive standalone invocations, all green (2 passed each time). The
      "concurrent `-n 6` load" framing predates this class's Phase 5 `xdist_serial` marking; by
      design that marker now guarantees this class never runs alongside the `-n 6` pool in
      gating CI (it runs alone in the serial pass instead), so standalone repetition is the
      condition that actually matters post-fix, and it is what was verified.
- [x] Default `rlimit` behavior unchanged: a test proves no `rlimit` is set when `max_rlimit` is
      absent
      (`test_solve_without_max_rlimit_sets_no_rlimit`, `test_re_solve_without_max_rlimit_sets_no_rlimit`;
      both pass)
- [x] No unregistered-marker warnings anywhere in pytest output
      Confirmed via `--collect-only -W error::pytest.PytestUnknownMarkWarning`: 2415 collected,
      no warning raised.
- [x] `pytest --collect-only` before/after counts reconcile exactly with the marking delta
      Final reconciliation (post-Phase 7's 2-test correction): 2415 total collected; 9
      `xdist_serial`; 2293 in the gating selection
      (`not packaging and not performance and not unstable and not xdist_serial`); 2415 - 9 = 2406,
      and 2406 - 2293 = 113 deselected by `packaging`/`performance`/`unstable`, unchanged from the
      original pre-task baseline (113) since this task added no new `packaging`/`performance`/
      `unstable` markings.

## Artifacts & Outputs

- `code/src/model_checker/builder/example.py` — `timeout` key, three-way `check_result()`,
  corrected return annotation
- `code/src/model_checker/models/structure.py` — three-way `check_result()`, `rlimit` wiring in
  `solve()`/`re_solve()`
- `code/src/model_checker/utils/testing.py` — `timeout` on `TestResultData`, migrated call sites
- `code/src/model_checker/solver/z3_adapter.py`, `protocols.py` — `set_rlimit` capability
- `code/src/model_checker/settings/types.py` — `max_rlimit` in `ExampleSettings`
- `code/src/model_checker/jupyter/display.py`, `interactive.py` — migrated call sites
- `code/src/model_checker/builder/tests/e2e/test_project_edge_cases.py` — redesigned timing
  assertions
- Five test modules newly carrying `@pytest.mark.xdist_serial`
- `code/pyproject.toml` — `xdist_serial` marker registration
- `.github/workflows/tests.yml`, `flake.nix` — timeout flags, marker expression, serial pass
- `code/tests/ci/test_workflow_parity.py`, `code/tests/ci/test_timing_marker_coverage.py` (new)
- `code/docs/core/TESTING_GUIDE.md` — four documentation changes
- `specs/169_eliminate_wall_clock_sensitive_test_flakes/summaries/01_*-summary.md`

## Rollback/Contingency

Every phase commits independently and the waves are ordered so that later phases depend on
earlier ones but not the reverse, so a single-phase `git revert` is safe for Phases 1, 3, 4, 7,
and 8 in isolation.

- **Phase 2 (three-way `check_result()`)** has the widest call-site blast radius. If migration
  proves larger than the Scope Hypothesis confirms, revert Phase 2 alone and ship Phases 1 + 3-8:
  Phase 1's additive `timeout` key already lets consumers distinguish the two cases, and the
  remaining phases do not depend on the enum. Re-file Phase 2 as its own task.
- **Phase 6 (CI wiring)** is the only phase whose failure mode is a red CI on `master`. If either
  pass fails after merge for reasons unrelated to a real defect, revert the two-file commit as a
  unit — it is an `atomic-batch` phase precisely so that revert is clean — leaving the marker
  work from Phase 5 in place and harmless (marked tests simply keep running in the parallel pass
  as they do today).
- **Phase 3 (`rlimit`)** is default-off; if it destabilizes any theory, revert the wiring in
  `solve()`/`re_solve()` while keeping the adapter capability, which is inert on its own.
- If `--timeout` turns out to be set too low and hard-fails real tests, raise the value in both
  files in a single follow-up commit — never remove the flag, and never raise `timeout-minutes`
  instead.
