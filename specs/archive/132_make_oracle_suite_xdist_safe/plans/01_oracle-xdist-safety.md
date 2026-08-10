# Implementation Plan: Make the Oracle Suite xdist-Safe

- **Task**: 132 - make_oracle_suite_xdist_safe
- **Status**: [COMPLETED]
- **Effort**: 3.5 hours (of which ~1 hour is unattended wall-clock waiting on test runs)
- **Dependencies**: None (the sibling timeout-widening work that landed `TEMPORAL_SOLVE_TIMEOUT_MS = 180000` in `oracle/bimodal_logic/tests/test_oracle_interface.py` is already in the tree)
- **Research Inputs**: `specs/132_make_oracle_suite_xdist_safe/reports/01_oracle-xdist-safety.md`
- **Artifacts**: plans/01_oracle-xdist-safety.md (this file)
- **Standards**:
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/plan-format-enforcement.md`
  - `.claude/rules/state-management.md`
  - `.claude/rules/no-task-references-in-deliverables.md`
- **Type**: python
- **Lean Intent**: false

## Overview

The five xdist-only failures in the `oracle/` suite are not a shared-state problem — each affected
test builds its own `Z3OracleProvider()`, and the one global the code touches (`z3.z3._main_ctx`,
swapped by `isolated_z3_context()`) is a process-local module attribute that cannot cross xdist's
worker-process boundary. The real mechanism is CPU-contention-induced Z3 solve-time inflation
tripping tight `max_time`/`timeout_ms` budgets, which the oracle pipeline reports as `None` (no
countermodel) rather than as an error — the "wrong answer, not an error" hazard documented in
`code/docs/core/TESTING_GUIDE.md` section 8.6. This plan therefore does not use `xdist_group`
(worker-affinity does nothing about the *other* five workers' contention). It introduces an
`xdist_serial` mark, an `oracle/conftest.py` that registers it (plus the currently-orphaned
`differential` and `slow` marks), and a two-invocation split: `-n 6 -m "not xdist_serial"` for the
bulk, then a no-`-n` serial pass for the seven contention-sensitive tests. Done means a two-pass
run produces the same verdicts as a fully serial run, modulo the two known-failing/known-unstable
tests owned elsewhere.

### Research Integration

The plan implements the research report's Recommended Changes 1-3 verbatim in mechanism, and
records its Recommendation 5 (residual risk) in this plan's Risks table rather than acting on it.
Findings carried directly into phase design:

- **No cross-process state exists** (report section 1). Nothing in this plan tries to serialize
  access to shared state, because there is none to serialize.
- **`xdist_group` and `--dist loadfile/loadscope` are both non-fixes** (report section 2). Neither
  appears anywhere in this plan.
- **The marker warnings are an ini-discovery gap, not a missing declaration** (report section 3).
  `differential` and `slow` are already declared at `code/pyproject.toml:86-91`, but `code/` is a
  sibling — not an ancestor — of `oracle/`, so a repo-root-invoked `pytest oracle/` never reaches
  that file. A `conftest.py` is the fix; an `oracle/pytest.ini` or `oracle/pyproject.toml` is
  explicitly rejected because it would become pytest's first-found inifile for any `oracle/`-rooted
  invocation and silently change rootdir semantics.
- **Mark the whole `TestStateIsolationRegression` class, not just the two methods observed
  failing** (report section 4). All four methods share the same `setup_method` and the same
  unmodified `timeout_ms=5000` default; a watch list built from a single observation has already
  proven unreliable on a sibling triage.
- **`-n 6`, never `-n auto`** (report section 5), matching the `flake.nix:95-101` precedent for the
  in-package bimodal suite and its documented contention-flake rationale.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no ROADMAP.md was consulted.

## Goals & Non-Goals

**Goals**:

- Register `differential`, `slow`, and a new `xdist_serial` mark so `oracle/`-rooted pytest
  invocations stop emitting `PytestUnknownMarkWarning`.
- Mark exactly the seven contention-sensitive test items identified by the research report, using
  an idiom that does not disturb the shared parametrize data structures.
- Provide a durable, single-command two-pass runner so the downstream baseline work can invoke the
  correct split without rediscovering it.
- Demonstrate empirically that the two-pass run reproduces serial verdicts.

**Non-Goals**:

- Changing oracle semantics, `oracle/bimodal_logic/provider.py`, or any solver budget
  (`max_time`, `timeout_ms`, `TEMPORAL_SOLVE_TIMEOUT_MS`). Budgets are owned by the sibling
  timeout work that already landed constants in `test_oracle_interface.py`.
- Fixing `test_enriched_vs_primitive_sat_agreement[all_future]`. It exceeds even the widened
  180000ms budget in isolation (195.47s / 187.63s) — a genuine slow-solver-path finding, not an
  xdist artifact.
- Fixing `test_complexity_5_scan_self_consistent` — a genuine pre-existing self-consistency defect
  that fails at both HEAD and the pre-refactor baseline, owned by a separate task.
- Auditing all 43 active examples in `code/src/model_checker/theory_lib/bimodal/examples.py` for
  tight `max_time` margins. Recorded as a residual risk below.
- Adding `oracle/` to `flake.nix` `checks.default`, whose scoping comment
  (`flake.nix:94-100`) deliberately excludes the unpackaged `oracle/` tree.
- Touching `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py`, which
  another session holds open with uncommitted changes.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Wrapping `some_past` / `BM_CM_1` in `pytest.param(..., marks=...)` breaks the shared data structures | H | H (would happen if the obvious idiom is used) | **Verified**: `ENRICHED_PRIMITIVE_PAIRS` feeds three parametrize sites, all with `ids=[p[0] for p in ENRICHED_PRIMITIVE_PAIRS]` — `p[0]` on a `ParameterSet` yields `.values`, not the name string, so all three `ids=` comprehensions break. `regression_examples` likewise feeds `.items()` consumers at `test_boundary_regression.py:476,497,519`. Phase 1 therefore uses a `pytest_collection_modifyitems` hook keyed on node id, which touches neither structure. |
| Other examples with 5-15s `max_time` surface as new unmarked xdist artifacts in a later run | M | M | Out of scope by decision (see Non-Goals). Recorded explicitly here and in the Phase 4 report so a future run that finds a new artifact recognizes the pattern instead of re-diagnosing it. `BM_CM_1` sits at `max_time=15` and is one of several examples in the 5-15s band. |
| A ~45-minute parallel pass exceeds the 10-minute foreground Bash tool ceiling and is misread as a hang or failure | M | H if run in foreground | Phase 4 mandates `run_in_background: true` for the parallel pass, with polling. Never run the full parallel pass in a foreground Bash call. |
| Z3 solve times vary ~20x run-to-run, so a single green two-pass run is weak evidence | M | M | Phase 4's exit criterion compares *verdicts* against the known-failing/known-unstable list rather than asserting an unconditional zero-failure run, and records wall-clock so a future run has a comparison point. |
| `pytest-xdist` missing from the bare interactive python is mistaken for a broken invocation | M | M | Every command in this plan is wrapped in `nix develop --command`. The devShell already realizes pytest 9.0.3, `pytest-xdist` 3.8.0, and z3 — no rebuild needed. |
| A collection-hook id match is too broad and marks unintended items | M | L | **Verified**: `test_oracle_provider.py` excludes `BM_CM_1` from its own `regression_examples` and names its test `test_regression_standard_pipeline`, so matching on function name plus id substring is unambiguous. Phase 1 verifies the selected count is exactly 7. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential: each phase's
verification requires the prior phase's artifact.

---

### Phase 1: Create `oracle/conftest.py` with marker registration and per-case marking [COMPLETED]

**Goal**: Close the ini-discovery gap so `differential`, `slow`, and `xdist_serial` are registered
for any `oracle/`-rooted invocation, and apply `xdist_serial` to the two parametrized cases that
cannot be marked at the source without breaking shared data structures.

**Tasks**:

- [x] Create `oracle/conftest.py` (new file; no `conftest.py` exists anywhere under `oracle/` today).
- [x] Add a `pytest_configure(config)` hook calling `config.addinivalue_line("markers", ...)` three
      times, for `differential`, `slow`, and `xdist_serial`. Reuse the exact descriptions already in
      `code/pyproject.toml:86-91` for the first two so the two declarations do not drift.
- [x] Give `xdist_serial` a description that states the mechanism and points at the durable anchor:
      tests whose Z3 solve budget has under ~2x headroom, which CPU contention under `-n` can push
      past the budget — reported as no-countermodel rather than as an error (see
      `code/docs/core/TESTING_GUIDE.md` section 8.6). Reference the runner script by path.
- [x] Add a `pytest_collection_modifyitems(config, items)` hook that applies
      `pytest.mark.xdist_serial` to exactly two node-id patterns:
      `test_enriched_vs_primitive_sat_agreement[some_past]` and
      `test_regression_all_active_examples[BM_CM_1` (prefix match — the full id carries the example
      tuple). Match on both the function name and the id fragment; do not match on the id fragment
      alone.
- [x] Add a brief module docstring explaining why registration lives in a `conftest.py` rather than
      an `oracle/pytest.ini` or `oracle/pyproject.toml`: a conftest is loaded during collection
      independent of rootdir/inifile resolution, and carries no ini-precedence side effects.
- [x] **MUST NOT** cite task numbers anywhere in this file. Cite `TESTING_GUIDE.md` section 8.6 and
      file paths as the durable anchors.

**Timing**: 40 minutes

**Depends on**: none

**Files to modify**:

- `oracle/conftest.py` — new file: `pytest_configure` marker registration plus
  `pytest_collection_modifyitems` per-case marking.

**Verification**:

- No `PytestUnknownMarkWarning` on a collection that touches the `differential` mark:

  ```bash
  cd /home/benjamin/Projects/ModelChecker && \
  nix develop --command bash -c \
    'PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py \
       --collect-only -q 2>&1 | grep -c PytestUnknownMarkWarning'
  ```

  Expected output: `0`.

- The hook selects exactly the two parametrized cases (the static decorators from Phase 2 are not
  in place yet, so this count is 2, not 7):

  ```bash
  cd /home/benjamin/Projects/ModelChecker && \
  nix develop --command bash -c \
    'PYTHONPATH=code/src pytest oracle/ -m xdist_serial --collect-only -q'
  ```

  Expected: exactly 2 items, named
  `test_enriched_vs_primitive_sat_agreement[some_past]` and
  `test_regression_all_active_examples[BM_CM_1-...]`. In particular
  `test_temporal_depth_identical[some_past]` MUST NOT appear.

- Total collection is unchanged at 550 items:

  ```bash
  cd /home/benjamin/Projects/ModelChecker && \
  nix develop --command bash -c 'PYTHONPATH=code/src pytest oracle/ --collect-only -q | tail -3'
  ```

---

### Phase 2: Apply static `xdist_serial` decorators in `test_soundness_regression.py` [COMPLETED]

**Goal**: Mark the five non-parametrized contention-sensitive tests at their source, covering both
the two methods previously observed failing and their two same-risk siblings.

**Tasks**:

- [x] Apply `@pytest.mark.xdist_serial` at class level to `class TestStateIsolationRegression`
      (`oracle/bimodal_logic/tests/test_soundness_regression.py:641`), covering all four methods:
      `test_100_calls_mixed_temporal_depths`, `test_sat_unsat_interleaving_stability`,
      `test_temporal_propositional_interleaving`, `test_no_semantics_reference_leak_with_temporal`.
      The latter two did not fail in the observed run but share the identical `setup_method` and
      the identical unmodified `timeout_ms=5000` default.
- [x] Apply `@pytest.mark.xdist_serial` at method level to
      `TestOracleMFormulaBoundarySafe.test_oracle_m_formula_depth1_boundary_safe` only.
- [x] Leave `test_oracle_m_formula_depth0_boundary_safe` unmarked (trivial depth-0 atom, ample
      margin) and `test_oracle_m_formula_depth2_returns_none` unmarked (it *asserts* `result is
      None`; a spurious contention timeout also yields `None`, so its verdict cannot invert).
- [x] Do not mark the whole `TestOracleMFormulaBoundarySafe` class.
- [x] Add a short comment above each decorator naming the mechanism and pointing at
      `code/docs/core/TESTING_GUIDE.md` section 8.6 — no task numbers.

**Timing**: 25 minutes

**Depends on**: 1

**Files to modify**:

- `oracle/bimodal_logic/tests/test_soundness_regression.py` — two decorator additions (one
  class-level at line ~641, one method-level at line ~1023) plus explanatory comments. Confirm
  `pytest` is already imported at module top before adding decorators.

**Verification**:

- The full marked set is now exactly 7 items:

  ```bash
  cd /home/benjamin/Projects/ModelChecker && \
  nix develop --command bash -c \
    'PYTHONPATH=code/src pytest oracle/ -m xdist_serial --collect-only -q'
  ```

  Expected: 7 items — the 4 `TestStateIsolationRegression` methods,
  `test_oracle_m_formula_depth1_boundary_safe`,
  `test_enriched_vs_primitive_sat_agreement[some_past]`, and
  `test_regression_all_active_examples[BM_CM_1-...]`.

- The complement is exactly 543:

  ```bash
  cd /home/benjamin/Projects/ModelChecker && \
  nix develop --command bash -c \
    'PYTHONPATH=code/src pytest oracle/ -m "not xdist_serial" --collect-only -q | tail -3'
  ```

  Expected: 543 items (550 total - 7 marked). If the two numbers do not sum to 550, the marking is
  wrong — stop and fix before proceeding.

---

### Phase 3: Add the two-pass runner script and document it [COMPLETED]

**Goal**: Capture the two-invocation strategy durably so the downstream baseline work invokes it as
one command rather than rediscovering the split.

**Recommendation (single option, not a survey)**: an executable shell script
`oracle/run-oracle-suite.sh`, co-located with the standalone tree it drives, plus a short pointer
section in `oracle/bimodal_logic/README.md`. Rejected alternatives, for the record: a `flake.nix`
app or check would contradict `flake.nix:94-100`, whose comment deliberately scopes
`checks.default` to the in-package bimodal suite and excludes the unpackaged `oracle/` tree;
`code/scripts/` sits inside the packaged wheel tree while `oracle/` is excluded from the wheel, so
a runner there would straddle the packaging boundary.

**Tasks**:

- [x] Create `oracle/run-oracle-suite.sh`, executable (`chmod +x`), with `set -uo pipefail` (not
      `-e`: pass 1 failing must not prevent pass 2 from running).
- [x] Assume the script runs *inside* the devShell; do not have it invoke `nix develop` itself.
      Guard at the top: if `python -c 'import xdist'` fails, print a message directing the caller to
      re-run under `nix develop --command bash oracle/run-oracle-suite.sh` and exit non-zero.
- [x] Default `PYTHONPATH` to `code/src` if unset, resolving it against the repository root derived
      from the script's own location so the script works from any cwd.
- [x] Pass 1: `pytest oracle/ -n 6 -m "not xdist_serial" "$@"`. Hard-code `-n 6`; do not use
      `-n auto`. Add a comment explaining the contention ceiling and pointing at the `flake.nix`
      precedent by path and section, not by task number.
- [x] Pass 2: `pytest oracle/ -m "xdist_serial" "$@"` with no `-n` at all.
- [x] Capture both exit codes, print a two-line summary naming each pass and its status, and exit
      non-zero if either pass failed.
- [x] Add a "Running the test suite" section to `oracle/bimodal_logic/README.md`: the one-command
      invocation, why the split exists (one sentence on the contention mechanism, citing
      `code/docs/core/TESTING_GUIDE.md` section 8.6), and the note that adding a new test whose Z3
      budget has under ~2x headroom over its typical solo wall-clock should carry
      `@pytest.mark.xdist_serial`.
- [x] **MUST NOT** cite task numbers in either the script or the README.

**Timing**: 35 minutes

**Depends on**: 1, 2

**Files to modify**:

- `oracle/run-oracle-suite.sh` — new executable script implementing the two-pass split.
- `oracle/bimodal_logic/README.md` — new "Running the test suite" section.

**Verification**:

- The script is executable and its guard works. Run a fast smoke test that exercises both passes
  against a narrow subset (keeps this phase's verification under the foreground timeout):

  ```bash
  cd /home/benjamin/Projects/ModelChecker && \
  nix develop --command bash -c \
    'bash oracle/run-oracle-suite.sh --collect-only -q 2>&1 | tail -20'
  ```

  Expected: pass 1 reports 543 collected, pass 2 reports 7 collected, and the summary reports both
  passes green with exit code 0.

- Confirm the executable bit: `test -x oracle/run-oracle-suite.sh`.

- Confirm no task-number citations landed outside `specs/`:

  ```bash
  cd /home/benjamin/Projects/ModelChecker && \
  grep -nE '\b[Tt]asks? [0-9]+' oracle/conftest.py oracle/run-oracle-suite.sh \
    oracle/bimodal_logic/README.md
  ```

  Expected: no matches in newly added lines. Pre-existing task references elsewhere in
  `README.md` are not in scope to remove.

---

### Phase 4: Validate the two-pass split against known verdicts [COMPLETED]

**Measured results**:

- Serial pass (`pytest oracle/ -m "xdist_serial" -q`): `7 passed, 543 deselected in 374.27s
  (0:06:14)`, exit 0.
- Parallel pass (`pytest oracle/ -n 6 -m "not xdist_serial" -q`): `1 failed, 533 passed, 9 xfailed
  in 2779.96s (0:46:19)`, exit 1. Sole failure:
  `test_cross_oracle_differential.py::TestFullScanReport::test_complexity_5_scan_self_consistent`
  — the known pre-existing self-consistency defect, out of scope.
- Coverage: 1 + 533 + 9 = 543 (parallel) + 7 (serial) = 550. Full accounting, no tests lost
  between the two passes.
- Failure count went from 7 (the original full-`-n 6` baseline) to 1 (this run) — the two-pass
  split cleared all five previously-observed xdist artifacts plus the two `TestStateIsolationRegression`
  siblings added as same-risk (never independently observed failing).
- **Correction to the plan's Non-Goals assumption**: `test_enriched_vs_primitive_sat_agreement[all_future]`
  passed in this parallel-pass run (confirmed: it is not in the 7-item `xdist_serial` set, and it
  does not appear in the parallel pass's failure list), running under full six-way contention. The
  prior "genuinely exceeds even the widened 180000ms budget" claim rested on two isolated samples
  (195.47s / 187.63s). With this passing counter-sample under strictly worse (contended)
  conditions, and given the ~20x Z3 solve-time variance documented in
  `code/docs/core/TESTING_GUIDE.md` section 8.6, the honest characterization is
  **marginal/flaky, straddling the 180s budget** rather than a confirmed slow-solver defect.
  Recorded here and in the summary; not acted on (still out of scope — would need repeat sampling
  to resolve, which is separately owned).

**Goal**: Demonstrate empirically that the two-pass run produces the same verdicts as a serial run,
modulo the tests owned by other tasks, and record wall-clock for future comparison.

**Tasks**:

- [x] Run the serial pass first (it is short, ~5-6 minutes: the four state-isolation tests plus
      `depth1` (~1.6s), `some_past` (~67s), and `BM_CM_1` (~12s)). Expect 7 passed. **Measured**:
      `7 passed, 543 deselected in 374.27s (0:06:14)`, exit 0.
- [x] Run the parallel pass **in the background** — at ~44 minutes it far exceeds the 10-minute
      foreground Bash ceiling, and a cut-off command must not be misread as a failure. Use
      `run_in_background: true` and poll, or redirect to a log file under the task's `run/`
      directory and poll that. **Measured**: `1 failed, 533 passed, 9 xfailed in 2779.96s
      (0:46:19)`, exit 1.
- [x] Compare the parallel pass's failure list against the known set. A run is **clean** if the
      only failures are drawn from:
      - `test_cross_oracle_differential.py::TestFullScanReport::test_complexity_5_scan_self_consistent`
        — genuine pre-existing self-consistency defect, fails at HEAD and at the pre-refactor
        baseline. Owned elsewhere; out of scope. **This is the sole observed failure.**
      - `test_enriched_vs_primitive_sat_agreement[all_future]` — **correction**: this case
        actually passed in the measured parallel-pass run, running under full six-way contention
        (confirmed not in the 7-item `xdist_serial` set and absent from the failure list). The
        prior "exceeds even the widened 180000ms budget" claim rested on two isolated samples
        (195.47s / 187.63s); a passing counter-sample under strictly worse conditions, combined
        with the ~20x Z3 solve-time variance documented in `code/docs/core/TESTING_GUIDE.md`
        section 8.6, means the honest characterization is marginal/flaky straddling the 180s
        budget, not a confirmed slow-solver defect. Not acted on further (still out of scope).
- [x] **Any other failure in the parallel pass is a real result for this task**: it means a
      contention-sensitive test was missed. Re-run that test alone serially. If it passes alone, add
      it to the `xdist_serial` set (Phase 2 idiom for a plain method, Phase 1 idiom for a
      parametrize case) and re-verify the 7-item count arithmetic from Phase 2. **No other
      failures occurred** — this branch was not needed.
- [x] Record in the implementation summary: both passes' wall-clock, the pass/fail counts, and the
      exact failure list with the known-set classification applied.

**Timing**: 90 minutes (≈50-60 minutes unattended wall-clock plus analysis)

**Depends on**: 3

**Files to modify**:

- None. This phase is validation only. Any marker additions it discovers are applied to the Phase 1
  and Phase 2 files under their existing idioms.

**Verification**:

- Serial pass (foreground, generous timeout — budget at least 600000ms given ~20x Z3 run-to-run
  variance):

  ```bash
  cd /home/benjamin/Projects/ModelChecker && \
  nix develop --command bash -c \
    'PYTHONPATH=code/src pytest oracle/ -m "xdist_serial" -q'
  ```

  Expected: `7 passed`.

- Parallel pass (**background only**):

  ```bash
  cd /home/benjamin/Projects/ModelChecker && \
  mkdir -p specs/132_make_oracle_suite_xdist_safe/run && \
  nix develop --command bash -c \
    'PYTHONPATH=code/src pytest oracle/ -n 6 -m "not xdist_serial" -q' \
    > specs/132_make_oracle_suite_xdist_safe/run/parallel-pass.log 2>&1
  ```

  Expected: 543 collected; the failure list is a subset of the two known entries above. Any other
  failure triggers the re-run-alone-then-mark loop.

- End-to-end, via the script (background):

  ```bash
  cd /home/benjamin/Projects/ModelChecker && \
  nix develop --command bash oracle/run-oracle-suite.sh \
    > specs/132_make_oracle_suite_xdist_safe/run/two-pass.log 2>&1
  ```

  Expected: pass 2 green; pass 1's only failures drawn from the known set. The script's overall exit
  code will be non-zero as long as the two known-failing/unstable tests remain in the tree — this is
  expected and is not a defect in this task's work.

---

## Testing & Validation

- [x] `pytest oracle/ --collect-only` emits zero `PytestUnknownMarkWarning` (Phase 1).
- [x] `-m xdist_serial` selects exactly 7 items and `-m "not xdist_serial"` selects exactly 543;
      the two sum to the full 550 (Phase 2).
- [x] `test_temporal_depth_identical[some_past]` is NOT marked — the hook must not spill onto the
      other two parametrize sites that share `ENRICHED_PRIMITIVE_PAIRS` (Phase 1).
- [x] `regression_examples.items()` consumers at `test_boundary_regression.py:476,497,519` and the
      three `ids=[p[0] for p in ENRICHED_PRIMITIVE_PAIRS]` comprehensions are untouched and still
      collect cleanly (Phase 1 — this is what the collection-hook idiom buys).
- [x] `oracle/run-oracle-suite.sh` is executable, guards against a non-devShell invocation, and
      runs both passes even when the first fails (Phase 3).
- [x] Serial pass: `7 passed` (Phase 4). Measured `7 passed, 543 deselected in 374.27s (0:06:14)`.
- [x] Parallel pass: failure list is a subset of `{test_complexity_5_scan_self_consistent,
      test_enriched_vs_primitive_sat_agreement[all_future]}` (Phase 4). Measured: sole failure was
      `test_complexity_5_scan_self_consistent`; `all_future` passed (see Phase 4 correction note).
- [x] No task-number citations in `oracle/conftest.py`, `oracle/run-oracle-suite.sh`, or the new
      `oracle/bimodal_logic/README.md` section.

## Artifacts & Outputs

- `oracle/conftest.py` — new: marker registration plus per-parametrize-case `xdist_serial` marking.
- `oracle/bimodal_logic/tests/test_soundness_regression.py` — modified: one class-level and one
  method-level `@pytest.mark.xdist_serial` decorator.
- `oracle/run-oracle-suite.sh` — new executable: the two-pass invocation.
- `oracle/bimodal_logic/README.md` — modified: "Running the test suite" section.
- `specs/132_make_oracle_suite_xdist_safe/run/parallel-pass.log`,
  `specs/132_make_oracle_suite_xdist_safe/run/two-pass.log` — validation logs.
- `specs/132_make_oracle_suite_xdist_safe/summaries/01_oracle-xdist-safety-summary.md` — the
  implementation summary, which must record both passes' wall-clock and the classified failure
  list, and must restate the residual risk (other examples in the 5-15s `max_time` band could
  surface as new unmarked artifacts in a future run).

## Rollback/Contingency

All changes are additive and confined to four files, three of which are new. To revert: delete
`oracle/conftest.py` and `oracle/run-oracle-suite.sh`, and remove the two decorators from
`test_soundness_regression.py` and the README section. No production code, no solver budgets, and
no oracle semantics are touched, so a rollback cannot change any test's verdict — it only restores
the single-invocation `-n 6` behavior and the `PytestUnknownMarkWarning` noise.

Partial-completion contingency: Phases 1-2 are independently valuable (the marks exist and are
correctly scoped even without the runner), and Phase 3's script is independently valuable without
Phase 4's validation. If Phase 4 finds a contention-sensitive test the research did not identify,
that is an in-scope result — add the mark and re-verify the count arithmetic; it does not invalidate
Phases 1-3.
