# Implementation Plan: Fix contention-flaky soundness regression tests

- **Task**: 172 - fix_contention_flaky_soundness_regression_tests
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/172_fix_contention_flaky_soundness_regression_tests/reports/01_contention-flaky-tests.md
- **Artifacts**: plans/01_mark-flaky-tests-xdist-serial.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Three tests in `oracle/bimodal_logic/tests/test_soundness_regression.py` fail under the gating
suite's parallel pass (`-n 6`) and pass serially: they call `find_countermodel(F_P)` on the
provider's unmodified `timeout_ms=5000` default with only ~3.3x measured headroom, which six-way
CPU contention erodes past budget. The remedy is scheduling, not budget: route these tests to the
serial pass with `@pytest.mark.xdist_serial`, exactly as the already-fixed sibling
`test_oracle_m_formula_depth1_boundary_safe` in the same file does. A fourth test in the same file
(`TestBoundaryVacuity::test_depth1_boundary_safe_is_true`) has a byte-for-byte identical risk
profile and is included. Done when a full `oracle/run-oracle-suite.sh` two-pass run shows pass 1
with zero failures and pass 2 green inside its 1800s budget.

### Research Integration

The research report's five findings are adopted in full:

- **Finding 1** — this is the exact class `code/docs/core/TESTING_GUIDE.md` sections 8.6/8.12
  describe, with an in-file precedent at `test_soundness_regression.py:1092` using the same formula
  (`F_P`), same budget (`timeout_ms=5000`), and same measured headroom. Use the precedent's
  per-method decorator + inline-comment style, not `TestStateIsolationRegression`'s class-level
  style (the enclosing classes hold fast depth-0 methods that must not be over-serialized).
- **Finding 2** — do not pass `max_rlimit`; TESTING_GUIDE 8.13 already rejected it for this exact
  flake shape. Recorded as an explicit decision in Phase 4.
- **Finding 3** — pass 2 grows by ~6s (four tests at ~1.5s each) against an 1800s budget. No
  separate budget investigation needed beyond the required full run.
- **Finding 4** — `test_depth1_boundary_safe_is_true` is included. **Decision: include it.** It is
  in `file_scope`, shares the class, formula, and default budget of a confirmed failure, and its
  absence from the measured failure list is consistent with probabilistic scheduling noise rather
  than evidence of safety. Leaving it unmarked invites a second round of this same report.
- **Finding 5** — do not add an AST floor guard to `code/tests/ci/test_example_budget_floor.py`.
  Recorded as an explicit decision in Phase 4. `test_oracle_provider.py::test_future_sat_returns_dict`
  carries the same risk but sits outside `file_scope`; it is recorded as a follow-up candidate, not
  pulled in.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; ROADMAP.md was not consulted.

## Goals & Non-Goals

**Goals**:
- Route the three reported flaky tests, plus the one in-scope sibling with an identical risk
  profile, to the serial pass via `@pytest.mark.xdist_serial` with inline rationale comments
  matching the in-file precedent.
- Verify green via the real two-pass driver `bash oracle/run-oracle-suite.sh`, not a narrowed
  selection.
- Record the two negative decisions (no `max_rlimit`, no new floor guard) with their reasons.

**Non-Goals**:
- Changing `oracle/bimodal_logic/provider.py` in any way — no `timeout_ms` default change, no
  `max_rlimit` at these call sites, no signature change.
- Adding or changing any test in `code/tests/ci/test_example_budget_floor.py`.
- Weakening, relaxing, or deleting any assertion in the four target tests.
- Editing `GATING_RECHECK_SOLVE_TIMEOUT_MS` (stays 40000) or `MIN_CONCLUSIVE_GATING_FORMULAS`
  (stays 100).
- Widening `ORACLE_PASS1_TIMEOUT` / `ORACLE_PASS2_TIMEOUT` or any per-formula solve budget.
- Fixing `test_oracle_provider.py::test_future_sat_returns_dict` (outside `file_scope`).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The full two-pass run surfaces a *different* pass-1 failure (flakiness is probabilistic) | M | M | Do not widen scope. Record any new failure with its file and error; if outside `file_scope`, note it as a follow-up candidate rather than fixing it in this task |
| Pass 2 exceeds its 1800s budget after gaining four tests | H | L | Four tests add ~6s to a measured 677-959s band. Read the reported pass-2 wall clock from the run output and compare to 1800s; if it were exceeded, the cause would be unrelated to this change and must not be met by widening the budget |
| The long run is reaped by the harness before completion | M | H | Launch detached with `setsid nohup ... &`, redirect to a log file, then poll the log rather than blocking on the command |
| Over-serializing by using a class-level marker | M | L | Use per-method decorators only; both enclosing classes contain fast depth-0 or exception-path methods that belong in pass 1 |
| Marking a test that is not actually at risk | L | L | Phase 1's inventory confirms each candidate calls `find_countermodel` on a `temporal_depth>=1` formula with no `timeout_ms` override and does not assert `pytest.raises(OracleTimeoutError)` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Confirm the at-risk call-site inventory [COMPLETED]

**Inventory result**: Enumerated all 25 `find_countermodel(` call sites in the file. Exactly
four are unmarked, bare-default (no `timeout_ms`), `temporal_depth>=1` formula calls with no
`pytest.raises(OracleTimeoutError)` guard — matching the plan's four-test hypothesis exactly:
`TestBoundaryVacuity::test_depth1_boundary_safe_is_true` (L401),
`TestBoundaryVacuity::test_depth1_countermodel_has_required_fields` (L450),
`TestGuardedCompositionality::test_forward_comp_with_temporal_formula_output` (L632),
`TestGuardedCompositionality::test_nullity_with_temporal_formula_output` (L651). Every remaining
call site falls into: depth-0 formula (`ATOM_A`/`TAUTOLOGY`), a class already carrying
`@pytest.mark.xdist_serial` (`TestStateIsolationRegression` L664, the L1092 precedent),
`pytest.raises(OracleTimeoutError)` (`TestKnownBoundaryUnsafe`'s `GG_P`/`GF_P`/`FF_P`/compound
tests, `test_gg_p_returns_none`), or a fourth bucket not literally named in the plan text but
consistent with the research report: three `FG_P`-based tests (L443, L871, L1149) resolve via
fast structural boundary-vacuity UNSAT (the negation is unsatisfiable by construction at the
domain boundary, decided without an expensive search), matching why none of the three appear in
the measured failure list despite ordinary CI load. No discrepancy with the four-test hypothesis.

**Goal**: Confirm, before editing, that exactly four tests in
`oracle/bimodal_logic/tests/test_soundness_regression.py` are unmarked, bare-default,
`temporal_depth>=1` call sites — no more and no fewer.

**Tasks**:
- [ ] Enumerate every `find_countermodel(` call in the file and, for each, record: the formula
      argument, whether a `timeout_ms` keyword is passed, whether the test or its class carries
      `@pytest.mark.xdist_serial`, and whether the test body wraps the call in
      `pytest.raises(OracleTimeoutError)`.
- [ ] Confirm the four target tests are unmarked bare-default `F_P` calls:
      `TestBoundaryVacuity::test_depth1_boundary_safe_is_true` (~line 396),
      `TestBoundaryVacuity::test_depth1_countermodel_has_required_fields` (~line 448),
      `TestGuardedCompositionality::test_forward_comp_with_temporal_formula_output` (~line 626),
      `TestGuardedCompositionality::test_nullity_with_temporal_formula_output` (~line 645).
- [ ] Confirm every remaining bare-default call site falls into one of the three exempt buckets the
      research identified: depth-0 formula (`ATOM_A`, `TAUTOLOGY`), already covered by an existing
      `xdist_serial` marker (`TestStateIsolationRegression` at ~line 664,
      `test_oracle_m_formula_depth1_boundary_safe` at ~line 1092), or asserting
      `pytest.raises(OracleTimeoutError)` (`TestKnownBoundaryUnsafe`, `test_gg_p_returns_none`).
- [ ] If the inventory disagrees with the four-test hypothesis, stop and record the discrepancy
      before editing; do not silently widen or narrow the edit set.

**Timing**: 0.25 hours

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: Exactly four tests in this file need the marker. Confirm at implementation
time by enumerating all `find_countermodel(` call sites in the file and classifying each against
the three exempt buckets above; any call site that is unmarked, passes no `timeout_ms`, uses a
`temporal_depth>=1` formula, and does not expect `OracleTimeoutError` belongs in the edit set.

**Files to modify**:
- None (read-only inventory phase).

**Verification**:
- The inventory enumerates every `find_countermodel(` call site in the file with no unclassified
  remainder, and the resulting edit set is either exactly the four named tests or an explicitly
  recorded deviation with its reason.

---

### Phase 2: Apply xdist_serial markers to the four tests [COMPLETED]

**Verification results**: `--collect-only -q -m xdist_serial` selects 9 tests (5 pre-existing +
4 newly marked), no depth-0 or raises-timeout test present. `--collect-only -q` collects 30
tests total, unchanged from before the edit. `git diff` on the target file shows only four
added decorator+comment blocks (5 lines each) — no assertion, call, or docstring line touched.

**Goal**: Add `@pytest.mark.xdist_serial` plus an inline rationale comment to each of the four
tests confirmed in Phase 1, matching the in-file precedent's style exactly.

**Tasks**:
- [ ] Read the precedent at `test_soundness_regression.py:1092-1097` and reuse its shape: decorator
      first, then a comment block between the decorator and the `def` line citing the measured
      headroom, the `timeout_ms=5000` default, `code/docs/core/TESTING_GUIDE.md` section 8.6, and
      the serial second pass of `oracle/run-oracle-suite.sh`.
- [ ] Add the decorator + comment to `TestBoundaryVacuity::test_depth1_boundary_safe_is_true`.
- [ ] Add the decorator + comment to `TestBoundaryVacuity::test_depth1_countermodel_has_required_fields`.
- [ ] Add the decorator + comment to `TestGuardedCompositionality::test_forward_comp_with_temporal_formula_output`.
- [ ] Add the decorator + comment to `TestGuardedCompositionality::test_nullity_with_temporal_formula_output`.
- [ ] Use per-method decorators only. Do not add a class-level marker to either class.
- [ ] Change nothing else: no assertion edits, no `timeout_ms` or `max_rlimit` keyword added, no
      docstring semantics altered.
- [ ] Cite durable anchors in the comments (TESTING_GUIDE section numbers, the precedent's test
      name). Do not reference task numbers in the source file, per
      `.claude/rules/no-task-references-in-deliverables.md`.

**Timing**: 0.5 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `oracle/bimodal_logic/tests/test_soundness_regression.py` - add four `@pytest.mark.xdist_serial`
  decorators with inline rationale comments.

**Verification**:
- `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_soundness_regression.py --collect-only -q -m xdist_serial`
  lists the four newly marked tests alongside the previously marked ones, and no depth-0 or
  raises-timeout test appears in that selection.
- `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_soundness_regression.py --collect-only -q`
  collects the same total test count as before the edit (markers reschedule, they never deselect
  at collection).
- `git diff oracle/bimodal_logic/tests/test_soundness_regression.py` shows only added decorator and
  comment lines — no modified assertion, call, or docstring line.
- `git status --short` shows `oracle/bimodal_logic/tests/test_soundness_regression.py` as the only
  modified file outside `specs/`.

---

### Phase 3: Full two-pass verification via the real driver [NOT STARTED]

**Goal**: Confirm pass 1 drops from three failures to zero and pass 2 stays green inside its 1800s
budget, using the unmodified two-pass driver rather than a narrowed selection.

**Tasks**:
- [ ] Launch the full run detached so the harness cannot reap it:
      `setsid nohup nix develop --command bash oracle/run-oracle-suite.sh > /tmp/claude-1000/-home-benjamin-Projects-ModelChecker/15065234-5397-4b68-927a-0fb793f145d2/scratchpad/oracle-suite-post.log 2>&1 &`
      (drop the `nix develop --command` prefix if already inside the project devShell — the script
      does not enter it itself and exits early if `pytest-xdist` is not importable).
- [ ] Poll the log file rather than blocking; budget ~25 minutes total (pass 1 ~13 min at `-n 6`,
      pass 2 ~11 min serial).
- [ ] Record from the log: pass 1 pass/fail/skip/xfail counts and wall clock; pass 2 test count and
      wall clock; both passes' exit codes as reported by the script's own summary.
- [ ] Confirm pass 1 reports zero failures, and specifically that none of the four target tests
      appears in pass 1's selection.
- [ ] Confirm pass 2 test count grew by exactly four and its wall clock is comfortably inside the
      1800s budget.
- [ ] If any new failure appears, capture its full node id and traceback. If it lies outside
      `file_scope`, record it as a follow-up candidate and do not fix it here.
- [ ] Do not re-run with a narrowed `-k` or single-file selection to obtain a green result;
      narrowed gates are what hid this defect originally.

**Timing**: 0.75 hours (mostly wall-clock wait)

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: Pass 2 grows from 15 to 19 tests and from ~677s to roughly 683s (four tests
at ~1.5s each). Confirm at implementation time by reading the observed pass-2 test count and wall
clock directly from the run log; treat any materially larger growth as a signal to re-check the
Phase 1 inventory rather than as an accepted result.

**Files to modify**:
- None (verification phase; the run log is written to the scratchpad, not the repository).

**Verification**:
- Pass 1: zero failures, and none of the four target tests present in its selection.
- Pass 2: green, test count increased by exactly four, wall clock inside 1800s.
- The script's own end-of-run summary reports success for both passes.

---

### Phase 4: Record decisions and close out [NOT STARTED]

**Goal**: Record the two negative decisions with their reasons and the one out-of-scope follow-up
candidate, and confirm the two untouched `file_scope` files are genuinely untouched.

**Tasks**:
- [ ] Record in the implementation summary: **`max_rlimit` was evaluated and deliberately not used
      at these call sites.** Reason — `code/docs/core/TESTING_GUIDE.md` section 8.13 already worked
      through this exact tradeoff for the `CL_TH_12`/`CL_TH_13` flake: an rlimit bound can only ever
      cause an inconclusive result, never prevent one. Once a test is in the serial pass it is no
      longer competing with five sibling workers, so there is no residual wall-clock risk left for
      `max_rlimit` to address; adding it would supply a second independent way to fail with no
      correctness benefit. 8.13 warrants `max_rlimit` only where a wall-clock budget cannot be
      widened far enough to be safe, which is not this case.
- [ ] Record in the implementation summary: **no AST floor guard was added to
      `code/tests/ci/test_example_budget_floor.py`.** Reason — that guard works because its risk is
      a per-call-site `'max_time': N` dict literal, raisable independently per site. Here the risk
      is a *shared function default* (`Z3OracleProvider.find_countermodel`'s `timeout_ms=5000`),
      whose value cannot be raised without changing behavior for the many callers that already pass
      deliberate explicit budgets. The actual risk factor is (unmarked bare call) x (formula with
      `temporal_depth>=1`), and `temporal_depth` is not statically readable from the call site
      without resolving a module-level formula argument — so an AST scan cannot distinguish a
      genuinely at-risk site from a `TestKnownBoundaryUnsafe`-style call that expects a timeout.
      `test_example_budget_floor.py` needs no code change.
- [ ] Record in the implementation summary the out-of-scope follow-up candidate:
      `oracle/bimodal_logic/tests/test_oracle_provider.py::test_future_sat_returns_dict` calls
      `find_countermodel(FUTURE_SAT_JSON)` (`some_future(atom A)`, `temporal_depth=1`) at the bare
      default and is unmarked — same risk class, outside this task's `file_scope`. Suggest a
      narrowly scoped follow-up via `/spawn` rather than widening this task.
- [ ] Record the measured before/after figures from Phase 3 in the summary.
- [ ] Confirm `git diff --stat` shows no change to `oracle/bimodal_logic/provider.py` or
      `code/tests/ci/test_example_budget_floor.py`.

**Timing**: 0.5 hours

**Depends on**: 3

**Verification Tier**: prose

**Commit Mode**: per-substep

**Files to modify**:
- `specs/172_fix_contention_flaky_soundness_regression_tests/summaries/01_mark-flaky-tests-xdist-serial-summary.md`
  - decision record, measured figures, follow-up candidate.

**Verification**:
- The summary contains both negative decisions with their TESTING_GUIDE-grounded reasons, the
  follow-up candidate, and the before/after pass-1 and pass-2 figures.
- `git diff --stat` lists `oracle/bimodal_logic/tests/test_soundness_regression.py` as the only
  changed file outside `specs/`; `provider.py` and `test_example_budget_floor.py` are absent.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_soundness_regression.py --collect-only -q -m xdist_serial` selects the four newly marked tests plus the pre-existing ones.
- [ ] Total collected test count for the file is unchanged by the edit.
- [ ] `bash oracle/run-oracle-suite.sh` pass 1: zero failures (down from three), none of the four target tests selected.
- [ ] `bash oracle/run-oracle-suite.sh` pass 2: green, 19 tests, wall clock inside the 1800s budget.
- [ ] No assertion in any of the four tests was weakened, relaxed, or removed.
- [ ] `GATING_RECHECK_SOLVE_TIMEOUT_MS` remains 40000 and `MIN_CONCLUSIVE_GATING_FORMULAS` remains 100.
- [ ] `oracle/bimodal_logic/provider.py` and `code/tests/ci/test_example_budget_floor.py` are unmodified.

## Artifacts & Outputs

- `specs/172_fix_contention_flaky_soundness_regression_tests/plans/01_mark-flaky-tests-xdist-serial.md` (this file)
- `specs/172_fix_contention_flaky_soundness_regression_tests/summaries/01_mark-flaky-tests-xdist-serial-summary.md`
- Modified: `oracle/bimodal_logic/tests/test_soundness_regression.py` (four decorators + comments)
- Run log (scratchpad, not committed): the detached two-pass run output

## Rollback/Contingency

The entire code change is four additive decorator-plus-comment blocks in a single test file, so
`git revert` of the implementation commit — or `git checkout HEAD -- oracle/bimodal_logic/tests/test_soundness_regression.py`
before commit — restores the prior state exactly, with no migration, no dependency, and no other
file affected. Reverting reinstates the known flakiness but breaks nothing else.

If Phase 3's full run reveals that serialization is insufficient (i.e. one of the four still times
out in the serial pass), do not widen any budget to force green: that outcome would mean the
diagnosis is wrong, and the task should return to research with the new measurement rather than
proceed.
