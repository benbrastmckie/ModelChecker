# Implementation Plan: Fix Oracle Ternary-SAT Timeout Boundary

- **Task**: 131 - fix_oracle_ternary_sat_regression
- **Status**: [COMPLETED]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/131_fix_oracle_ternary_sat_regression/reports/01_oracle-ternary-sat-regression.md
- **Artifacts**: plans/01_fix-oracle-ternary-timeout.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/rules/state-management.md
- **Type**: python
- **Lean Intent**: false

## Overview

`TestTernarySerializationAll::test_all_sat_task_relation_ternary` is not a refactor-introduced
semantic regression. Research established that the `next_A` case's Z3 solve time clusters at
52.8-58.9s across five isolated runs split between the pre-refactor baseline `6cfb7f48` and HEAD,
against a hard 60000ms budget set at `oracle/bimodal_logic/tests/test_oracle_interface.py:1048` —
88-98% of budget, with no measurable difference between the two commits. The fix is therefore
confined to the test's own timeout budget. Done means: the primary site is widened behind a named
module-level constant, the widened budget is empirically confirmed to clear the observed variance
band across repeated isolated runs, sibling call sites sharing the same 60000ms boundary are
audited (and widened where they are boundary-exposed), and the task's own record is corrected from
"regression" to "timeout flake" so the downstream full-suite baseline task is unblocked with a
correct premise.

### Research Integration

Findings carried forward from `reports/01_oracle-ternary-sat-regression.md`, treated as settled and
not re-derived:

- Five isolated runs (3 at HEAD, 2 at baseline `6cfb7f48` via read-only worktree) span 52.80s-58.91s
  with no separation between commits. The original "passes at baseline, fails at HEAD" was one
  sample per commit landing on opposite sides of a shared boundary.
- All six constraint-building functions in the exercised path are byte-identical between baseline
  and HEAD; `oracle/` has zero diff in that range; `bimodal/operators.py` (including
  `DefNextOperator`) is unchanged.
- The one genuine behavioral diff in range (`models/structure.py` UNKNOWN-outcome reclassification)
  is proven observationally equivalent for this test's None-vs-SAT decision, because
  `Z3OracleProvider.find_countermodel` short-circuits on `not structure.z3_model_status`, which is
  `False` under both the old and new code.
- `next_A` is the only depth>0 formula in `sat_formulas`; depth 1 forces `M = max(1+2, 3) = 3`,
  the boundary where `build_frame_constraints` dispatches to the expensive
  MBQI-avoidance path. This is a known-slow region, not new.
- `code/docs/core/TESTING_GUIDE.md` section 8.6 explicitly warns against deriving a budget from a
  measured solve time plus a small margin — which is exactly what the current 60000ms is.

Research recommends `180000` ms (~3x margin over the observed maximum). This plan adopts that value.

**Design decision — named constant over a bare number.** The widening is applied as a module-level
named constant with an explanatory docstring rather than editing `60000` to `180000` in place,
because the same 60000ms boundary appears at five-plus independent call sites in this file and a
named, documented constant gives the audit in Phase 2 a single edit point and stops a future reader
from re-tightening the budget back toward the measured solve time. Sourcing the budget from an
environment variable is deliberately rejected: it would make CI timing behavior non-deterministic
and non-reproducible, which is a worse property than a generous fixed ceiling.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` supplied in the delegation context; no roadmap consultation performed.

## Goals & Non-Goals

**Goals**:
- Remove the timeout-boundary flake from `test_all_sat_task_relation_ternary` with real margin.
- Express the depth>0 solver budget as a single named, documented constant.
- Audit sibling call sites in the same file that share the 60000ms boundary and assert SAT, and
  widen the boundary-exposed ones.
- Leave the full 550-test oracle suite runnable, with a correct, verified invocation recorded for
  the downstream baseline task.
- Correct this task's record so downstream work does not inherit the false "semantic regression"
  premise.

**Non-Goals**:
- Any change under `code/src/model_checker/**`. Research proved no semantic defect there.
- Any change to `oracle/bimodal_logic/provider.py`, `operators.py`, or `semantic/core.py`.
- Solver-performance work on the M=3 MBQI-avoidance path. Research notes
  `build_grounded_abundance_constraints` was already tried as a faster M>=3 alternative and caused
  correctness and performance regressions; there is no known cheap win.
- Widening the `30000`ms call sites (lines 613, 770, 986, 1002, 1021, 1255). See Phase 2 for why
  these are audited but not changed.
- Touching `test_timeout_handling` (line 1092, `timeout_ms=1`), whose tiny budget is the point of
  the test.
- Running the full oracle suite. That is the downstream task's deliverable; this plan only
  guarantees it is runnable and records the invocation.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Test commands run in the bare interactive shell, which lacks `pytest-xdist` and resolves a different Python | H | H | Every command in this plan is wrapped in `nix develop <repo> --command bash -c '...'`. The devShell is already realized and needs no rebuild. Do not substitute a bare `python3 -m pytest`. |
| Concurrent agent sessions inflate wall-clock and corrupt timing measurements | H | M | Run `ps aux \| grep -c "[p]ytest"` immediately before every timing run in Phases 1-2; if any other pytest process is live, wait and re-run. Research flagged live concurrent sessions in this sandbox. |
| Widening budgets on tests that legitimately return `None` (UNSAT or by-design timeout) triples their runtime and slows the full suite | M | M | Apply the widened constant only at sites that assert a non-`None` result on a depth>0 formula. Sites tolerating `None` (e.g. line 837 `test_deeply_nested_enriched`) keep their existing budget. Stated explicitly as a Phase 2 rule. |
| Downstream full-suite run uses `-n auto` and CPU contention re-creates the exact boundary problem this task is fixing | H | M | `flake.nix` documents `-n auto` as a known CPU-contention flake for this repo and uses `-n 6` for its own check. The handoff in Phase 3 records `-n 6`, not `-n auto`, and states why. |
| 180000ms proves insufficient under heavy contention | L | L | Phase 2's repeated-run verification measures actual margin. If any run exceeds 120s (two-thirds of the new budget), escalate the constant rather than declaring the phase green. |
| Sibling audit uncovers a site whose solve time genuinely exceeds even the widened budget, indicating a real slow path | M | L | Phase 2 records the measurement and reports it as a finding for the downstream suite task rather than expanding this task's scope into solver work. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel. This plan is fully sequential.

---

### Phase 1: Widen the primary timeout behind a named constant [COMPLETED]

- **Goal:** Replace the hard-coded 60000ms depth>0 budget at the failing test's call site with a
  named module-level constant set to 180000ms, documented against the measured solve-time band.

- **Tasks:**
  - [x] Add a module-level constant near the top of
    `oracle/bimodal_logic/tests/test_oracle_interface.py`, adjacent to the existing module-level
    test data definitions. Suggested shape:
    ```python
    # Solver budget for formulas with temporal_depth > 0. These force M = max(depth+2, 3) >= 3,
    # which dispatches to the expensive MBQI-avoidance constraint path; measured solve times
    # cluster at 53-59s. Set generously rather than at measured-time-plus-margin, per
    # code/docs/core/TESTING_GUIDE.md section 8.6 -- a tight ceiling here produces wall-clock
    # boundary flakes, not signal.
    TEMPORAL_SOLVE_TIMEOUT_MS = 180000
    ATEMPORAL_SOLVE_TIMEOUT_MS = 10000
    ```
  - [x] Rewrite line 1048 from `timeout = 60000 if depth > 0 else 10000` to
    `timeout = TEMPORAL_SOLVE_TIMEOUT_MS if depth > 0 else ATEMPORAL_SOLVE_TIMEOUT_MS`.
  - [x] Do not modify any other call site in this phase.
  - [x] Confirm the comment contains no task-number references (per
    `.claude/rules/no-task-references-in-deliverables.md`; `oracle/` is outside `specs/**`).

- **Timing:** 0.25 hours

- **Depends on:** none

- **Files to modify:**
  - `oracle/bimodal_logic/tests/test_oracle_interface.py` - add two module-level constants; replace
    the literal budget expression at line 1048.

- **Verification:**
  - The file imports and collects cleanly, and the target test is still discovered:
    ```bash
    nix develop /home/benjamin/Projects/ModelChecker --command bash -c \
      'cd /home/benjamin/Projects/ModelChecker && \
       PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src \
       python -m pytest oracle/bimodal_logic/tests/test_oracle_interface.py \
         --collect-only -q 2>&1 | tail -5'
    ```
    Success criterion: collection reports no errors and a non-zero test count.
  - Exactly one `60000` literal is gone and the two new constants are present:
    ```bash
    grep -n "TEMPORAL_SOLVE_TIMEOUT_MS\|ATEMPORAL_SOLVE_TIMEOUT_MS" \
      /home/benjamin/Projects/ModelChecker/oracle/bimodal_logic/tests/test_oracle_interface.py
    ```
    Success criterion: the definitions appear once each at module level, plus one usage each at the
    rewritten line 1048 site.

---

### Phase 2: Verify the fix and audit sibling boundary sites [COMPLETED]

- **Goal:** Empirically confirm the widened budget clears the observed variance band with real
  margin, and determine which sibling call sites share the 60000ms boundary risk and widen those
  that do.

- **Tasks:**
  - [x] Confirm no competing pytest processes before timing:
    `ps aux | grep -c "[p]ytest"` must report `0`. (Confirmed `0` before every timing run below.)
  - [x] Run the target test 5 times in isolation inside the devShell, recording each wall clock.
    Results: 53.79s, 63.80s, 52.46s, 51.19s, 50.98s (per-test `call` durations 53.59/63.55/52.29/
    50.99/50.79s) — all 5 PASSED.
  - [x] Record the observed maximum. Green requires all 5 runs PASSED **and** the maximum below
    120000ms (two-thirds of the new budget). If any run exceeds that, do not mark the phase
    complete — raise `TEMPORAL_SOLVE_TIMEOUT_MS` and re-verify.
    Observed max 63.55s (35.3% of the 180000ms budget) — well under the 120000ms bar. No escalation
    needed.
  - [x] Enumerate sibling depth>0 sites in the same file that use a 60000ms budget **and** assert a
    non-`None` result. Research plus direct inspection identify this cohort:
    - line 731-733, `test_enriched_vs_primitive_sat_agreement` (`timeout = 60000 if depth > 0 else
      10000`; a one-sided timeout produces a false SAT/UNSAT mismatch failure)
    - line 807-809, `test_mixed_and_neg_some_future`
    - line 815-817, `test_mixed_and_box_next`
    - line 821-824, `test_mixed_or_diamond_prev`
    - line 828-831, `test_mixed_and_all_future_neg`
    - line 951-952 and line 964, the `timeout_ms=60000` sites asserting non-`None`

    **Deviation**: direct inspection of the current file shows line 964 (loop over
    `valid_formulas`, now at line 972 after Phase 1's +8 line insertion) actually asserts
    `result is None` (expects F4/F7/F9/F10 to be valid/UNSAT), not non-`None`. Only the F5 call
    immediately above it (line 951-952, now line 959) is a genuine assert-non-`None` site. The
    `valid_formulas` loop is treated as a tolerates-`None` site instead (see the explicitly-
    unchanged list below) — this is a correction to the plan's site enumeration, not a scope
    change.
  - [x] Time each cohort member once. Apply `TEMPORAL_SOLVE_TIMEOUT_MS` to any whose measured solve
    time exceeds 30000ms (i.e. is within 2x of its current 60000ms ceiling). Leave members
    comfortably below that threshold at their current budget and record the measurement.

    Measurements (pre-widening, single run each) and disposition:
    | Site | Measured | Disposition |
    |------|----------|-------------|
    | `test_enriched_vs_primitive_sat_agreement[next]` | 104.02s combined (enriched+primitive) | **Widened** — same M=3 case as the primary fix |
    | `test_enriched_vs_primitive_sat_agreement[all_future]` | 125.32s combined pre-edit; 379.57s post-edit | **Widened**, but see finding below — genuinely exceeds even 180000ms per call |
    | `test_enriched_vs_primitive_sat_agreement[some_past]` | 64.13s combined | **Widened** (conservatively, part of the same parametrized timeout expression as `next`/`all_future`) |
    | `test_mixed_and_neg_some_future` | 38.54s | **Widened** (>30000ms, <2x headroom under 60000ms) |
    | line 959 (F5 site) | 241.95s total for the whole test; isolated single-call measurement 0.64s | **Widened** (harmless; isolated timing shows no real risk, kept for margin/consistency) |
    | `test_mixed_and_box_next` | 17.53s (pre-edit); 14.21s (post-edit re-run) | Left unchanged — >=2x headroom under 60000ms |
    | `test_mixed_and_all_future_neg` | 25.75s (pre-edit); 21.62s (post-edit re-run) | Left unchanged — >=2x headroom under 60000ms |
    | `test_mixed_or_diamond_prev` | 1.46s / 1.33s | Left unchanged — far below threshold |
    | `test_deeply_nested_enriched` | 60.33s / 60.34s | Left unchanged — tolerates `None` by design |
    | `valid_formulas` loop (F4/F7/F9/F10) | ~241.3s aggregate over 4 calls (241.97s total minus F5's isolated 0.64s) | Left unchanged — tolerates `None` by design (see deviation note above) |

    **Finding for the downstream full-suite task (not fixed here, per this plan's own risk
    mitigation against solver-performance scope creep)**: isolated instrumentation of the
    `all_future` pair shows the **enriched form takes 195.47s and the primitive form 187.63s,
    both returning `None` (timeout) even at the new 180000ms budget**. The test still passes
    because both sides agree (`None == None`), but this is very likely a masked pre-existing
    timeout-equivalence, not a verified semantic agreement — the same pathology existed at the
    original 60000ms budget too (both sides would have timed out there as well). Widening did not
    fix or worsen this; it is a genuinely slow query, not a boundary flake, and is out of this
    plan's scope. The `test_deeply_nested_enriched` (60.34s at its own 60000ms ceiling) and the
    `valid_formulas` loop (~60s/call average) sites show the same tolerate-`None` pattern and may
    also be silently masking timeouts as UNSAT-equivalence.
  - [x] Explicitly leave unchanged, and record the reason for each:
    - line 837 (now 845 post-Phase-1) `test_deeply_nested_enriched` — asserts
      `isinstance(result, (dict, type(None)))`, so it tolerates `None`; widening only lengthens a
      by-design timeout.
    - line 1096 `test_timeout_handling` — `timeout_ms=1` is the subject of the test.
    - all `30000`ms sites (now 621, 778, 994, 1010, 1029, 1263 post-Phase-1) — these are either
      guarded by `if result is not None:` or compare against an expected SAT/UNSAT verdict that
      includes legitimately-`None` UNSAT examples; widening them would materially lengthen the
      full suite without removing an assertion-level flake.
    - the `valid_formulas` loop (line 972) — added to this list per the deviation noted above;
      tolerates `None` for F4/F7/F9/F10 (expected valid/UNSAT), so a timeout is indistinguishable
      from the expected outcome and widening only lengthens a by-design (possibly already-masked)
      timeout.
  - [x] Record every measurement in the phase notes so Phase 3's handoff can cite real numbers.
    (See tables above.)

- **Timing:** 1.25 hours (mostly solver wall clock; ~5 minutes of edits)

- **Depends on:** 1

- **Files to modify:**
  - `oracle/bimodal_logic/tests/test_oracle_interface.py` - apply `TEMPORAL_SOLVE_TIMEOUT_MS` to
    boundary-exposed cohort members identified by measurement.

- **Verification:**
  - Five isolated runs of the target test, all PASSED:
    ```bash
    nix develop /home/benjamin/Projects/ModelChecker --command bash -c \
      'cd /home/benjamin/Projects/ModelChecker && \
       for i in 1 2 3 4 5; do \
         PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src \
         python -m pytest \
           "oracle/bimodal_logic/tests/test_oracle_interface.py::TestTernarySerializationAll::test_all_sat_task_relation_ternary" \
           -q --durations=0 2>&1 | tail -3; \
       done'
    ```
    Success criterion: 5/5 report `1 passed`, and the slowest reported duration is under 120s.
  - The enclosing class passes end to end:
    ```bash
    nix develop /home/benjamin/Projects/ModelChecker --command bash -c \
      'cd /home/benjamin/Projects/ModelChecker && \
       PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src \
       python -m pytest \
         "oracle/bimodal_logic/tests/test_oracle_interface.py::TestTernarySerializationAll" \
         -v --durations=0'
    ```
    Success criterion: all tests in the class pass.
  - The audited cohort passes:
    ```bash
    nix develop /home/benjamin/Projects/ModelChecker --command bash -c \
      'cd /home/benjamin/Projects/ModelChecker && \
       PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src \
       python -m pytest oracle/bimodal_logic/tests/test_oracle_interface.py \
         -k "enriched_vs_primitive or mixed_ or ternary" -q --durations=0'
    ```
    Success criterion: zero failures, and every reported duration has at least 2x headroom under
    its site's budget.
  - No unintended literal survives in the depth>0 assert-SAT cohort:
    ```bash
    grep -n "60000" \
      /home/benjamin/Projects/ModelChecker/oracle/bimodal_logic/tests/test_oracle_interface.py
    ```
    Success criterion: every remaining `60000` occurrence corresponds to a site explicitly listed
    above as intentionally unchanged.

---

### Phase 3: Correct the task record and publish the full-suite handoff [COMPLETED]

- **Goal:** Replace the false "refactor-introduced semantic regression" framing in this task's own
  record with the established timeout-flake finding, and record a verified, runnable invocation for
  the downstream 550-test oracle baseline so it proceeds on correct premises.

- **Tasks:**
  - [x] Update this task's `completion_summary` in `specs/state.json` to state the finding as a
    timeout-budget boundary flake with no semantic defect, then regenerate TODO.md via
    `bash .claude/scripts/generate-todo.sh`. Do not hand-edit TODO.md.
  - [x] Write the implementation summary to
    `specs/131_fix_oracle_ternary_sat_regression/summaries/01_fix-oracle-ternary-timeout-summary.md`,
    including the Phase 2 measurement table and the explicit list of sites left unchanged with
    reasons.
  - [x] Record in the summary that the downstream baseline task's stated blocker
    ("pytest-xdist unavailable") is **false**: `pytest-xdist` is declared at `flake.nix:72` and
    `code/pyproject.toml:48`, and is present and already realized inside the devShell with no
    rebuild required. It is absent only from the bare interactive Python.
  - [x] Record the handoff invocation for the full oracle suite, using `-n 6` rather than `-n auto`.
    State the reason inline: `flake.nix` documents `-n auto` as a known CPU-contention flake for
    this repo and pins its own `checks.default` to `-n 6`; since this task's entire failure mode is
    wall-clock contention against a solver budget, `-n auto` would risk re-creating it under a
    different name.
  - [x] State the exit criteria for the downstream run explicitly: the devShell provides pytest,
    z3, `pytest-xdist`, and `PYTHONPATH` (its shellHook exports `code/src` plus the BimodalHarness
    sibling when present); `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness` is confirmed
    on disk (re-confirmed present); no `code/` or `oracle/` source change was made by this task, so
    any suite failure is pre-existing and not attributable to it.

- **Timing:** 0.5 hours

- **Depends on:** 2

- **Files to modify:**
  - `specs/state.json` - corrected `completion_summary` for this task.
  - `specs/131_fix_oracle_ternary_sat_regression/summaries/01_fix-oracle-ternary-timeout-summary.md` - new.
  - `specs/TODO.md` - regenerated, not hand-edited.

- **Verification:**
  - The handoff invocation collects the full suite without error (collection only — running it is
    the downstream task's job):
    ```bash
    nix develop /home/benjamin/Projects/ModelChecker --command bash -c \
      'cd /home/benjamin/Projects/ModelChecker && \
       PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src \
       python -m pytest oracle/ -n 6 --collect-only -q 2>&1 | tail -5'
    ```
    Success criterion: collection completes with no errors and reports the expected suite size;
    `-n 6` is accepted, proving `pytest-xdist` is live.
  - No source outside the test file was touched:
    ```bash
    cd /home/benjamin/Projects/ModelChecker && git status --short -- code/ oracle/
    ```
    Success criterion: the only listed path is
    `oracle/bimodal_logic/tests/test_oracle_interface.py`.
  - The summary file exists and is non-empty, and `specs/state.json` parses:
    ```bash
    jq -e '.active_projects[] | select(.project_number == 131) | .completion_summary' \
      /home/benjamin/Projects/ModelChecker/specs/state.json
    ```
    Success criterion: exits 0 and prints the corrected timeout-flake framing.

---

## Testing & Validation

- [x] `test_all_sat_task_relation_ternary` passes 5/5 in isolation inside `nix develop`, slowest run
      under 120s against the 180000ms budget. (Max 63.55s.)
- [x] `TestTernarySerializationAll` passes end to end.
- [x] The audited sibling cohort (`enriched_vs_primitive`, `mixed_*`, ternary tests) passes with at
      least 2x headroom under each site's budget, **except** the `all_future` parametrize case
      (recorded as a finding, not fixed — genuinely exceeds even the widened budget; see Phase 2
      notes and the summary).
- [x] `pytest --collect-only` on `oracle/` succeeds under `-n 6`, confirming the full suite is
      runnable for the downstream baseline task. (550 tests collected.)
- [x] `git status --short -- code/ oracle/` lists only the test file among files this task
      touched. Other `code/` files appear modified but were already dirty before this task began
      (pre-existing concurrent-session work this task did not touch) — see the summary's
      verification section.
- [x] No task-number references were added by this task's edits (the constants/comment added at
      lines 110-116 and the widened call sites contain none). Pre-existing task-number references
      elsewhere in the file (e.g. lines 3, 1139-1147) predate this task and are out of its scope.

## Artifacts & Outputs

- `oracle/bimodal_logic/tests/test_oracle_interface.py` - two new module-level timeout constants;
  widened budgets at the primary site and at boundary-exposed cohort members.
- `specs/131_fix_oracle_ternary_sat_regression/plans/01_fix-oracle-ternary-timeout.md` - this plan.
- `specs/131_fix_oracle_ternary_sat_regression/summaries/01_fix-oracle-ternary-timeout-summary.md` -
  measurement table, unchanged-site rationale, corrected framing, and the full-suite handoff
  invocation.
- `specs/state.json` / `specs/TODO.md` - corrected task record.

## Rollback/Contingency

The change is confined to a single test file and is trivially revertible with
`git checkout HEAD -- oracle/bimodal_logic/tests/test_oracle_interface.py` (safe here only because
no other uncommitted work exists in that file; otherwise run `bash .claude/scripts/git-snapshot.sh`
first, per `.claude/rules/git-workflow.md`). Reverting restores the 60000ms budget and with it the
boundary flake — it does not restore any semantic behavior, since none was changed.

If Phase 2 shows the target test exceeding 120s even at the widened budget, do not escalate into
solver work inside this task. Record the measurement, raise the constant to clear it, and report the
slow path as a finding for a separate performance task; research already established that the known
alternative constraint path regressed both correctness and performance.
