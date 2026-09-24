# Blocker Analysis: Task #172

**Parent Task**: #172 - fix_contention_flaky_soundness_regression_tests
**Generated**: 2026-08-31
**Blocker**: `TestShiftClosure::test_shift_closure_on_extracted_worlds_m3` fails deterministically
(2/2 independent full pass-1 runs) with `AssertionError: Solver should find SAT for atom 'p' at
M=3 with depth-bounded abundance`, a defect that shares no mechanism with the four
`find_countermodel`/`xdist_serial` tests this task's approved remedy targets.

## Root Cause

Task 172's Phase 1 inventory correctly scoped itself to bare-default `find_countermodel(` call
sites with `timeout_ms=5000` (the CPU-contention flake class). Phase 3's mandatory full two-pass
verification (`bash oracle/run-oracle-suite.sh`, per the plan's own Non-Goals: "narrowed gates are
what hid this defect originally") surfaced a fifth, unrelated failure in the same file:
`oracle/bimodal_logic/tests/test_soundness_regression.py:541`
(`TestShiftClosure::test_shift_closure_on_extracted_worlds_m3`).

**Reproduced 2/2** across two independent full pass-1 runs (`1 failed, 615 passed, 2 skipped,
4 xfailed`, 705.05s and 718.15s — see
`specs/172_fix_contention_flaky_soundness_regression_tests/summaries/01_mark-flaky-tests-xdist-serial-summary.md`
and the scratchpad logs `oracle-suite-post.log` / `oracle-pass1-rerun.log`). This is
**deterministic, not the contention-flake class task 172 addresses** — an earlier "possible
contention blip" hypothesis recorded in the plan is explicitly retracted in the summary.

**Why 172 cannot fix it (mechanism mismatch, confirmed by reading the test body at
`test_soundness_regression.py:508-556`)**: the test constructs `BimodalStructure` directly —

```python
settings = {'N': 2, 'M': 3, 'temporal_depth': 1, ..., 'max_time': 15.0, ...}
semantics = BimodalSemantics(settings)
structure = BimodalStructure(model_constraints, settings)
assert structure.z3_model_status and not structure.timeout, (
    "Solver should find SAT for atom 'p' at M=3 with depth-bounded abundance"
)
```

It never calls `Z3OracleProvider.find_countermodel()`, so it never touches the
`timeout_ms=5000`/`OracleTimeoutError` scheduling path that task 172's `xdist_serial` remedy
targets. It uses its own `max_time: 15.0` budget on a genuinely different code path (direct
`BimodalSemantics`/`BimodalStructure` construction). Task 172's plan (Phase 3, Non-Goals) and
summary both record this explicitly and correctly declined to widen scope to fix it — "in scope
by file... but out of scope by remedy."

**Not budget-related on its face.** Historical baselines
(`specs/archive/108_soundness_regression_test_suite/`,
`specs/archive/114_skolem_abundance_overconstrain_fix/`) show this exact test previously ran
2-8s against its 15s `max_time` budget — 2-7x headroom, not a near-budget shape. The failure
message and the plan/summary's own characterization (`structure.z3_model_status is False`)
indicate the solver is reporting UNSAT (or a non-timeout non-SAT status) within budget, not
timing out — this report could not independently re-run the test to confirm `structure.timeout`'s
exact value, so the spawned task must verify this first rather than assume it.

**This is a regression against a previously-fixed defect, not a fresh symptom.** The test's own
docstring cites "Task 114 fix: uses `temporal_depth=1` for bounded shift closure at M=3" and the
archived task-114 summary (`specs/archive/114_skolem_abundance_overconstrain_fix/summaries/`)
confirms: task 114 (2026-06-01) introduced
`BimodalSemantics.depth_bounded_skolem_abundance_constraint(max_shift)` specifically so this test
would find SAT at M=3, removed its prior `xfail`, and it has apparently held since. `git log` on
`code/src/model_checker/theory_lib/bimodal/semantic/core.py` shows three later commits
(task 144 phases 2-4, 2026-08-11) that experimented with alternative Z3 trigger/grounding
strategies for the same `depth_bounded_skolem_abundance_constraint` quantifier — but each is
explicitly logged as "Reverted" / "tested and rejected" in its own commit message, so the current
encoding should be byte-identical to the post-task-114 baseline. Whether an incomplete revert, an
unrelated code change, or (per `code/pyproject.toml:29`, `"z3-solver>=4.8.0"` — an **unpinned
lower bound only**) a drifted `z3-solver` package version (currently installed: 4.16.0) altered
solver behavior on this exact quantifier shape is the open question the spawned task must answer
with evidence, not assume.

`git log --stat` on tasks 152/158/175's landed commits (cited in the plan/summary) touches no
bimodal semantic/solver code this test depends on, ruling out same-window tree drift from
concurrently-running tasks as the cause.

## Proposed New Tasks

### New Item 1: Root-cause and fix the M=3 depth-bounded shift-closure SAT regression
- **Effort**: 3-5 hours
- **Task Type**: python
- **Rationale**: This is the sole remaining defect blocking task 172's Phase 3 exit criterion
  ("pass 1: zero failures"). It requires investigating the Z3 constraint/solver layer (why a
  previously-SAT-finding encoding at M=3 with `temporal_depth=1` now reports non-SAT within a
  15s budget with 2-7x historical headroom), not test scheduling — a different discipline from
  172's `xdist_serial` remedy and explicitly out of that task's approved scope.
- **Depends on**: None

## Dependency Reasoning

A single task fully addresses this blocker — there is no natural split point. Investigation
(confirming timeout vs. genuine UNSAT, bisecting `depth_bounded_skolem_abundance_constraint`
history, checking `z3-solver` version drift) and remediation (a constraint fix, or — only if a
genuine fix is not found and TESTING_GUIDE.md section 8.9's four `unstable`-marker entry criteria
are honestly met — a documented `unstable` marking with a measured, non-semantic mechanism and a
concrete exit criterion) are one coherent unit of work on one narrowly-scoped test. Splitting
"investigate" from "fix" would produce a research task whose output is entirely consumed by
implementation choices in the same file, with no independent value on its own — exactly the case
the Task Minimization Principle's Sequentiality clause argues against ever spawning as two tasks.

No task-to-task dependency edges exist because only one task is spawned.

**Follow-up candidate 1 from task 172's summary was evaluated and NOT spawned.**
`oracle/bimodal_logic/tests/test_oracle_provider.py::test_future_sat_returns_dict` shares the
same *risk class* as the four tests task 172 already fixed (bare-default `find_countermodel`
call, `temporal_depth=1`, no `xdist_serial` marker) — but unlike the M=3 shift-closure failure,
it has **never been observed failing**; task 172's own report calls it a "same risk class"
prediction, not a measured defect. It is also mechanistically identical to the class task 172
already has a proven remedy for (route to `xdist_serial`), so it does not need dedicated
root-cause investigation the way the M=3 failure does. Spawning a task on unobserved risk with a
known, cheap fix would violate this task's explicit "keep spawned scope MINIMAL... do not bundle
in unrelated oracle work" instruction and the Task Minimization Principle's preference for fewer
tasks. If it is later observed failing, it is a one-line `xdist_serial` marker addition (task 172's
own precedent) and does not warrant a `/spawn` cycle of its own.

## After Completion

Once the spawned task is complete, resume the parent task #172 with `/implement 172` — its
Phase 3 verification only needs to be re-run once, not repeated per-fix, since the four-test
remedy is already independently verified and the new task will confirm the fifth failure is gone
in the same full-suite run it performs for its own verification.

The blocker will be resolved because: task 172's Phase 3 verification criterion ("pass 1: zero
failures") currently fails solely due to
`TestShiftClosure::test_shift_closure_on_extracted_worlds_m3`. Once that test is fixed (or
legitimately `unstable`-marked per TESTING_GUIDE 8.9, which would also make pass 1 report zero
failures), a fresh `bash oracle/run-oracle-suite.sh` run has no remaining obstacle to reporting
zero pass-1 failures, and task 172 can close `[COMPLETED]`.
