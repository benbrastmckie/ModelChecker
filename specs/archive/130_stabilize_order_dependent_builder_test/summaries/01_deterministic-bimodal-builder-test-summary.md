# Implementation Summary: Deterministic, correctly-named bimodal BuildExample integration test

- **Plan**: `specs/130_stabilize_order_dependent_builder_test/plans/01_deterministic-bimodal-builder-test.md`
- **Status**: COMPLETED (4/4 phases)
- **Files changed**: `code/src/model_checker/builder/tests/unit/test_example.py` (one file, as
  scoped)

## What Changed

1. Renamed `TestBuildExampleIntegration.test_logos_extensional_theory` to
   `test_build_example_bimodal_theory_countermodel`, matching the file's `test_build_example_*`
   sibling convention and describing what the body actually does.
2. Rewrote the docstring and in-body comments to describe the bimodal theory the test actually
   loads (dropping all "logos"/"extensional restriction" framing) and to note that
   `get_theory(config=None)` in the bimodal theory accepts but ignores its `config` argument, so
   the loaded theory is always the full bimodal theory.
3. Renamed the `semantic_theories` dict key and the two `BuildModule`/`BuildExample` lookups from
   `"Extensional"` to `"Bimodal"` (not explicitly listed in the plan's task checklist, but
   necessary to avoid reintroducing the same misleading framing the rename was meant to fix).
   Renamed the inline temp file from `logos_test.py` to `bimodal_test.py`.
4. Added explicit `max_time` to the `SIMPLE` example's settings dict, replacing the inherited
   `BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS['max_time'] = 1` default that raced against the
   real ~1.7-2s solve. **Final value is `max_time: 30`, not the plan's initial `max_time: 10`**
   (see Deviations).
5. Left the `assertTrue(result["model_found"], ...)` assertion and its message unchanged — the
   research established the countermodel genuinely exists; only the timing budget and naming
   needed to change.

## Verification: Three-Invocation Determinism

All commands run with `PYTHONPATH=code/src`.

| Invocation | Result | Observed call time(s) |
|---|---|---|
| Isolated node id, run 1 | PASS | 1.98s |
| Isolated node id, run 2 | PASS | 1.85s |
| File-scope (`test_example.py`) | PASS | 0.69s |
| Full builder suite, run 1 | PASS | 1.37s |
| Full builder suite, run 2 (extra) | PASS | 15.08s |
| Full builder suite, run 3 (extra) | PASS | not individually logged; suite-level PASS confirmed |

The target test passed **identically** (no `TIMEOUT: Model search exceeded maximum time`, always
a genuine `model_found=True`) across every invocation, with the full three-way requirement (2x
isolated, file-scope, full-suite) satisfied and two additional full-suite runs added for extra
confidence given the wide variance observed (1.37s-15.08s call time under full-suite load).

Full raw output for every run is saved under
`specs/130_stabilize_order_dependent_builder_test/baselines/`:
`pre-change-three-invocations.txt`, `pre-change-failed-set.txt`,
`post-change-three-invocations.txt`, `failed-set-diff.txt`, plus the intermediate
`attempt1-max_time_10-*` files documenting the first (insufficient) attempt.

## FAILED-Set Regression Check

Compared by test node id (message-text comparison was unusable — two pre-existing
e2e/performance failures embed run-to-run-variable floating-point timings in their `FAILED` line).
Both pre-change and post-change full-suite runs have the identical 5-item FAILED set:
`test_theory_library_execution`, `test_multiple_examples_process_efficiently`,
`test_small_model_generation_completes_quickly`, `test_find_next_model_basic`,
`test_project_initialization_default`. Zero regressions, zero new failures. Full detail in
`baselines/failed-set-diff.txt`.

## Out-of-Scope Failure: `test_find_next_model_basic`

Per the delegation, this is explicitly **not fixed**. Honest state-of-file record: it still fails
in every invocation observed during this task, but its failure mode varied between runs —
most commonly `AttributeError: 'BuildExample' object has no attribute 'find_next_model'`, but one
file-scope run during Phase 4 verification instead showed
`AssertionError: False is not true : Should find initial model for A` (its `SAT` example, like
the target test's original `SIMPLE` example, also omits `max_time` and inherits the same 1s
default — the plan's own Follow-Up Candidates section already flags this as the same
missing-headroom pattern applying to this test too).

## Plan Deviations

1. **Observed pre-change polarity contradicted the plan's stated assumption.** The plan's
   "Research Integration" section asserted the test "FAILS deterministically in all three
   invocations" on this branch. Phase 1's actual measurement showed the isolated run FAILS but
   both the file-scope and full-suite runs PASS — the classic order-dependent-flakiness pattern
   the task is named for, and if anything a cleaner demonstration of the root cause than the
   plan's stated baseline. Phase 1 was explicitly designed to re-confirm rather than assume, so
   this is a correction to a documented assumption, not a plan violation.
2. **`max_time` raised from the plan's initial 10 to 30, via the plan's own documented
   contingency.** The first attempt at `max_time: 10` passed both isolated runs and the
   file-scope run but FAILED the full-suite run with a 10.11s call time — a genuine timeout at
   the budget boundary. The plan's Rollback/Contingency section explicitly covers this case
   ("If Phase 4 shows the test still flakes at `max_time: 10`, the contingency is to raise the
   budget further ... rather than to weaken the assertion"), and names 30s (matching sibling
   bimodal examples' CI-variance headroom) as the next step. Applied that exactly, then re-ran
   Phase 4's full verification suite plus two extra full-suite runs for confidence given the
   observed variance.
3. **Renamed `semantic_theories` dict key and temp filename beyond the plan's explicit
   checklist** (`"Extensional"` -> `"Bimodal"`, `logos_test.py` -> `bimodal_test.py`) to avoid
   reintroducing misleading framing after the method rename; the temp-file rename was already
   listed as a "consider" item in the plan and was applied.
4. **FAILED-set diff shape differs from the plan's expectation** because of deviation 1: since
   the target test was never in the pre-change FAILED set (it passed in that run), there was no
   "removal" to observe — the correct diff is empty in both directions, which is the strongest
   possible regression-free result, not a deviation from intent.

## Follow-Up Candidates (unchanged from plan, not actioned)

- `theory_lib/bimodal/__init__.py`'s `get_theory(config=None)` ignores its `config` argument
  repository-wide.
- `test_find_next_model_basic` needs the same `max_time` fix and has a broken
  `find_next_model()` API reference.
