# Task 140: Fix Bimodal Order Dependence and Baseline-Script Bugs

## Scope Covered This Session

This session picked up from commits `4efdbfd7` (baseline-comparison masking fix) and `29e1fdec`
(progress record) on branch `task-140-fix-bimodal-order-dependence`, which had already resolved
item 3's masking defect but left the true root causes of items 1, 2, 4, and 5 open. This
dispatch resolved items 1, 2, and the remainder of item 3, and attempted item 4.

## Item 2 (PRIMARY): Root Cause of Order-Dependent Cross-Test Failures

**Finding**: `code/src/model_checker/theory_lib/bimodal/operators.py` defines a process-global
`_bound_var_counter = itertools.count()` used by `_fresh_bound_int()` to name every
quantifier-bound Z3 `Int` constant (e.g. `t!17`). This counter is never reset across examples,
even though `model_checker.utils.context.isolated_z3_context()` swaps in a brand-new Z3
`Context()` for every example specifically to prevent cross-test state leakage (and already
resets the analogous `AtomSort` cache for the same reason).

Because the counter is never reset, the *numeric suffix* in every bound variable's name depends
on how many prior examples ran earlier in the same pytest process. That leaked, run-order-
dependent naming is enough to perturb Z3's MBQI-driven quantifier instantiation path and flip an
example between success and failure -- purely a function of process history, not of the example
itself.

**Empirical confirmation** (via a standalone script, no pytest involved): running BM_CM_4 alone
with `_bound_var_counter` pre-seeded at 17 -- the exact value the counter reaches after
`EX_CM_1`, `MD_CM_1..6`, `BM_CM_1`, `BM_CM_2` run in `test_bimodal.py`'s fixed parametrize
order -- reproduces the isolated-run failure deterministically. Every other tested seed (0, 5,
10, 13, 15, 16, 18, 20, 25, 30) passes. This fully explains why `test_bimodal.py` run alone
(only 9 preceding examples, ending at counter=17) fails, while the same test inside the full
`bimodal/tests/` run (many more preceding examples, counter far past 17 by the time BM_CM_4
runs) or any subset with fewer than all 9 preceding tests removed from that exact set, passes.

**Fix**: added `operators.reset_bound_var_counter()` and call it from
`BimodalSemantics._reset_global_state()` (`semantic/core.py`), which already runs at the very
start of every fresh `BimodalSemantics.__init__` and is explicitly documented for "reset[ting]
any global state that could cause interference between examples."

**Why this is safe, not a reintroduction of the bug the counter exists to prevent**: the
counter's docstring explains it guards against `z3.Int()`'s name-based interning aliasing two
calls that produce the same name. That hazard is only possible *within a single Z3 Context* --
two terms with the same name are the literal same AST node only within the same context/ast
manager. Since every `BimodalSemantics` instance is used inside its own fresh
`isolated_z3_context()` Context, a counter reset to 0 at the start of each instance's lifetime
still hands out strictly increasing, therefore distinct, suffixes for every call made against
that instance's Context -- the aliasing guarantee is fully preserved.

## Item 1: Re-Measured, Not a Separate Defect

Per the branch's own progress record, item 1's originally-recorded figures were already known to
be stale. Re-measured fresh (not assumed) after the item 2 fix: `BM_CM_1-example_case7` passes
inside the full `bimodal/tests/` run (302/302 passed, twice consecutively) and inside
`test_bimodal.py` alone (43/43 passed, three times consecutively). It was a downstream symptom
of the same counter leak, not an independent defect.

## Item 3: Remaining Low-Severity Fixes

- `code/scripts/compare_bimodal_baseline.sh`'s default baseline path (used when the script is
  invoked with no argument, as its own usage comment advertises) pointed at
  `specs/097_optimize_build_frame_constraints/baseline_results.txt`, which moved to
  `specs/archive/097_optimize_build_frame_constraints/baseline_results.txt` when task 97 was
  archived. Fixed the default to the archive location.
- "EXTRA tests" mislabeling: pytest's `-v` output lists every FAILED test twice -- once as its
  per-test progress line (`...test_name[...] FAILED [ NN%]`), and again in the "short test
  summary info" section (`FAILED path::test_name[...]`). The script's original extraction
  (`grep -E "PASSED|FAILED|ERROR|SKIPPED"`) captured both occurrences, which desynced
  `CURRENT_NAMES` (two entries for a failing test) from `BASELINE_NAMES` (one entry), causing
  `comm -13` to misreport the duplicate occurrence as "EXTRA tests (in current but not
  baseline)" for any genuinely-failing test. Fixed by restricting the extraction to lines ending
  in a `[ NN%]` progress marker, which only the per-test progress lines have.

## Item 4: Gating Oracle Suite (Attempted)

Per the dispatch's stated priority ("only attempt if items 1-3 are resolved and you have time"),
items 1-3 were resolved first. `oracle/run-oracle-suite.sh` was then launched inside
`nix develop`. See `.orchestrator-handoff.json` and any follow-up note in this summary's final
revision for the outcome recorded before this session ended -- if the run did not reach a
verdict before the session concluded, item 4 remains an open blocker exactly as before, and
nothing about its prior characterization (two `OracleTimeoutError` failures, one 900s
non-termination) should be assumed resolved without a fresh, complete run's output.

## Item 5: Environment Discipline

All adjudication in this session was performed inside `nix develop` (python 3.12.13). No
bare-PATH python result was used to characterize any outcome.

## Hard Constraints: Compliance

No pin, timeout budget, conclusive floor, xfail marker, assertion, `strict=True` requirement, or
guard was weakened, widened, deleted, or relaxed anywhere in the repository. Specifically:
`code/scripts/verify-refactor.sh`, `oracle/bimodal_logic/tests/test_oracle_interface.py`, and the
recorded 43-pass baseline file (`specs/archive/097_optimize_build_frame_constraints/baseline_results.txt`)
are all untouched by this session's commits (verified via `git diff` against each before
committing).

## Verification Performed (all inside `nix develop`)

- New regression tests `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bound_var_counter_isolation.py`:
  RED before the fix (poisoned-counter-at-17 end-to-end case fails; reset-to-zero unit assertion
  fails), GREEN after (4/4 passed).
- `test_bimodal.py` alone: 43 passed, 3 consecutive runs (~29-30s each, versus 38-41s before the
  fix, consistent with removing accumulated bound-variable-name growth).
- Full `bimodal/tests/`: 302 passed, 2 consecutive runs (~175-185s each).
- `compare_bimodal_baseline.sh` invoked with no argument (exercising the new default path):
  "Baseline: 43 passed / Current: 43 passed, 0 failed, total=43 / OK: 0 regressions (matches
  baseline)".
- `verify-refactor.sh --skip-oracle`: all of Steps 1-5 and 7 green, including Step 4 ("bimodal
  in-package suite") green on the **first** attempt for the first time on this branch --
  previously it needed its documented one-retry allowance for the same underlying flake.

## Plan Deviations

- None (no plan file existed for this task; work followed the delegation context's stated
  priority order and the branch's own progress record verbatim).

## Files Changed

- `code/src/model_checker/theory_lib/bimodal/operators.py` -- added `reset_bound_var_counter()`.
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` -- call it from
  `_reset_global_state()`.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bound_var_counter_isolation.py` --
  new regression tests (both the direct reset assertion and the end-to-end poisoned-counter
  reproduction).
- `code/scripts/compare_bimodal_baseline.sh` -- default baseline path fix; EXTRA/MISSING
  name-extraction fix.
