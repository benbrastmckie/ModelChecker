# Task 140: Item 4 Continuation -- BM_CM_4 A/B Diagnosis and box_next Characterization

## Scope Covered This Session

Continuation dispatch focused solely on item 4. Items 1-3 were already done and committed
(`71d437bd`) before this session began; this dispatch did not touch them. This session's job was
the clean A/B comparison requested to determine whether the three new BM_CM_4 oracle failures
seen in the gating suite's pass 1 (`-n 6` parallel) were caused by the `reset_bound_var_counter()`
fix, plus a secondary characterization of the long-standing `test_mixed_and_box_next`
`OracleTimeoutError`.

## Primary Finding: BM_CM_4 Oracle Failures Are a Pass-1 Contention Artifact, Not a Regression

Ran the 3 BM_CM_4 oracle tests serially (`-p no:xdist`, no `-n`), inside `nix develop`, at two
commits:

**At HEAD (`71d437bd`, post-fix)**:
```
oracle/bimodal_logic/tests/test_boundary_regression.py::TestBoundaryDocumentation::test_countermodel_bm_cm4_at_example_settings PASSED [ 33%]
oracle/bimodal_logic/tests/test_boundary_regression.py::TestExampleRegression::test_regression_all_active_examples[BM_CM_4-example_case9] PASSED [ 66%]
oracle/bimodal_logic/tests/test_oracle_provider.py::TestOracleExampleRegression::test_regression_standard_pipeline[BM_CM_4-example_case8] PASSED [100%]
3 passed in 59.55s
```

**At pre-fix commit `29e1fdec`** (via `git worktree add --detach <scratch-dir> 29e1fdec`, removed
after use; working tree and branch never touched):
```
oracle/bimodal_logic/tests/test_boundary_regression.py::TestBoundaryDocumentation::test_countermodel_bm_cm4_at_example_settings PASSED [ 33%]
oracle/bimodal_logic/tests/test_boundary_regression.py::TestExampleRegression::test_regression_all_active_examples[BM_CM_4-example_case9] PASSED [ 66%]
oracle/bimodal_logic/tests/test_oracle_provider.py::TestOracleExampleRegression::test_regression_standard_pipeline[BM_CM_4-example_case8] PASSED [100%]
3 passed in 31.07s
```

**Conclusion**: All 3 tests pass at both commits when run serially -- this is outcome 3 of the
three possible outcomes named in the delegation ("Pass at both when serial -> contention artifact
of the `-n 6` parallel pass"). The `reset_bound_var_counter()` fix from this branch did **not**
cause these failures. They are unmasked/unlucky timing under the gating suite's own `-n 6`
parallel pass-1 concurrency, the same class of contention `oracle/run-oracle-suite.sh`'s own
docstring already documents as the reason other tests are marked `xdist_serial`.

Per the delegation's explicit instruction for this outcome: **the fix is NOT to widen any
budget**, and none was widened. No code change was made or needed for this finding.

**Caveat on machine quietness**: the delegation described the machine as quiet (load ~4.6); at
measurement time load average was 5.16-6.67, and other agents (`main`, `impl-140-c1`) were
concurrently active in this same session. The two runs (59.55s vs 31.07s for the identical 3
tests) show real variance consistent with that background contention, though not enough to flip
either run's pass/fail outcome. This is noted for completeness, not as a caveat on the
pass/pass conclusion itself, which does not depend on absolute timing.

## Secondary Finding: `test_mixed_and_box_next` Is a Genuine Tight-Budget Solve, Not (Solely) Noise

Ran `oracle/bimodal_logic/tests/test_oracle_interface.py::TestMixedFormulas::test_mixed_and_box_next`
serially in isolation at HEAD, twice, inside `nix develop` (note: this file imports
`bimodal_harness`, which requires the devShell's own `PYTHONPATH` -- `code/src:../BimodalHarness/src`
-- rather than a hand-set `PYTHONPATH=code/src` override, which caused a collection error on the
first attempt and was corrected before these runs):

```
Run 1: 1 passed in 44.16s
Run 2: 1 passed in 44.82s
```

Both runs pass comfortably under the 60000ms budget, but consume ~74-75% of it -- a stable,
near-deterministic solve time, not high-variance noise. This is the same headroom-starved profile
already diagnosed and fixed (before this session, task 139 commit `dd587065`) for the sibling test
`test_mixed_or_diamond_prev` in the same file/class: that test's genuine serial solve time also
sat close to its old budget once the bound-variable-naming/interning fix in that prior task made
solves genuinely slower (no longer artificially fast via accidental Z3 term-identity sharing), and
under `-n 6` contention it blew the budget; the documented fix there was
`timeout_ms: 60000 -> 150000` plus `@pytest.mark.xdist_serial`.

`test_mixed_and_box_next` was not touched by that prior fix and still carries `timeout_ms=60000`
with no `xdist_serial` marker. Its serial solve (~44-45s) is consistent with the same mechanism:
comfortably under budget alone, but with only ~25% headroom, plausibly insufficient once run
alongside 5 sibling workers in the gating suite's `-n 6` pass 1 -- which is exactly where its
recorded `OracleTimeoutError` occurred.

**This is reported, not fixed.** The applicable fix pattern (widen `timeout_ms` and/or add
`xdist_serial`, as already done for `test_mixed_or_diamond_prev`) is explicitly forbidden by this
session's hard constraints ("Raising max_time, timeout_ms, ORACLE_PASS*_TIMEOUT, or marking
anything xdist_serial ... to get green is forbidden. If the only available fix requires that,
report blocked with measurements instead."). No change was made to
`oracle/bimodal_logic/tests/test_oracle_interface.py`.

## Status of Item 4 / Step 6 of `verify-refactor.sh`

Step 6 (gating oracle suite) must continue to be described as RED. The BM_CM_4 finding is now
fully explained and requires no fix (contention artifact, confirmed innocent at both commits).
`test_mixed_and_box_next` remains an open, understood-but-unfixable-under-constraints risk: a
budget-adjacent genuine solve that is a strong candidate for the same
widen-timeout-plus-`xdist_serial` treatment already applied to its sibling, but that treatment is
out of scope for this session per the hard constraints. This is the one blocker carried forward.

## Plan Deviations

- None (no plan file exists for this task; work followed the delegation's stated priority order
  verbatim).

## Files Changed

- None. This dispatch was diagnostic only; no production or test code was modified.

## Verification Performed (all inside `nix develop`)

- 3 BM_CM_4 oracle tests, serial, HEAD (`71d437bd`): 3 passed in 59.55s.
- Same 3 tests, serial, pre-fix worktree (`29e1fdec`, `git worktree add --detach`, removed after
  use): 3 passed in 31.07s.
- `test_mixed_and_box_next`, serial, HEAD, x2: 1 passed in 44.16s; 1 passed in 44.82s.
