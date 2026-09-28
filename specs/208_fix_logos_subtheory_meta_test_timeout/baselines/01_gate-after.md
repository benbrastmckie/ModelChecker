# Baseline: full repository gate, after deletion

- **Date**: 2026-09-27 (host-local timestamps below are PDT), same host/session as
  `01_gate-before.md`.
- **Host-load caveat**: same shared, ambient-load host as the before-run. Sibling task 197
  committed further bimodal-certificate work between the before and after runs (see "Node-count
  reconciliation" below), so this is not a clean-room A/B — the decisive evidence is the node-id
  diff, not the raw wall-clock comparison.

## Invocation shape

Identical to `01_gate-before.md`'s (re-verified unchanged): `-m` expressions, `-n 4`,
`--timeout=300 --timeout-method=thread`, run from `code/` with `PYTHONPATH=src`.

## Node-count reconciliation (the actual defect-fix evidence)

Raw `--collect-only -q` totals moved from **3099/3237 selected** (before) to **3103/3241
selected** (after) — a net **+4**, not the naively-expected **-1**. This is fully explained by a
concurrent sibling commit, not by any defect in this deletion: a full sorted diff of both
collect-only node-id lists shows

- **Removed** (in before, absent from after): exactly one node —
  `logos/tests/integration/test_subtheory_orchestration.py::TestSubtheoryOrchestration::test_all_subtheory_tests_pass`
  — this task's own deletion target, and nothing else.
- **Added** (in after, absent from before): exactly five nodes, all under `bimodal/tests/`
  (`test_certificate_lean_agreement.py::TestProtocolFailureIsLoud::test_protocol_failure_is_none`
  and four `test_certificate.py::TestCanonicalWireBytes::*` nodes) — all attributable to sibling
  task 197's `ae3584d0` commit ("canonical wire bytes, in the protocol module"), landed on this
  shared tree between the two collect-only runs.

Net: `3099 - 1 + 5 = 3103`, matching the observed after-count exactly. **This task's own change
is the clean, isolated -1 the plan requires**; the sibling's unrelated +5 is additive noise from
the declared concurrent-dispatch cycle, not a coverage regression from this deletion.

## Parallel pass result

`3102 passed, 1 skipped, 5 warnings in 251.45s (0:04:11)` — wall time **251.45s (4m12.011s per
`time`)**, **0 failed**.

- `test_all_subtheory_tests_pass` no longer appears anywhere in the run (absent from output and
  from the slowest-durations list, as expected after deletion).
- Slowest 10 durations no longer contain any item attributable to this task's deletion target;
  the slowest item is unrelated bimodal certificate work
  (`test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2`, 142.88s, comfortably under the 300s
  ceiling).
- The before-run's one failure
  (`bimodal/tests/integration/test_iterate.py::TestLiveIteration::test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`)
  is **not present** in this run — it passed. This is consistent with `01_gate-before.md`'s
  attribution of that failure to transient contention from a concurrent sibling's mid-edit state
  at the time of the before-run, now resolved (task 197 has since committed). **No newly failing
  node appears in the after-run that was not already failing in the before-run** — the Phase 4
  stop condition (a newly-failing node outside this deletion) does not trigger; if anything, the
  after-run has strictly fewer failures than the before-run.
- Skipped count differs (15 before vs. 1 after). This is not attributable to this deletion (which
  touched only `logos/tests/integration/test_subtheory_orchestration.py`, which contained no
  skip markers before or after); it is plausibly tied to sibling task 197's `_lean_check.py`
  changes affecting Lean-availability skip conditions in `bimodal`, out of scope for this task to
  investigate further.

## Serial pass result

`9 passed, 3236 deselected in 3.79s` — wall time 4.837s (`time`). No failures, matching the
before-run's shape (9 passed, no failures); deselected count moved from 3232 to 3236, consistent
with the same net +4 node-count change described above.

## Verification against Phase 4's stop condition

- Selected-node count delta from this task's own change alone: **exactly -1** (the meta-test
  node), isolated from the sibling's unrelated +5 by the node-id diff above.
- No node newly fails in the after-run that did not already fail in the before-run.
- No timeout value, marker expression, or workflow file was changed (confirmed unchanged from
  Phase 1's re-read).
- The one assertion dropped by this deletion — "each subtheory's nested pytest invocation returns
  0" — is safe to drop because (a) the same 418 subtheory tests are collected and run directly by
  this same gate (spot-checked: the four subtheory `tests/` directories remain fully present in
  the after-run's collect-only output), and (b) the only additional property re-execution could
  have guarded, cross-subtheory operator-conflict freedom, is already asserted in-process by
  `test_no_operator_conflicts` and `test_dependency_resolution`, both still passing.

## Wall-time comparison (informational; not the decisive evidence per the risk table)

| Pass | Before | After |
|------|--------|-------|
| Parallel | 334.27s (5m34.849s) | 251.45s (4m12.011s) |
| Serial | 4.08s (5.626s) | 3.79s (4.837s) |

The ~83s parallel-pass reduction is directionally consistent with removing a 162.94s-320.90s
serial item that contended with the other three xdist workers, but is not offered as a precise
measurement given the ambient host load and the sibling's concurrent commits between runs.

## Files

- Raw log: `baselines/01_gate-after.log`
