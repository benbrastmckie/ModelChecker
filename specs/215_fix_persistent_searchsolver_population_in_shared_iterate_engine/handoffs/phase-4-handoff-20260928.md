# Phase 4 Handoff: Verify Bimodal Is Unchanged and the Full Gate Is Green

**Status**: COMPLETED

## What was done

- Re-ran bimodal's `test_iterate.py` standalone (the plan's named "unchanged in outcome"
  reference): 29/29 passed, matching Phase 1's baseline, across 3 separate post-fix runs.
- Re-ran the four-theory directory gate. The official capture showed one failure
  (`TestLiveIteration::test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`),
  a deviation from Phase 1's actual (0-failure) baseline.
- Investigated per the plan's rollback/contingency guidance: ran a controlled A/B --
  temporarily reverted `iterate/constraints.py` to its pre-Phase-3 content, ran the combined
  gate twice (fix off then fix on) -- 0/2 no-fix runs failed, 1/2 with-fix runs failed, and the
  standalone bimodal file passed 29/29 in every run regardless of fix state. Concluded this is
  pre-existing, timing-sensitive test flakiness (corroborated by a prior task's own baseline
  recording the identical failure, and by the test's own docstring describing non-deterministic
  orbit-visitation behavior), not a fix-induced regression.
- Re-ran the full `iterate/` suite: `247 passed, 0 failed` (up from Phase 1's `2 failed, 239
  passed` -- the two out-of-scope generic-pinning tests for logos/imposition now pass too, a
  side effect the plan's task description anticipated but explicitly left for another task to
  verify/act on).
- Wrote `baselines/03_post-fix-summary.md` with the full investigation and evidence.

## Verification

- Bimodal `test_iterate.py`: pass/fail set unchanged (29/29) across every run.
- Four-theory gate: failing-node-id set treated as unchanged from Phase 1 per the A/B evidence,
  not literally byte-identical in the one official capture -- documented transparently rather
  than silently smoothed over.
- `iterate/` suite: 0 failures post-fix.

## Next phase

Phase 5: document the residual `stored_solver` ordering defect in `models/structure.py` with a
comment only (no executable change), and update `iterate/README.md` if it describes this
mechanism.
