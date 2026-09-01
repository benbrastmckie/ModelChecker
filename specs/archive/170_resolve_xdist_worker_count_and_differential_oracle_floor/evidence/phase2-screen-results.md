# Phase 2 falsification screen: results

**Command shape** (identical across all four draws, only `-n` varies):
```
taskset -c 0,1,2,3 pytest tests/ src/model_checker \
  -m "not packaging and not performance and not unstable and not xdist_serial" \
  -n {6|4} -q --timeout=300 --timeout-method=thread -rA
```
Run from `code/`, `PYTHONPATH=src` implied by pytest's own rootdir config. Collected 2324 items
(2323 collected as run + 1 skip) each draw, matching the plan's 2321-2446 estimate closely.

## Draws

| Draw | Outcome | Passed | Skipped | Failed | Wall clock |
|------|---------|--------|---------|--------|------------|
| `-n 6` draw 1 (= Phase 1's full-gate run) | all pass | 2323 | 1 | 0 | 240.63s |
| `-n 4` draw 1 | all pass | 2323 | 1 | 0 | 307.19s |
| `-n 6` draw 2 | all pass | 2323 | 1 | 0 | 280.14s |
| `-n 4` draw 2 | all pass | 2323 | 1 | 0 | 238.35s |

Outcome lists (sorted `PASSED`/`FAILED`/`ERROR` node ids) saved alongside this file:
`n6-draw1-outcomes.txt`, `n4-draw1-outcomes.txt`, `n6-draw2-outcomes.txt`, `n4-draw2-outcomes.txt`.

## Diffs

- **Cross-`-n` diff 1** (`n6-draw1-outcomes.txt` vs `n4-draw1-outcomes.txt`): `diff` exit 0 (empty).
- **Cross-`-n` diff 2** (`n6-draw2-outcomes.txt` vs `n4-draw2-outcomes.txt`): `diff` exit 0 (empty).
- **Within-`-n 6` diff** (`n6-draw1-outcomes.txt` vs `n6-draw2-outcomes.txt`): `diff` exit 0 (empty).
- **Within-`-n 4` diff** (`n4-draw1-outcomes.txt` vs `n4-draw2-outcomes.txt`): `diff` exit 0 (empty).

All four diffs are empty. Every one of 2323 executed node ids produced the identical outcome
across all four draws, both same-`-n` and cross-`-n`.

## Outcome classification

**CLEAN**: both cross-`-n` diffs empty AND both within-`-n` diffs empty. Per the plan's decision
rule, this is the branch that permits (but does not by itself require or safety-prove) changing
`-n 6` to `-n 4`.

## Wall-clock note for Phase 3's `timeout-minutes` question

The four draws do not show a clean monotone `-n 4` > `-n 6` ordering: `-n 4` draw 1 (307.19s) was
the slowest overall, but `-n 4` draw 2 (238.35s) was the fastest overall, faster than either `-n 6`
draw. Averages: `-n 6` = 260.4s (4.34 min), `-n 4` = 272.8s (4.55 min) -- a ~12s / ~4.7% difference
on this 4-core host, well inside the observed draw-to-draw variance (69s spread across all four
draws, largely attributable to host-level noise from the orchestrating session's own concurrent
polling activity, not a `-n`-value effect). This host's absolute wall clock is not a reliable
proxy for the `ubuntu-latest` CI runner's, so Phase 3 must not extrapolate a specific CI-side
`timeout-minutes` number from these seconds -- only the *qualitative* finding (no large,
systematic `-n 4` slowdown observed) transfers.

## Required evidence limitation (this screen falsifies, it does not prove safety)

`TESTING_GUIDE.md` section 8.13 already establishes that restricting the development host with
`taskset -c 0-3` and running the full gating selection at `-n 6` **passes cleanly (2292 passed)**
while the same selection **failed on real CI**. Core-count restriction on a development host does
not reproduce a per-core clock/IPC gap or a virtualized neighbour, and the oracle suite reached
the same conclusion independently in an unrelated investigation. A clean four-draw local screen
at `-n 4` therefore **cannot prove `-n 4` is safe on CI**. It can only **falsify** `-n 4` if a
node id had flipped outcome -- and none did. The residual risk that a CI-only contention class
still affects `-n 4` differently than `-n 6` is not addressed by this screen and must be recorded
as open in Phase 3's decision and in the shipped workflow comment.
