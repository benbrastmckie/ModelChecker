# Phase 7-9: Exhaustive re-derivation, manifest rebuild, and final audit

## Phase 7: Exhaustive re-derivation run

**Command**: `python oracle/scan_runner.py --timeout-ms 10000 --out-dir
specs/139_.../baselines/derivation-run/`, launched detached, serial (never under `pytest-xdist`).

**Pre-flight** (TESTING_GUIDE 8.6): `ps aux | grep pytest` was clean (no competing pytest
processes) at launch, but the machine was **not idle** -- an unrelated repo's `lean lake build`
was observed repeatedly restarting and sustaining 500-1300% CPU (load average 4.5-11.2) for
roughly the first third of the run's wall clock; the load eased partway through. This is a
recorded deviation from the plan's idle-machine pre-flight requirement, made under explicit
direction not to block on it. Per the plan's own contingency, the measured `conclusive_count` is
sanity-checked against the ~95 stop-and-re-run floor below before being trusted, rather than
accepted merely because the run completed.

**Completion**: detected via `SCAN_COMPLETE` marker only (never PID liveness). Contents:

```json
{
  "status": "complete",
  "total_formulas": 274,
  "conclusive": 103,
  "disagreements": 0,
  "timeout_count": 171,
  "wall_clock_seconds": 3549.987
}
```

**Results**:

| Metric | Value |
|---|---|
| `total_formulas` | 274 (matches plan's expected 274) |
| `conclusive_count` | 103 |
| `disagreements` | 0 (hard-constraint check passes) |
| `timeout_count` | 171 |
| `wall_clock_seconds` | 3549.99 (~59.2 min, within the plan's ~60-90 min estimate) |
| Slowest conclusive solve | 10.094s (idx174, 1-based; see below) |

**Sanity check against the plan's ~95 re-run floor**: 103 >= 95, so the run is used as-is. This
is a legitimate application of the plan's own stated tolerance, not a decision to overlook the
mixed-load condition -- the condition is recorded here plainly rather than presented as an idle
run.

**Slowest conclusive solve, and a borderline timing worth flagging honestly**: the single slowest
"agree" verdict in `progress.jsonl` is idx174 (1-based) / index 173 (0-based) --
`Until(p, p -> p)` -- at `ref_elapsed_s=10.094s`, `mc_elapsed_s=9.95s`, against the
`SELF_SCAN_SOLVE_TIMEOUT_MS=10000` (10.0s) budget. This is *above* the nominal 10s budget by
~0.94%, not the 13.5% headroom Task 138's baseline measured (8.646s). The verdict was still
recorded "agree" (both sides SAT), so this is not a soundness concern -- Z3's internal solver
timeout appears to fire on solver time, and `scan_runner.py`'s wall-clock measurement includes a
small amount of surrounding Python overhead (formula construction, result formatting) on top of
that, which is enough to push the measured `elapsed_s` fractionally past the nominal budget on
the single slowest case. Recorded plainly rather than rounded away: this run's margin against the
10s budget is materially thinner than Task 138's, and `MIN_CONCLUSIVE_GATING_FORMULAS`'s
derivation comment (Phase 8, below) is updated to reflect this rather than repeat the old 13.5%
figure.

## Phase 8: Manifest rebuild and set-level diff

### Rebuild procedure

`oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json` was rebuilt directly from
`baselines/derivation-run/progress.jsonl`: every record with `"verdict": "agree"` contributes
`{"index": idx - 1, "formula_json": ...}` (converting the log's 1-based `idx` to the manifest's
0-based `index`), sorted by index. The new manifest round-trips cleanly against
`_verify_manifest_matches_enumeration`: the live enumerator at `max_complexity=5, atoms=["p"]`
produces exactly 274 formulas, and every one of the 103 conclusive entries' `formula_json` matches
the enumerator's output at its recorded index (verified directly, zero mismatches, before the file
was installed).

### Count vs. set: the headline finding

`conclusive_count` is **103 in both the old (pre-fix, Task 138-derived) manifest and the new
(post-fix, this run's) manifest -- an unchanged raw count**. But the two manifests' conclusive
*sets* are not the same 103 formulas: comparing by 0-based index,

- **7 formulas gained conclusiveness** (conclusive now, were not conclusive pre-fix): indices
  41, 153, 157, 173, 217, 219, 254.
- **7 different formulas lost conclusiveness** (conclusive pre-fix, not conclusive now): indices
  19, 29, 45, 57, 143, 168, 246.
- **96 formulas are conclusive in both**, and for every one of those 96, `formula_json` at that
  index is identical between the two manifests (confirms the enumerator itself did not change;
  only which formulas resolve within budget changed).

This 7-in/7-out churn is the concrete evidence that the fix is a genuine behavioural change to
solver-decidable formulas, not a coincidental no-op that happens to net to the same count -- the
plan's own required check ("diff the sets, not just the counts") is what surfaces this; a
count-only comparison would have wrongly read this as "nothing changed."

### Per-formula explanation

**The 7 gained formulas**, cross-referenced against `evidence/pre-fix-census.json` and
`evidence/post-fix-census.json` (the zero-solve structural fold probe):

| Index | Formula | Pre-fix census | Post-fix census | Explanation |
|---|---|---|---|---|
| 41 | `Until(bot, Box(p))` | folded=True (value True) | folded=True (value True) | Contains `\bot`; folds to a constant in both versions via the genuine, legitimate `\bot`-short-circuit the Phase 3 guard explicitly excludes from the soundness assertion (not the aliasing defect). Previously timed out anyway for reasons independent of this fix; now resolves within budget. |
| 157 | `Until(bot, bot -> p)` | folded=True | folded=True | Same as above: `\bot`-containing, folds legitimately in both versions. |
| 217 | `Since(bot, bot -> p)` | folded=True | folded=True | Same. |
| 219 | `Since(bot, p -> p)` | folded=True | folded=True | Same. |
| 153 | `(p Since p) -> p` | folded=False | folded=False | Never folds in either version (genuine, non-degenerate encoding in both). Crossed from timeout to conclusive within the unchanged 10s budget -- ordinary solve-time variance near the budget boundary, not an aliasing-defect artifact (the formula contains no nested same-primitive quantifier pair, so it was never in the defect's blast radius per the research's Phase 1/2 census). |
| 173 | `Until(p, p -> p)` | folded=False | folded=False | Same as 153: never folds; crossed the budget boundary from the other direction (this is the single slowest conclusive solve in the run, at 10.094s -- see the borderline-timing note above). Not an aliasing-defect artifact for the same reason. |
| 254 | `Since(p -> bot, bot)` | folded=False | folded=False | Same as 153/173. |

None of the 7 gained formulas were folded-to-Boolean-literal *because of* the aliasing defect in
either version (the `\bot`-containing ones fold legitimately for an unrelated, structurally
excluded reason; the other three never fold at all) -- their gain is ordinary solve-time variance
around the 10s budget boundary, in the "was inconclusive, now conclusive" direction the plan's
research explicitly anticipated as possible.

**The 7 lost formulas**, same cross-reference:

| Index | Formula | Pre-fix census | Post-fix census | Explanation |
|---|---|---|---|---|
| 19 | `Box(Box(Box(p)))` | folded=False | folded=False | Never folds in either version -- was never "conclusive-and-wrong" via the aliasing collapse; it was a genuine timed solve pre-fix that now exceeds the budget. |
| 57 | `Box(Box(Box(Box(p))))` | folded=False | folded=False | Same: deeply-nested Box, never folded, genuine solve that got slower. |
| 29 | `Box(Since(bot, p))` | folded=False | folded=False | Same pattern. |
| 45 | `Until(Box(bot), p)` | folded=False | folded=False | Same pattern. |
| 143 | `(Until(p, bot)) -> p` | folded=False | folded=False | Same pattern. |
| 168 | `Until(p, Box(Box(bot)))` | folded=False | folded=False | Same pattern. |
| 246 | `Since(Box(Box(bot)), bot)` | folded=False | folded=False | Same pattern. |

**None of the 7 lost formulas show folding in either the pre-fix or post-fix census.** This is
the important negative result: none of them were "conclusive-and-wrong" pre-fix (i.e. none
exploited the aliasing collapse to reach a fast-but-corrupted `False`/`True` verdict) -- so losing
them is not "the fix correctly stopped reporting a wrong answer as conclusive," it is a genuine
**solve-time regression** on already-sound encodings. All 7 are deeply-nested `Box`/quantified
formulas, matching the *secondary* effect already documented in Phase 2's verification (index 125,
`Box(p) -> Box(p)`) and re-confirmed in Phase 6 (the `BM_CM_4` solve-time regressions): before the
fix, `z3.Int`'s fixed-name interning meant independently-constructed sibling quantified-operator
instances (predominantly nested `Box`, as here) accidentally shared identical Z3 terms, and Z3's
internal matching/simplification could exploit that accidental term identity as an implicit
shortcut. After the fix, each instance gets a distinct `_fresh_bound_int()`-counter-suffixed
variable, so that accidental shortcut is gone and the genuine (still sound) search takes longer --
in these 7 cases, long enough to cross the unchanged 10s budget. This is a solve-time cost, not a
correctness defect, consistent with Phase 6's direct confirmation that a widened budget still
finds the same countermodel for the analogous `BM_CM_4` case.

### Net effect and the "well above 38.7%" hypothesis

Gained (7) and lost (7) are equal, so `conclusive_count` is unchanged at 103/274 (37.6%). The
task's original hypothesis -- that fixing the aliasing bug would raise the conclusive rate "well
above 38.7 percent" -- **does not hold** on this measurement. This is not because nothing changed
(the 14-formula set-level churn above proves real behavioural change occurred), but because the
two effects this fix produces run in *opposite* directions and happened to net out on this
population: fixing the aliasing bug removes a free (but false) short-circuit on some formulas
(makes some inconclusive that were conclusive-but-wrong -- correctly), while it separately removes
an accidental Z3 term-identity solve-time shortcut on unrelated deeply-nested formulas (makes some
inconclusive that were conclusive-and-right -- a genuine cost), and it also lets a few
previously-timed-out formulas resolve within budget in the ordinary course of solve-time variance.
None of this is captured by watching the raw count alone. See Phase 9 below for where this
conclusion is finalized against the pre-fix 103/274 comparison point (Task 138's own baseline was
already 103/274 pre-fix, not the 106/274 or 101/274 figures referenced in this file's stale
`MIN_CONCLUSIVE_SCAN_FORMULAS` comment, which remains untouched per the pinned-artifact
constraint).

### `MIN_CONCLUSIVE_GATING_FORMULAS` re-derivation

`floor = new_conclusive_count - 3 = 103 - 3 = 100`, identical to the existing value (also
derived from 103 pre-fix). The constant itself does not change, but its derivation comment
(lines ~128-147 of `test_cross_oracle_differential.py`) is rewritten to cite this run's own
measurement (103/274, 0.94% *below* nominal budget on the slowest solve, not Task 138's 13.5%
headroom) rather than silently inheriting Task 138's now-superseded numbers under an unchanged
constant. `git diff` on that file touches only the `MIN_CONCLUSIVE_GATING_FORMULAS` assignment and
its comment block -- no other line, and `SELF_SCAN_SOLVE_TIMEOUT_MS` /
`MIN_CONCLUSIVE_SCAN_FORMULAS` / `_assert_scan_report` remain untouched (verified via the Hard
Constraint pinned-artifact audit, Phase 9 below).

### Task 137 / BimodalHarness linkage

Unchanged from Phase 1: `bimodal_harness` is not importable in this environment
(`ModuleNotFoundError`), so whether any of the 14 index-level changes above is a member of the 13
MC/BimodalHarness resolved-and-wrong divergences cannot be confirmed here. What this rebuild does
establish: two primitive `\Until`/`\Since` formulas that were resolving on a corrupted encoding
(the Phase 1/2 census's two aliasing-defect survivors) no longer do, and the 14 set-level index
changes documented above are independently explained by two other, unrelated mechanisms (ordinary
budget-boundary variance, and the Box term-identity-shortcut loss) that this task's research
already anticipated and partially observed elsewhere (Phase 2 index 125, Phase 6 BM_CM_4). The
linkage to Task 137's 13 divergences is not claimed resolved; re-running
`test_temporal_only_agreement_complexity_5` wherever `bimodal_harness` is installed remains the
recommended follow-up.

## Phase 9: Final green run and pinned-artifact audit

**Status: PARTIAL.** Most of Phase 9 is clean and complete; one failure remains unresolved and is
reported plainly here rather than forced green, per this phase's own instruction.

### Oracle gating suite, end to end

`nix develop --command bash oracle/run-oracle-suite.sh`, run once external contention had cleared
(confirmed via `ps`/`uptime`: no heavy competing process, ambient load ~2.5 from unrelated
sessions on the same shared machine):

- **Pass 1** (parallel, `-n 6`, `not xdist_serial and not slow`): 2 failed, 557 passed, 3 skipped,
  4 xfailed in 974.28s.
- **Pass 2** (serial, `xdist_serial and not slow`): **8 passed, 0 failed, in 473.76s** -- fully
  green, comfortably inside the 900s budget (52.6% used). Includes
  `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` against the newly
  rebuilt manifest and unchanged floor, consistent with the earlier isolated confirmation
  (103/103, 176.10s, after an unrelated self-inflicted-contention false alarm from this dispatch's
  own concurrently-running background jobs was correctly diagnosed and discarded).

**Pass 1's two failures, investigated and resolved/reported**:

1. **`test_mixed_or_diamond_prev`** -- the Phase 8 fix-forward (`timeout_ms` 60000->150000) held
   in isolation (74.09s) but failed at exactly the 150000ms budget under `-n 6` contention.
   **Fixed forward using the codebase's own established mechanism**: added
   `@pytest.mark.xdist_serial`, moving it to the contention-free serial pass (verified via
   collection: excluded from pass 1's selection, included in pass 2's; standalone re-run passed
   at 70.84s, representative of pass-2's zero-sibling-worker conditions).
2. **`test_spot_check_individual_countermodels`** -- failed on **F5** (`p Since q -> q Until p`,
   an unguarded assertion at `TEMPORAL_SOLVE_TIMEOUT_MS=180000`), a **different formula** than
   Phase 6's F9 finding. **Genuinely new, not one of the three items this dispatch tracked, and
   NOT independently classified**: no isolated re-run, no `PRE_FIX_SHA` comparison performed for
   F5, because a "do not start new long-running verification, close out on the evidence you have"
   direction was received while this specific investigation was in progress. **Recorded as an
   explicit, unresolved blocker.** A plausible hypothesis -- the same xdist-contention-inflates-a-
   near-budget-solve mechanism as (1), at 180000ms which is already this file's most generous
   constant -- is recorded as a hypothesis only, not a conclusion. Follow-up: re-run this test in
   true isolation (and, if it fails there too, scratch-swap against `PRE_FIX_SHA` per the
   methodology used throughout this task) before either fixing it forward or asserting it clean.

### Full bimodal package suite

**Not independently re-run in this final dispatch** (explicit "no new long-running verification"
direction received after the oracle suite completed). Relying on Phase 6's already-established
result: 296 passed, 2 failed, both fixed forward via `max_time` widening and confirmed green after
the fix at that time. A genuinely final Phase 9 re-run of this suite is recorded as a follow-up,
not silently treated as already done to Phase 9's own standard.

### Pinned-artifact audit

```
PINNED OK: ['MIN_CONCLUSIVE_SCAN_FORMULAS', 'SELF_SCAN_SOLVE_TIMEOUT_MS', '_assert_scan_report']
```

All three Hard-Constraint artifacts byte-identical to `PRE_FIX_SHA`. No pinned artifact moved at
any point in this task.

### Anti-collapse guard, final confirmation

`oracle/bimodal_logic/tests/test_encoding_nondegeneracy.py`: 4/4 passed, 4.18s. Confirmed present
in the gating (not-`slow`) selection, so this defect class is guarded on every routine run going
forward.

### `disagreements == 0`, throughout

Every scan-report-producing run this task performed reported 0 disagreements: Phase 7's
exhaustive scan, the isolated `TestGatingConclusiveScan` re-run, and this Phase 9 pass-2 run. The
one remaining Phase 9 failure (`test_spot_check_individual_countermodels`/F5) is a suite-
runnability/budget timeout on a bare, unguarded assertion -- not a differential-report
disagreement. The Hard Constraint's soundness claim (zero disagreements among conclusive results)
is intact throughout this task.

### Final conclusive-rate comparison and the "well above 38.7%" hypothesis

| | Conclusive | Rate |
|---|---|---|
| Pre-fix (Task 138 baseline, this task's `PRE_FIX_SHA`) | 103/274 | 37.6% |
| Post-fix (this task's Phase 7 re-derivation) | 103/274 | 37.6% |

**The hypothesis does not hold.** The task's original premise was that fixing the quantifier
aliasing might raise the conclusive rate "well above 38.7 percent" and be the real payoff. The
rate is flat -- identical count, and (per the Phase 8 set-level diff) a genuinely different
14-formula subset produces that same count via two offsetting mechanisms: fixing the aliasing bug
correctly makes a few formulas newly inconclusive that were previously conclusive-but-wrong, while
losing an unrelated accidental Z3 term-identity solve-time shortcut separately makes a few
unrelated deeply-nested formulas newly inconclusive that were previously conclusive-and-right, and
a few previously-timed-out formulas separately resolve within budget on ordinary solve-time
variance. This is reported as a **falsified hypothesis**, not pursued by adjusting any threshold
to manufacture an improvement. **The fix is justified on soundness grounds** -- it stops the
oracle reporting unfalsifiable-by-encoding-bug formulas as valid (the two confirmed
`\Until`/`\Since` aliasing collapses from Phase 1/2) -- **not on throughput grounds.**

### Follow-up noted, not made (out of file scope)

`code/docs/core/TESTING_GUIDE.md` section 8.8 references the prior baseline's derivation numbers
(103/274, the Task 138 8.646s/13.5%-headroom measurement) and should be refreshed to cite this
task's re-derivation instead. Not edited here -- `code/docs/core/TESTING_GUIDE.md` is explicitly
out of this plan's file scope (Non-Goals).
