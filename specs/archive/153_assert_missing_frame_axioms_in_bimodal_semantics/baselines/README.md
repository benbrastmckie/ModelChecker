# Task 153 Regression Baselines

Harness: `01_frame-axiom-regression-script.py`, adapted from
`specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/01_abundance-removal-script.py`.
Invariants preserved from the 152 harness: in-process via
`model_checker.utils.testing.run_enhanced_test`, `isolated_z3_context()` per run, each example's
own `examples.py` settings, and `core.py` on disk is never edited by this script. Run from the
repo root with `PYTHONPATH=code/src`:

```
python3 specs/153_.../baselines/01_frame-axiom-regression-script.py baseline specs/153_.../baselines/01_pre-change-verdicts.json
python3 specs/153_.../baselines/01_frame-axiom-regression-script.py with_new_axioms specs/153_.../baselines/03_post-change-verdicts.json
```

Two arms:
- `baseline` -- whatever `BimodalSemantics.build_frame_constraints` currently is on disk,
  unmodified. Before Phase 4 lands, this is the pre-task-153 method. After Phase 4 lands, this
  already includes Seriality/Interpolation (Phase 4 edits `core.py` directly). **This is the arm
  Phase 7 actually used for its post-change run** -- see the correction note below.
- `with_new_axioms` -- a script-local, self-contained reconstruction of `build_frame_constraints`
  that inlines the Skolemized Seriality/Interpolation constraints (report Section 2.1/3.1) using
  fresh, differently-named Z3 symbols (`serial_succ_inline` etc.), independent of whether `core.py`
  has been changed. **Discovered during Phase 7 not to be a reliable cross-check**: on `BM_CM_4`
  this arm decided `match` in 4.56s while the real committed `build_seriality_constraint`/
  `build_interpolation_constraint` methods (same logical formulas, different Z3 symbol names/
  construction order) went `inconclusive` at 120s on the identical example -- Z3's MBQI/E-matching
  is sensitive enough to incidental symbol-naming/construction-order differences that a "structurally
  equivalent" reconstruction is not a safe stand-in once real regression-hunting is at stake. Left
  in the script for its original purpose (getting a same-shape "with new axioms" measurement before
  Phase 4 landed, where no such discrepancy is possible since there is no "real committed method" to
  diverge from yet) but **do not use it to characterize post-Phase-4 behavior** -- use `baseline`
  against the post-Phase-4 tree instead, as Phase 7 does.

## Phase 1: pre-change reference run

`01_pre-change-verdicts.json` -- full 52-example run (`countermodel_examples` union
`theorem_examples`, matching the 152 README's example count), `baseline` arm, current
(pre-Phase-4) tree. Confirms this task's own scope hypothesis: 52 examples, `core.py` untouched
(`git status --short` on `core.py` clean before and after).

**Diff against `specs/152_.../baselines/01_abundance-removal-verdicts.json`'s `baseline` side**:
0 divergences across all 52 examples (both `check_result` and `z3_model_status` compared
per-example). In particular:

| Example | check_result | z3_model_status | solving_time |
|---|---|---|---|
| `BM_TH_1` | `inconclusive` | `False` | 30.19s |
| `BM_TH_2` | `inconclusive` | `False` | 30.22s |
| `BM_TH_3` | `match` | `False` | 0.11s |
| `BM_TH_4` | `match` | `False` | 0.12s |

Matches the 152 baseline's recorded figures for the four abundance-dependent cells exactly (same
verdicts; timings within normal host variance). No host-level divergence to record.

## Phase 7: post-change run and flip accounting

`03_post-change-verdicts.json` -- full 52-example run, `baseline` arm (unmodified, real
committed `build_frame_constraints`; see the correction note above for why `with_new_axioms` is
not used here), post-Phase-4 tree. `core.py` is unmodified by this run (already committed by
Phase 4-6; `git status --short` on `core.py` clean before and after this script's execution).

**Diff procedure**: every key in `03_post-change-verdicts.json` compared against both
`01_pre-change-verdicts.json` (same-host "before") and
`specs/152_.../baselines/01_abundance-removal-verdicts.json`'s `baseline` side (the recorded
reference), on both `check_result` and `z3_model_status`.

**Result: 2 of 52 examples diverge from both references.** Every other key (50/52) is identical
across all three sources.

| Example | pre-153 / 152 baseline | post-change | Diagnosis |
|---|---|---|---|
| `BM_CM_4` | `match`, ~18-20s | `inconclusive`, 120.36s (hits its own `max_time=120`) | **Attributable cost regression.** See below. |
| `BM_CM_1` | `match`, ~7-9s | `inconclusive`, 60.23s (hits its own `max_time=60`) | **Attributable cost regression, with caveats.** See below. |

**Cells that matter, explicitly**:
- `BM_TH_3`/`BM_TH_4`: unchanged `match` (0.11s/0.04s) -- exactly as the research report's
  Skolemized-encoding benchmark predicted. No regression.
- `BM_TH_1`/`BM_TH_2`: unchanged `inconclusive` at ~30.3s in all three sources (pre-153: 30.19s/
  30.22s; 152 baseline: 30.16s/30.15s; post-change: 30.31s/30.31s). Per this task's own rule, an
  unchanged timeout here is **no signal** -- it neither confirms nor denies a regression, since
  the baseline was already saturating its budget before any of this task's constraints existed.
  Not re-adjudicated.
- `TN_CM_2`: unchanged `inconclusive` at 10.1s in all three sources (pre-153: 10.1s; 152 baseline:
  10.09s; post-change: 10.1s). Already inconclusive pre-change -- **not a new or affected
  example**, explicitly confirmed rather than assumed.
- `BM_CM_1`'s `unstable` marker and `BM_CM_4`'s own recalibration history (both documented in
  `code/src/model_checker/theory_lib/bimodal/examples.py`) are not re-adjudicated by this run;
  their pre-existing heavy-tail behavior is exactly why the finding below is stated carefully.

### BM_CM_4: the primary, best-evidenced finding

Four independent measurements against the real, committed `build_seriality_constraint`/
`build_interpolation_constraint` methods, all consistent:

| Measurement | Result |
|---|---|
| `pytest -k "BM_CM_4"` (isolated single-test run) | 120.78s wall, FAILED (timeout) |
| Direct `run_enhanced_test` call (isolated single-example) | 120.37s, `inconclusive` |
| Full 52-example Phase 7 suite run (this section) | 120.36s, `inconclusive` |
| Isolation probe, shorter 40s budget, real methods via `self.build_seriality_constraint()`/`self.build_interpolation_constraint()` | 40.21s, `inconclusive` |

Against a clean pre-change contrast: 4.07s decided `match` (pre-Phase-4 reconstruction via a
git-blob check of the Phase 3 commit) and 18.26s-20.29s decided `match` (152 baseline and this
task's own Phase 1 pre-change run). **Stated as an outcome, not a proven mechanism**: BM_CM_4
regresses from a clean, fast, decided countermodel to undecided-at-budget with both new axioms
present. This is a cost regression (`inconclusive`, never a decided `unsat`) -- the axioms have
not been shown to eliminate BM_CM_4's countermodel, only to make the search not finish within
`max_time=120s`.

Isolation (`bm_cm4_isolate.py`, real methods, 40s probe budget): neither axiom alone is
individually responsible -- `seriality_only` (9.27s) and `interpolation_only` (6.33s) both stay
decided `match`, modestly slower than `neither` (3.10s); only `both` (40.21s) goes
`inconclusive`. One mitigation was tried (an explicit Z3 pattern anchoring
`build_interpolation_constraint` to its premise's ground `task_rel` term, mirroring
`build_forward_comp_constraint`'s existing `MultiPattern` convention) and did not recover a
decided result (still `inconclusive` at 40s).

### BM_CM_1: a second affected example, with an important caveat

`BM_CM_1` shows the same before/after pattern (decided `match` pre-change, `inconclusive` at its
own `max_time=60` post-change) -- but its own isolation table (`bm_cm1_isolate.py`, real methods,
70s probe budget, since `BM_CM_1`'s own baseline is already slower than `BM_CM_4`'s) is
**non-monotonic and contradicts BM_CM_4's pattern**:

| Configuration | BM_CM_4 (40s probe) | BM_CM_1 (70s probe) |
|---|---|---|
| `neither` | `match`, 3.10s | `match`, 22.55s |
| `seriality_only` | `match`, 9.27s | `match`, 40.42s |
| `interpolation_only` | `match`, 6.33s | **`inconclusive`, 70.21s** |
| `both` | **`inconclusive`, 40.21s** | **`match`, 16.43s** |

For `BM_CM_1`, `interpolation_only` alone is the configuration that fails to decide, while `both`
decides *faster* than `neither`. This is not explainable by any additive or monotonic
per-axiom-cost model, and it directly contradicts a "the two axioms interact superlinearly, and
that interaction is what costs" reading of the `BM_CM_4` table -- if that were a general
mechanism, `BM_CM_1`'s `both` row should be the expensive one, not the cheapest.

**What this does and does not establish**:
- It does **not** establish that the new axioms interact superlinearly as a general mechanism.
  That hypothesis is contradicted by `BM_CM_1`'s own isolation table and must not be presented as
  settled. The most that can be said from a single-run-per-configuration isolation table is that
  Z3's solving cost here is highly sensitive to the exact constraint set and to incidental
  formula-construction details in ways that are not compositional or predictable from
  per-axiom-alone costs -- the same phenomenon already surfaced directly by the
  `with_new_axioms`-arm symbol-naming discrepancy documented above (`serial_succ` vs
  `serial_succ_inline` alone changed `BM_CM_4` from 120s-`inconclusive` to 4.56s-`match`).
- `BM_CM_1` is the pre-existing, documented-`unstable` example (median ~7-8s, historical draws to
  47.78s, per `examples.py`'s own comments) -- its `neither` baseline in this very isolation run
  (22.55s) is already well above its documented median, confirming it is inherently high-variance
  independent of anything this task changed. The `inconclusive` draw at `interpolation_only` is
  corroboration of that pre-existing variance pattern as much as it is evidence of an
  axiom-specific effect, and its `unstable` marker is not re-adjudicated by this run.
- Settling the actual mechanism (is there a real superlinear interaction, is this pure Z3 search
  variance, or both) would require repeated runs per configuration to characterize the variance
  distribution -- **beyond this task's budget**, and a legitimate item for a follow-on task.

### Summary

Both `BM_CM_4` and `BM_CM_1` go from decided to undecided-at-budget with the new axioms present.
`BM_CM_4` is the strong, reproducible, well-evidenced finding (four consistent measurements, no
contradicting data). `BM_CM_1` shows the same before/after direction but its isolation table
contradicts `BM_CM_4`'s in a way that rules out stating a single general mechanism; it is reported
as corroboration of high solver-cost variance under the new constraint set, not as independent
proof of the same cause. Per this task's plan, no axiom was dropped, no budget was raised, and no
example's `unstable` marker or expected verdict was adjusted to work around this — see the
implementation summary for the full blocker writeup and remedy options.
