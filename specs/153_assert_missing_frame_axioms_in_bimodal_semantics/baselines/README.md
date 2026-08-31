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
  already includes Seriality/Interpolation (Phase 4 edits `core.py` directly).
- `with_new_axioms` -- a script-local, self-contained reconstruction of `build_frame_constraints`
  that inlines the Skolemized Seriality/Interpolation constraints (report Section 2.1/3.1),
  independent of whether `core.py` has been changed. Used post-Phase-4 as both the Phase 7 "after"
  run and a cross-check that the inline reconstruction matches the real, committed implementation.

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

See the "Phase 7" section appended below once the post-change run is complete.
