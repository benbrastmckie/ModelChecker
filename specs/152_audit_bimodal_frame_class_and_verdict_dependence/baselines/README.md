# Bimodal Abundance-Removal Baseline

This directory is the regression net the two follow-on frame-axiom tasks (asserting Seriality and
Interpolation, and the extension-certified search that depends on them) must diff against before
landing any change to `BimodalSemantics.build_frame_constraints`. It exists because narrowing the
frame class can legitimately flip some verdicts, and neither follow-on task can tell "legitimate
narrowing" from "genuine regression" without knowing, in advance, which of the 52 canonical
examples' verdicts actually depend on the `capped_skolem_abundance_constraint`/
`depth_bounded_skolem_abundance_constraint` shift-closure approximation.

## What the baseline measures

For every example in `unit_tests` (`bimodal/examples.py`'s `countermodel_examples ∪
theorem_examples`, aliased as `test_example_range`, 52 examples), the model checker is run twice,
in-process, via `model_checker.utils.testing.run_enhanced_test`, using `isolated_z3_context()` per
run:

1. **baseline** — unmodified `BimodalSemantics.build_frame_constraints`.
2. **no_abundance** — a process-local monkeypatched copy of `build_frame_constraints` with the
   abundance term dropped from the returned constraint list; every other constraint (world
   enumeration, convexity, interval, lawfulness, `nullity_identity`, `converse`, `forward_comp`,
   `world_uniqueness`) unchanged and in the same order.

The monkeypatch lives only in the throwaway script's process — **`core.py` on disk is never
edited**. If a verdict changes between the two runs (`z3_model_status` differs and neither side is
`inconclusive`), the example is *abundance-dependent*; the audit found exactly 4 of 52
(`BM_TH_1`–`BM_TH_4`).

## How to invoke it

From the repository root, with the project's standard `PYTHONPATH` (the script also hardcodes
`sys.path.insert` to the same location, so this is belt-and-suspenders):

```bash
# Full 52-example run (original baseline; ~105s total wall time under a quiet host —
# dominated by BM_TH_1/BM_TH_2's 30s-each timeout and BM_CM_4's ~18s baseline side).
PYTHONPATH=code/src python3 specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/01_abundance-removal-script.py

# Subset re-run: only the 4 abundance-dependent examples, with BM_TH_1/BM_TH_2's baseline
# side raised to a capped 90s (used by this audit's Phase 3; ~3 minutes total).
PYTHONPATH=code/src python3 specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/02_phase3-rerun-script.py
```

Both scripts write incrementally (so an interrupted run still leaves partial results) and print a
per-example transcript line as they go. Neither takes command-line arguments; to change which
examples run or which settings are overridden, edit the script directly (they are throwaway,
process-local, and never touch `core.py`).

## Comparison procedure for a follow-on task

A follow-on task that changes the frame class (adds Seriality/Interpolation, or anything else that
alters `build_frame_constraints`) must, before landing the change:

1. Re-run `01_abundance-removal-script.py` (or a copy adapted to also monkeypatch in the new
   constraint set) against the *new* `build_frame_constraints`, comparing against **this
   directory's recorded `baseline` side**, not against a fresh run of the old code.
2. Diff `check_result` (`match`/`mismatch`/`inconclusive`) and `z3_model_status` per example
   against `01_abundance-removal-verdicts.json`.
3. **Explain every flip individually — never absorb one silently.** A verdict flip after adding a
   genuine frame axiom is *not* automatically a regression: narrowing the frame class legitimately
   turns SAT into UNSAT for a formula whose earlier countermodel depended on the now-excluded
   relations. But an unexplained flip is exactly the failure mode this baseline exists to catch,
   so every flip goes in the follow-on task's summary with a stated reason, not a silent pass.

## The cells that matter

`BM_TH_1`, `BM_TH_2`, `BM_TH_3`, `BM_TH_4` are the **entire** abundance-dependent surface measured
by this baseline (out of all 52 canonical examples). These are the cells a follow-on task must
explain if their verdict changes. Every other example's verdict is decided by constraints the
abundance approximation does not touch and is **not informative** for distinguishing legitimate
frame-class narrowing from a genuine regression with respect to this particular constraint — a
flip in one of the other 48 signals a different kind of problem entirely (unrelated to abundance)
and should be investigated on its own terms.

Current state of the four cells (`01_abundance-removal-verdicts.json`, refreshed by this audit's
Phase 3 re-run, `rerun_20260831_phase3` field per example):

| Example | Baseline (with abundance) | No-abundance | Note |
|---|---|---|---|
| `BM_TH_1` | `inconclusive-at-90s` (timed out at both 30s and a capped 90s re-run) | SAT countermodel, `mismatch`, <0.2s | Dependence conclusion rests on the no-abundance side plus code-comment corroboration (`examples.py:1473`, `core.py:598`–`601`), not on the timeout itself |
| `BM_TH_2` | `inconclusive-at-90s` (same) | SAT countermodel, `mismatch`, <0.3s | Same basis, `examples.py:1474` |
| `BM_TH_3` | `match` (no countermodel), decided, reproduced twice | SAT countermodel, `mismatch`, decided, reproduced twice | Clean flip, both sides decided on every run so far |
| `BM_TH_4` | `match` (no countermodel), decided, reproduced twice | SAT countermodel, `mismatch`, decided, reproduced twice | Clean flip, both sides decided on every run so far |

## Known caveats

- **Pervasive interpretation error, not a verdict-affecting bug.** Every recorded run in
  `01_abundance-removal-verdicts.json` — all 52 examples, both sides — carries the same error
  string: `Interpretation error: BimodalProposition.truth_value_at() missing 1 required
  positional argument: 'eval_time'`. Verdicts are read off Z3's SAT/UNSAT status
  (`z3_model_status`/`check_result`), not off the interpretation step that raises this error, so
  the error does not affect any recorded verdict. It is out of this audit's non-goals scope to
  fix; a follow-on task should not be surprised by it appearing on every run, and should not treat
  its presence or absence as a signal of anything.
- **`BM_CM_1`'s documented timing flake (`pytest.mark.unstable`).** `test_bimodal.py:63`–`94`
  documents a heavy-tailed Z3 solve distribution for this example (median ~7–8s, draws up to
  47.78s decided, one undecided draw at 600s, a real CI failure at 60.94s against a 60s budget)
  with four strict entry criteria for the `unstable` marker and two exit criteria (20 consecutive
  clean unstable-watch runs, or a verified encoding fix across a >= 20-seed sweep). This audit's
  baseline runs (7.66s and 7.67s across two sessions) are each one more data point at a recorded
  host condition, not a re-adjudication — see `test_bimodal.py:44`–`95` for the full policy.
- **`TN_CM_2`'s separately-documented timeout.** `test_bimodal.py:46` notes its countermodel
  search "times out even at 15s"; this baseline used a 10s `max_time` for it and recorded
  `inconclusive` on the baseline side while the no-abundance side found the expected countermodel
  in 0.06s — a solver-speed effect, not a verdict dependency (the countermodel is expected on both
  sides).
- **`MF_MODAL_FUTURE_TH` and `BM_TH_5` are already-known non-theorems, not regressions.**
  `MF_MODAL_FUTURE_TH` (`\Box A -> \Box \Future A`) is documented at `test_bimodal.py:35`–`37` as
  not valid under current bimodal semantics; `BM_TH_5` (`\Box A -> \Future \Box A`, present in
  `examples.py`'s `example_range` but excluded from `unit_tests`/`test_example_range`) is likewise
  a known non-theorem. Both are `mismatch` (countermodel found) with abundance intact and remain
  `mismatch` without it — expected on both sides, not a flip to investigate.
- **A verdict flip is not automatically a regression** (repeated from the Comparison Procedure
  above because it is the single easiest mistake to make when reading a diff against this
  baseline): adding a genuine, missing frame axiom legitimately shrinks the frame class, which can
  turn a SAT (countermodel found) into an UNSAT (no countermodel, theorem holds) for a formula
  whose earlier countermodel depended on a relation the new axiom now excludes. The requirement is
  not "no flips" — it is "every flip is explained," per the Comparison Procedure above.

## Files in this directory

- `01_abundance-removal-script.py` — the original 52-example baseline script.
- `01_abundance-removal-verdicts.json` — raw per-example results; each of `BM_TH_1`–`BM_TH_4`
  additionally carries a `rerun_20260831_phase3` field with the capped-90s re-run results,
  preserved alongside the original values rather than overwriting them.
- `01_abundance-removal-run.log` — full run transcript, both the original run and the Phase 3
  re-run appended to it (gitignored by the project's `*.log` rule; present on disk, not tracked).
- `02_phase3-rerun-script.py` — the Phase 3 subset re-run script (4 examples, raised `max_time` on
  `BM_TH_1`/`BM_TH_2`'s baseline side only).
