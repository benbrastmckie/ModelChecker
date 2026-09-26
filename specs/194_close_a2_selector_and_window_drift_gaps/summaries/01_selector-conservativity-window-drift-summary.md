# Implementation Summary: Close the A2 selector and window-drift gaps

- **Task**: 194 - Close the two residual encoder-versus-specification gaps in the A2
  encoding-completeness argument
- **Status**: [COMPLETED]
- **Started**: 2026-09-26T00:00:00Z
- **Completed**: 2026-09-26T00:00:00Z
- **Effort**: ~4.5 hours (matches plan estimate)
- **Dependencies**: None
- **Artifacts**: plans/01_selector-conservativity-window-drift.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Closed both residual encoder-versus-specification gaps named in the A2 encoding-completeness
argument: the one-hot target selector's conservativity (structure decision D5 introduces that
conditions (C1)-(C4) do not themselves contain) and `WitnessRegistry.target_window()`'s
independent definition (the last window bound not shared by import with `certificate.py`'s
re-checker). Both are now discharged: the window is shared by construction, and the selector's
conservativity is argued in `docs/ADEQUACY.md` section 7.3 and pinned by a direct unit test
against the re-checker's own `_target_holds`.

## What Changed

- `semantic/witness_registry.py`: `target_window()` now delegates to `certificate._box_window`
  (`return _box_window(self)`), replacing its own `range(-self.nb, self.nm + self.nf)` body; the
  method's docstring records why sharing is the technically correct outcome, not a convenience.
- `semantic/certificate.py`: the four-window-helpers comment block updated to state all four
  window helpers are now shared by import — none independently defined.
- `semantic/witness_constraints.py`: `sel`'s and `target_constraints`' docstrings extended with
  the conservativity argument; the module docstring's `registry.target_window()` mention updated
  to note it is now the shared `_box_window` definition.
- `tests/unit/test_witness_registry.py`: `TestTargetWindow` extended with a swept-range
  regression pinning `target_window() == _box_window(registry) == range(-back, mid+fwd)` across
  36 `(back, mid, fwd)` combinations (`back`/`fwd` in `1..3`, `mid` in `0..3`).
  `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py:200`
- `tests/unit/test_witness_constraints.py`: new `TestSelectorConservativity` class — four generic
  label-pattern generators (`none`/`one`/`several`/`all` satisfying positions), a shared
  `_build_selector_family`/`_assert_bits_from_family` helper pair (both sides derived from one
  `LabelledLasso`, never hand-duplicated), an aggregate-satisfiability test, a per-position
  `push`/`pop` selectability test, a deliberate-mismatch vacuity guard, and a solver-free
  periodicity-corollary test — parametrized across `back=2,mid=1,fwd=2` and `back=mid=fwd=1`.
  `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py:175`
- `docs/ADEQUACY.md` section 7.3: new paragraph recording the selector-conservativity argument
  (lossless Skolemization of (C4)'s existential target time) and naming
  `TestSelectorConservativity` as its deciding test.
- `docs/TRUST_PIPELINE.md`: Stage-2 "What is nonetheless known about the encoder" paragraph
  updated from "three of the four window bounds" to all four, and the "Two gaps remain" sentence
  replaced with the closed state; the "What remains" table's "Selector conservativity, and the
  last unshared window" row removed (both halves discharged), leaving the separate "Widen the A2
  grid to `nb = nf = 2`" row untouched (explicit non-goal here, tracked by a sibling task).

## Decisions

- Followed the plan's adopted recommendation verbatim: share one `target_window()` definition
  (delegation, not merely an assert-agreement test) *and* keep the swept-range regression as a
  supplementary mechanical backstop, not a replacement for the delegation.
- The selector-conservativity test computes every expected verdict via
  `certificate._target_holds` on a hand-built `WitnessFamily`, never via an inline
  re-implementation of premise/conclusion membership — directly closing the weakness (F2) named
  in the existing `TestTargetConstraints` tests.
- Label patterns for the four assignment kinds ("none"/"one"/"several"/"all" satisfying
  positions) were built as generic, length-parametrized generators rather than hand-written per
  configuration, so the same four kinds apply cleanly at both `back=2,mid=1,fwd=2` and
  `back=mid=fwd=1` (8 parametrized cases per test).

## Plan Deviations

- None (implementation followed plan).

## Impacts

- `WitnessRegistry.target_window()`'s public API (name, signature, `range` return type) is
  unchanged; only its body changed, and behavior is provably identical for every valid
  `(nb, nm, nf)` (confirmed both by the Phase 1 swept-range test and by the full suite runs
  below).
- No downstream consumer (`semantic/witness_constraints.py`, `semantic/core.py`,
  `semantic/symmetry.py`, `semantic/proposition.py`, `iterate.py`, or any test module) required
  changes — all call through the unchanged `registry.target_window()` interface (confirmed via
  `grep -rn "target_window"` across `bimodal/`).
- Trust-pipeline documentation (`docs/ADEQUACY.md`, `docs/TRUST_PIPELINE.md`) no longer names an
  open encoder-versus-specification gap in either the selector or the window; a future reader of
  those documents sees the closed state.

## Verification

- Phase 1: `test_witness_registry.py` — 46 passed (36-combination swept-range test plus the two
  pre-existing `TestTargetWindow` tests).
- Phase 2: directly affected unit modules (`test_witness_registry.py`,
  `test_witness_constraints.py`, `test_certificate.py`, `test_symmetry.py`) — 131 passed; full
  bimodal suite — 420 passed (includes the `slow`-marked A2-triangle cases; this repo's
  `addopts` does not deselect `slow` by default). Confirmed `target_window()`'s body is exactly
  `return _box_window(self)` (no arithmetic) and `range(-` no longer appears in
  `witness_registry.py`.
- Phase 3: `test_witness_constraints.py` — 40 passed, including the new
  `TestSelectorConservativity` class (16 parametrized aggregate/per-position cases, the
  deliberate-mismatch guard, and the periodicity-corollary test). The deliberate-mismatch guard
  was confirmed non-vacuous during development: an unflipped control run of the same assertions
  checks `sat`, versus `unsat` with the deliberate flip in the committed test.
- Phase 4: full `bimodal/tests/unit` suite — 375 passed (confirms no docstring edit crossed a
  string boundary). `grep` confirms no remaining "independently defined"/"unshared window"/"Two
  gaps remain" language anywhere in `bimodal/` (the only surviving hits are the new,
  closed-state statements this task and a sibling task's companion document introduced).
- Phase 5 (final gate):
  - Full bimodal suite: **441 passed, 0 failed, 0 errors** in 150.51s (the increase from 420 to
    441 reflects sibling tasks 192/193's concurrent, independent additions to this same shared
    working tree — not a behavioral change from this task).
  - Four-theory gate, parallel pass (`-n 4`, excluding `xdist_serial`/`packaging`/`performance`/
    `unstable`): **2944 passed, 1 skipped, 5 warnings**, 0 failed, in 255.60s.
  - Four-theory gate, serial pass (`xdist_serial`, excluding `packaging`/`unstable`): **9 passed,
    3074 deselected**, 0 failed, in 3.26s.
  - `dev_cli.py` bimodal examples: 25 of 53 examples active; all 13 `_CM_`-named examples
    reported "there is a countermodel" and all 12 `_TH_`-named examples reported "there is no
    countermodel" — every verdict matches its naming-encoded `expectation`, with no error or
    mismatch in the run log. The certificate-encoding path runs through `target_window()` in
    `extract_certificate`, so this exercises the Phase 2 delegation end to end.

## Follow-ups

- None required by this task. "Widen the A2 grid to `nb = nf = 2`" remains tracked separately in
  `docs/TRUST_PIPELINE.md`'s "What remains" table (an explicit non-goal of this task, addressed
  by a sibling task in the same cycle).

## References

- `specs/194_close_a2_selector_and_window_drift_gaps/plans/01_selector-conservativity-window-drift.md`
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py`
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md`
