# Implementation Summary: Certifying Countermodel Architecture

- **Task**: 205 - certifying_countermodel_architecture
- **Status**: [COMPLETED]
- **Started**: 2026-09-27
- **Completed**: 2026-09-28
- **Effort**: ~8 hours across 8 phases
- **Dependencies**: None declared. Consumed (did not re-decide) task 197's certificate-wire hardening (landed): the checker returns `acceptance: entailment` with a bytewise-matching `echo`.
- **Artifacts**: plans/01_certifying-countermodel-architecture.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

This task owned three things: the output gate on reported countermodels (item 1), the checker's
runtime availability for users with no Lean toolchain (item 2), and the repositioning of the
existing test tiers as UNSAT-direction liveness/regression evidence (item 3). All eight plan
phases completed. A production-side checker resolver (`semantic/checker.py`) now gates every
reported countermodel behind a `verify` setting (`'off'`/`'auto'`/`'required'`), the test helper
(`tests/_lean_check.py`) was refactored onto that same resolver, a fresh measurement on a trimmed
checker binary confirmed the out-of-band opt-in artifact remains the right packaging route, and
seven documentation/test-module surfaces now state that the standing A2 test tiers are
UNSAT-direction evidence, never countermodel trust.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/semantic/checker.py` — new module: production
  checker resolver (`resolve_checker`), resolution order (`BIMODAL_CHECKER_BIN` → per-user cache
  → `BIMODAL_LOGIC_PATH` checkout, invoked directly), lazy bounded probe (memoized per process,
  5s timeout), the capability handshake (status/acceptance-vocabulary/echo validation), optional
  SHA-256 digest pinning, checkout-HEAD provenance capture, and `check_certificate` for real
  invocations (raising `ProtocolFailure` on an echo mismatch).
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py` — new, 24 tests covering
  resolution order, memoization, timeout handling, the capability handshake, digest pinning, and
  `check_certificate`.
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` — added `'verify'` to
  `DEFAULT_EXAMPLE_SETTINGS` (default `'auto'`), validated early. **Deliberately stored as
  `self.verify_mode`, not `self.verify`** — see Decisions below.
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` — wired the independent check into
  `BimodalStructure.__init__` immediately after the mandatory `recheck` guard; added the
  `_verification_label()` helper and rendered it in `print_certificate`/`print_evaluation`; the
  `'required'` withholding error.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` — new, 7
  tests covering all three output states, `'required'` withholding, `'off'` never invoking the
  checker, the overclaim guard, and (skipped cleanly without a checkout) the real-checker path.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` — existing tests made
  deterministic (`verify='off'` by default via the `_settings()` helper) plus two new tests for
  the 'off' and forced-unavailable 'auto' label states.
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` — rewritten to delegate the
  actual subprocess invocation to `semantic/checker.py`'s `_invoke`, now invoking the built binary
  directly rather than through `lake exe check_certificate`. Every exported name unchanged
  (verified: `__all__` identical to `git show HEAD:...`).
- Documentation: `docs/SETTINGS.md` (new `## Certificate Verification` section: the three values,
  the three output states in the code's own wording, availability path, digest pinning);
  `docs/ADEQUACY.md` (§7.4 addition on unchecked-is-not-a-validity-claim; §7.1's `f^3` → `O(back ×
  fwd)` correction in both places; §7.3 now leads with both grid sizes, records the per-candidate
  comparison, and carries the direction claim); `docs/USER_GUIDE.md` (cross-reference);
  `docs/A2_GAP.md` (§8 limit 3 recorded discharged; direction claim); `docs/SEARCH_COVERAGE.md`
  (§1 direction claim); `docs/TRUST_PIPELINE.md` (item-1 row tightened to "the only *independent*
  check" and marked done; item-2 row extended with Phase 6's measured decision; new structural-
  conformance-check follow-on row; direction claim on "The standing test for A2"); `tests/README.md`
  (`test_certificate_a2_triangle.py` row); two test-module docstrings (`test_certificate_a2_triangle.py`,
  `test_search_period_coverage.py`).

## Decisions

- **`self.verify_mode`, not `self.verify` (load-bearing, not stylistic).** `models/semantic.py`'s
  `initialize_with_state` and `iterate/models.py`'s generic model-rebuild path both use
  `hasattr(semantics, 'verify')` as the theory-capability test distinguishing a verify/falsify
  theory (logos, exclusion) from one that is not (bimodal, which uses `truth_condition`). Setting
  `self.verify` to a string flips that check to `True` and crashes the live iterator (`'str'
  object is not callable`) — caught by `test_iterate.py::TestLiveIteration` during Phase 3's
  full-suite verification. The settings *key* stays `'verify'` throughout (matching the plan and
  `docs/SETTINGS.md`); only the resolved attribute's name differs.
- **Direct binary invocation flows into the test differential tier too (F5's side effect).**
  Delegating `tests/_lean_check.py`'s invocation to `semantic/checker.py`'s `_invoke` means the
  differential test suite now also invokes the built binary directly rather than through `lake
  exe`. Measured: the three consuming modules' real-checker runs dropped from ~2.2s/call to
  0.01s–0.3s/call — a substantial, unplanned but welcome speed-up, confirmed live during Phase 4.
- **Item 2's packaging route stands as recommended in Phases 1–5, now on a fresh measurement.**
  Phase 6 rebuilt `check_certificate` with `supportInterpreter = false`: gzip-9 dropped from
  ~65.9MiB to ~32.8MiB (roughly halved) but stayed in the tens of MiB, not single-digit. In-wheel
  shipping (Route A) is declined on this measured number; the out-of-band opt-in artifact (Route
  B — `BIMODAL_CHECKER_BIN` plus optional SHA-256 pinning, already built in Phases 1–2) remains
  the recommendation. The companion repository's lakefile flag and build artifact were both
  restored to baseline afterward (verified: `git diff` clean, rebuilt binary's byte count matches
  baseline exactly).
- **A2_GAP.md §8 limit 3 and the A2-triangle test's leg (i)/(iii) comparison are already
  per-candidate**, not merely aggregate — this was landed code the two ledger documents had not
  yet caught up to describing; both are now corrected to record it as discharged rather than
  open, per-candidate mechanism named precisely (`compile_and_bind`, `_run_exhaustive_triangle`'s
  first-divergence raise).

## Plan Deviations

- **Task 3.2** (add `verify` to `DEFAULT_EXAMPLE_SETTINGS`): altered — resolved attribute is
  `self.verify_mode`, not `self.verify`, to avoid the `hasattr(semantics, 'verify')` framework
  collision described above. Settings key unaffected.
- **Task 4.2** (rewrite `tests/_lean_check.py`): altered — `run_check_certificate_with_sent` now
  invokes the built binary directly via `semantic/checker.py`'s `_invoke`, per F5, rather than
  through `lake exe check_certificate`. Exported names and semantics unchanged; only the
  subprocess command underneath differs, and only in a way that makes the tests faster.
- **Task 8.1** (run the full project gate): altered — `code/tests/ci/test_timing_marker_coverage.py`
  caught `tests/unit/test_checker.py::test_probe_timeout_yields_unavailable_not_a_hang` reading a
  real `time.time()` and asserting a bound without a `performance`/`xdist_serial` marker. Fixed
  by adding `@pytest.mark.xdist_serial` (the taxonomy's "adequate headroom, contention-sensitive"
  classification, appropriate since the timed operation is monkeypatched to return instantly).

## Verification

- Build: N/A (no compiled artifacts in this repository; the companion Lean binary was rebuilt
  twice in Phase 6 and both builds succeeded — see Phase 6's own commands).
- Tests:
  - `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py -v` — 24 passed.
  - `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py -v` — 7 passed (including the real-checker class, run live against the local BimodalLogic checkout).
  - `BIMODAL_LOGIC_PATH=/nonexistent PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` — 612 passed, 17 skipped (checker unavailable; default `'auto'` never fails on absence).
  - `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` (real checkout available, run solo after an earlier parallel run produced one contention-induced flake that did not reproduce in isolation) — 629 passed.
  - `PYTHONPATH=code/src pytest code/tests/ -q` (whole-project gate) — 645 passed, 5 skipped, 2 warnings, after fixing the timing-marker gate.
  - Overclaim guard: no rendered output contains "kernel-checked proof" (asserted in
    `test_structure.py` and `test_output_gate.py`, and confirmed live via `dev_cli.py` against
    both the checked and unchecked states).
- Files verified: Yes — every new/modified file read back and its content confirmed against the
  live test runs and the `dev_cli.py` manual renderings quoted below.
- No test deleted, narrowed, or newly skipped (confirmed via `git diff --stat` across the whole
  task range and a line-by-line read of every test-file hunk); `_assert_exhaustive_triangle_agrees`
  unchanged.

### Manual verification transcripts (Phase 3)

```
$ BIMODAL_LOGIC_PATH=/nonexistent PYTHONPATH=src ./dev_cli.py .../bimodal/examples.py
  Verification: re-checked by this repository's own pure-Python decision procedures only
  (no independent checker available: environment absence: no checker candidate configured ...)

$ PYTHONPATH=src ./dev_cli.py .../bimodal/examples.py   # real checkout present
  Verification: independently checked -- Lean constructed a WitnessFamily.Refutes term for
  this certificate by applying a compile-time kernel-checked implication to four run-time
  decisions (acceptance: entailment, checkout 3e508e085c429b8e941dcc284a247fab0f2d3222)

$ verify='required', no checker -> ModelConstructionError:
  "A satisfying certificate was found, but 'verify': 'required' demands an independent check
  before reporting a countermodel, and no checker is available. ... Suggestion: Obtain a
  standalone checker binary -- see docs/SETTINGS.md's 'Certificate Verification' section ..."
```

### Phase 6's measured decision

| | Unstripped | Stripped | gzip -9 |
|---|---|---|---|
| Baseline (`supportInterpreter = true`) | 313,863,000 B | 219,351,032 B | 69,143,714 B (~65.9 MiB) |
| Trimmed (`supportInterpreter = false`) | 139,076,848 B | 91,420,336 B | 34,389,441 B (~32.8 MiB) |

Handshake on the trimmed binary: `status=countermodel`, `acceptance=entailment`, echo matched
bytewise, ~47ms. **Decision**: stays in the tens of MiB — out-of-band opt-in (Route B) remains
the recommendation; in-wheel shipping (Route A) is declined on this measured number, not merely
the untrimmed one. Companion repo restored: `lakefile.toml` diff clean, rebuilt binary matches
baseline byte count exactly.

## Impacts

- Every reported countermodel now carries an honest, source-grounded verification label; the
  previously-silent gap (a sampled test tier that clean-skipped in default CI, leaving no check on
  a candidate countermodel in a default run) is closed for users who configure a checker, and
  honestly labelled for those who do not.
- The differential test tier (three modules consuming `tests/_lean_check.py`) is now
  substantially faster (direct binary invocation vs. `lake exe`), an unplanned but valuable side
  effect of Phase 4's refactor.
- Four ledger/coverage documents plus three test-module/README surfaces now state plainly that
  the standing A2 tiers back the UNSAT direction, not countermodel trust — closing a
  mischaracterization risk this task's dispatch specifically named.
- `code/tests/ci/test_timing_marker_coverage.py` gained one more correctly-marked test; the
  project-wide invariant it enforces is unaffected in shape.

## Follow-ups

**Deferred findings for the certificate-wire hardening task** (per the dispatch's explicit
routing — not decided or edited here):

- **`ADEQUACY.md` §6.2 and `TRUST_PIPELINE.md`'s trust-base overclaim (F2).** Both documents
  describe an `acceptance: entailment` verdict as "a kernel-checked proof for that particular
  certificate" (`ADEQUACY.md` lines ~458 and ~490; `TRUST_PIPELINE.md`'s Stage 5 section, line
  ~162). Per `BimodalTools/CertificateImport.lean`'s `Acceptance` inductive docstring, that phrase
  describes the *reserved, not-yet-introduced* third `Acceptance` value (per-certificate kernel
  checking by re-elaboration) — nothing the binary produces today is that. The accurate narrower
  claim, already used throughout this task's own new code and docs: "Lean constructed a
  `WitnessFamily.Refutes` term for this certificate by applying a compile-time kernel-checked
  implication to four run-time decisions." This task's own gate label (`semantic/model.py`'s
  `_verification_label`) is written from the Lean docstring directly, never from §6.2's sentence,
  so the overclaim does not propagate into new user-facing text — but the two source documents
  still carry it and were explicitly out of scope to edit here (this task's own Non-Goals list).
- **Whether `BIMODAL_LOGIC_COMMIT` should track the companion repository automatically.** It is
  a dead pin (declared, exported, consumed by nothing) that has already drifted multiple times
  (`d55e2760` → `d1a24b30` → the companion repo's current HEAD, observed same-day in research and
  again during this task). This task demoted the *enforcement* mechanism to the capability
  handshake (Phase 2) and kept the commit as recorded provenance only (`checker.py`'s
  `CheckerHandle.provenance`, captured dynamically per resolution rather than read from this
  stale constant) — but `tests/_lean_check.py`'s own `BIMODAL_LOGIC_COMMIT` constant is
  unchanged, per Phase 4's "keep every exported name" constraint, and remains worth deciding
  whether to auto-track or retire.

**Incidental observations** (research surfaced, this task did not act on):

- **The companion repository now has a `translate_sentence` executable**
  (`[[lean_exe]] name = "translate_sentence", root = "BimodalTools.TranslateSentenceMain"`,
  confirmed present live in `~/Projects/BimodalLogic/lakefile.toml`), while this repository's
  `TRUST_PIPELINE.md` records the Lean-side half of translation (obligation S4) as deferred and
  not yet attempted. Worth a look by whoever owns S4's Lean-side half: an executable target may
  mean infrastructure already exists, even if the truth-preservation theorem itself does not.
- **The `lean-toolchain` pin question has resolved, not merely persisted.** Research recorded a
  divergence between the checkout's `lean-toolchain` pin (`v4.33.0-rc1`) and the toolchain that
  built the measured binaries (`4.27.0-rc1`). Re-checked live during this task's Phase 6: `elan
  show` reports `v4.27.0-rc1` as the *default* toolchain but `v4.33.0-rc1` as the *active* one
  (overridden by the checkout's own `lean-toolchain` file), and the freshly-rebuilt binary's own
  build trace confirms `v4.33.0-rc1` was actually used. The two now agree — the divergence
  research observed either does not hold today or was specific to a different measurement
  session; recorded here as a correction rather than repeated as still-open.

**Deferred, named so it is not rediscovered** (per the dispatch, not built here): a structural
conformance check that the emitted Z3 constraint set matches the (C1)-(C4) schema instantiated at
the configured bounds, extending `tests/_pinned_eval.py`'s `full_constraints` and
`tests/unit/test_pinned_eval.py`'s operator-inventory/atom-coverage guards, linear in formula
size rather than candidate space. Recorded as a new remaining-work row in `docs/TRUST_PIPELINE.md`
(item 3, Phase 7) — UNSAT-direction work, explicitly sequenced after items 1-2.

## References

- Plan: `specs/205_certifying_countermodel_architecture/plans/01_certifying-countermodel-architecture.md`
- Research: `specs/205_certifying_countermodel_architecture/reports/01_certifying-countermodel-architecture.md`
- Progress files: `specs/205_certifying_countermodel_architecture/progress/phase-{1..8}-progress.json`
