# Implementation Summary: `-n 4` Worker-Count Verification on Real CI

- **Task**: 171 - Verify xdist worker count on real ci
- **Status**: [COMPLETED]
- **Started**: 2026-08-26T17:36:00Z
- **Completed**: 2026-08-26T18:40:00Z
- **Effort**: ~1 hour (observation, log analysis, two follow-on fixes)
- **Dependencies**: None
- **Artifacts**: reports/01_verify-xdist-worker-count-ci.md (with addendum)
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, pr-prohibition.md

## Overview

All four "WHAT TO DO" items are discharged against real CI, and the Python-3.12 worker-crash
telemetry item collected its first real-CI reading. The task's own root-cause item (item D) was
explicitly NOT closed, per its own instruction — and the evidence that arrived during this task
made that instruction load-bearing rather than precautionary.

## What Changed

- `specs/171_.../reports/01_verify-xdist-worker-count-ci.md` — the verification record, plus a
  correcting addendum written after run `32996446859` falsified one of its conclusions.
- `.github/workflows/tests.yml` — peak-RSS sampler ungated from the 3.12 matrix leg
  (commit `d0f4f7ab`).
- `code/tests/ci/test_worker_rss_sampler.py` — added `TestSamplerIsNotMatrixGated` (2 tests,
  written RED against the live gate) so the sampler cannot be silently re-gated.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` — timeout/unsat
  discriminator plus `TestSkipIfSolverTimedOut` (commit `75012389`); see below.

## Findings

**(1)(2)(3) discharged.** Run `32995122897` on `cf60b1c8` (which carries `-n 4`) went green on
all four jobs. No example flipped: 2089 passed / 255 skipped on all three Pythons against the
`-n 6` baseline's 2043/255, with the +46 delta verified as 55 newly added test functions
(0 removed), not behavior change. `-n 4` averaged 202.4s against `-n 6`'s 204.5s — marginally
*faster*, a better result than the local screen's predicted ~5% slowdown. Worst job used under a
third of `timeout-minutes: 20`.

**(4) revert trigger did not fire.** No flip, no timeout. `-n 4` stands in both files;
`timeout-minutes` was not widened.

**Telemetry collected.** First real-CI RSS reading: aggregate peak 4.14 GiB of 16 GB (~26%),
with one worker at 3.59 GiB against siblings at 226/269/380 MB — a ~10x asymmetry, and the
single most concrete lead item D has produced.

## Decisions

- **Item D left OPEN**, as the task requires. The crash's non-recurrence on `32995122897` was
  briefly consistent with the memory-ceiling hypothesis; run `32996446859` then reproduced it on
  **Python 3.11**, which weakens both leading hypotheses at once (not 3.12-specific, and `-n 4`
  gives *more* headroom yet still crashed).
- **Sampler ungated rather than left 3.12-scoped.** Its gate rested on "the only leg the crash
  has been observed on", now false. Gated telemetry cannot observe a failure whose leg
  distribution is the open question.
- **The `test_iterate` failure was fixed at the root, not quarantined.** A Z3 `UNKNOWN` sets
  `timeout=True, z3_model_status=False` while a genuine unsat sets `timeout=False,
  z3_model_status=False`; asserting on `z3_model_status` alone cannot distinguish them. Fixed at
  both real-solve sites. `unstable` was deliberately not used — TESTING_GUIDE.md 8.9 reserves it
  for instability that survives a repair attempt, and this did not survive one.

## Plan Deviations

No plan was written for this task (it ran research -> observation -> targeted fix). Two fixes
were made that the original description did not anticipate, both prompted by evidence that
arrived mid-task: the sampler ungating and the timeout discriminator.

## Impacts

- `-n 4` is verified on real CI hardware and stays.
- The sampler now collects on all three legs, so the next crash produces data instead of log
  archaeology.
- The bimodal iterate tests will now *skip* rather than fail under contention. This is correct,
  but means they stop providing coverage on exactly the loaded runs where coverage matters most;
  making the bimodal `iterate` solve genuinely cheaper is the durable fix and is not in scope
  here.

## Follow-ups

- **Item D has no owning task** and is not this task's to close. The `[gw2] node down` crash now
  has three incidents across two Python versions with no root cause. A dedicated task carries it
  forward.
- Two consecutive runs on near-identical trees produced all-green and two-failures respectively.
  The failure *rate* is the signal; a single green Tests run is weak evidence.

## References

- `specs/171_verify_xdist_worker_count_on_real_ci/reports/01_verify-xdist-worker-count-ci.md`
- CI runs `32995122897` (green, `-n 4`), `32915763636` (`-n 6` baseline), `32996446859` (crash
  recurrence on 3.11), `32995122906` (differential oracle green via `unstable` deselection)
- Commits `d0f4f7ab` (sampler ungating), `75012389` (timeout discriminator), `812317c1` (report
  correction)
