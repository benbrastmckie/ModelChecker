# Implementation Summary: Mark the Oracle Gating Scan `unstable` and Extend the Watch Classifier

- **Task**: 160 - Verify bimodal oracle budget and watch unstable marker
- **Plan**: `plans/01_unstable-marker-and-watch-classifier.md`
- **Status**: All 6 phases COMPLETED

## What Was Built

Phases 1-5 (committed prior to this dispatch) added `@pytest.mark.unstable` to
`TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` in
`oracle/bimodal_logic/tests/test_cross_oracle_differential.py` under the same four-criteria
entry-record convention `BM_CM_1` uses; extracted the `unstable-watch.yml` classifier into an
importable, unit-tested module (`.github/scripts/unstable_watch_classify.py` +
`code/tests/ci/test_unstable_watch_classifier.py`) with a dedicated gating-floor `TIMING`
signature branch (duration-independent, keyed on the floor-shortfall message with
`disagreements=0`), a laundering guard against a disagreements-carrying failure being
misclassified as `TIMING`, and an honesty-corrected promotion-streak calculation; and wired
`-m "... and not unstable"` into both of `oracle/run-oracle-suite.sh`'s passes so the oracle tree
is now in scope for the deselection contract the same way `code/` already was.

Phase 6 (this dispatch) brought `code/docs/core/TESTING_GUIDE.md` section 8.9 in line with that
work and ran the full verification gate set:

- **"Currently marked"** now carries two entries (`BM_CM_1` and the gating scan), each a
  one-line pointer to its own marker-site comment block — no duplication of the four-criteria
  text into the guide.
- **"Where the deselection is wired"** now names `oracle/run-oracle-suite.sh`'s two passes
  explicitly and states that the oracle tree entered scope only once it carried its first
  `unstable` marking (the `code/`-tree workflows never reach `oracle/`, so the script needed its
  own filter) — and points at `code/tests/ci/test_unstable_deselection_wiring.py` as the
  executable enforcement of the contract.
- A new **"The classifier lives in an importable module, not YAML"** paragraph records that a
  third `unstable` marking must extend `.github/scripts/unstable_watch_classify.py` (and its
  tests), not edit workflow YAML.
- A new **"Promotion-streak limitation"** paragraph records that the step-summary streak's
  historical component is `NEW`-sensitive only (a `TIMING`-style failure's job conclusion still
  reads as success in `gh run list`), making the reported streak an upper bound; exit-criterion
  evaluation for a test expected to fail `TIMING`-style with any regularity must be checked
  against the uploaded per-run `unstable-watch-record.jsonl` artifacts, not the step-summary
  number alone.
- 8.8's `TestGatingConclusiveScan` mention (the gating-vs-exhaustive split, `GATING_RECHECK_SOLVE_TIMEOUT_MS`
  value) was checked for staleness and found still accurate — no edit was needed there.

## Phase 6 Hard-Constraint Gate Result

`git diff e75f7513..HEAD` (plus the uncommitted `TESTING_GUIDE.md` working-tree diff) was
reviewed for every occurrence of `MIN_CONCLUSIVE_GATING_FORMULAS`, `GATING_RECHECK_SOLVE_TIMEOUT_MS`,
and `max_time`. All occurrences across all six phases are comment/docstring/prose additions
(entry-criteria records, characterization-test docstrings, plan-checklist text) — **none change a
value**. Confirmed against the live source:

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py:286`:
  `MIN_CONCLUSIVE_GATING_FORMULAS = 100` — unchanged.
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py:217`:
  `GATING_RECHECK_SOLVE_TIMEOUT_MS = 40000` — unchanged (last widened 20000 -> 40000 in a prior
  task, before this task's `e75f7513` baseline).
- No `max_time` value changed anywhere in the diff.

**One pre-existing, out-of-scope observation** (not a task 160 defect, noted for the record):
`code/scripts/verify-refactor.sh`'s `GUARD_CONSTANTS` array still pins
`GATING_RECHECK_SOLVE_TIMEOUT_MS=20000`, which is stale against the file's actual `40000` value.
That script was not touched by any phase of this task (`git log e75f7513..HEAD -- code/scripts/verify-refactor.sh`
is empty; its last commit predates `e75f7513`), so it is drift left over from the prior task that
widened the constant, not something this task introduced or is in scope to fix under Phase 6's
hard-constraint gate (which asks only whether *this task* touched the three named values).

## Marker-Site Record Confirmation

Both required records at the `test_cross_oracle_differential.py` marker-site comment block
(item 3) were confirmed present and correctly stated:

- **`xdist_serial` lead: CLOSED.** The comment states the test class has carried
  `@pytest.mark.xdist_serial` since 2026-08-06 — six days before either CI shortfall run — and
  that `differential-tests.yml`'s invocation uses no pytest-xdist `-n` flag at all, so
  sibling-worker contention was never live for either recorded shortfall run. Explicitly
  distinguished from the still-open, untestable shared-host noisy-neighbor hypothesis.
- **Seven timing-out formulas: identities UNRECOVERABLE from available CI artifacts.** The
  comment states `differential-tests.yml` has no `actions/upload-artifact` step, captured logs
  print only the aggregate `scan report: ...` line, and the call site passes none of
  `_generate_differential_report`'s `progress_path`/`heartbeat_every`/`artifact_dir`
  instrumentation — and correctly declines to assert a same-7 claim given the 7-vs-8 count
  difference across the two shortfall runs.

## Verification Gate Results

| Gate | Command | Result |
|---|---|---|
| 1 | `PYTHONPATH=code/src pytest code/tests/ci/ -v` | **PASS** — 35 passed in 1.62s |
| 2 | `cd code && PYTHONPATH=src pytest tests/ -q` | **PASS** — 522 passed, 5 skipped in 187.63s |
| 3 | `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -m "not slow and not differential and not unstable" -q` | **NARROWED** — see below |
| 4 | `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -m unstable --collect-only -q` | **PASS** — 1/629 collected (628 deselected), exactly one test (the newly-marked `TestGatingConclusiveScan` test) |

### Gate 3 narrowing — explicit record

The plan's literal Gate 3 command against the whole `oracle/bimodal_logic/tests/` directory
(619 collected tests after the `-m` deselection) was first attempted at its full scope, bounded
by `timeout 580` in the foreground: it did not complete within 580s and was killed (this matches
the behavior that caused the two prior dispatches' orphaned 13-minute and 3.4-minute background
processes — the directory-wide oracle run is genuinely slow, not hung).

Per this dispatch's process constraint, the gate was narrowed to the one file this task actually
modified in the oracle tree — `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`,
the file carrying the new `unstable` marker — run with the identical `-m` expression:

```
PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py \
  -m "not slow and not differential and not unstable" -q
```

Result: **PASS** — 62 passed, 10 deselected in 321.47s (0:05:21). This confirms both required
properties for the file this task touched: the suite runs green, and the newly-marked test is
among the deselected set (not attempted), matching the plan's stated intent for this gate. The
remaining ~13 other files in `oracle/bimodal_logic/tests/` were not additionally re-run under
Gate 3 in this dispatch (they were not modified by any phase of this task and their behavior is
unaffected by the marker/deselection change); the directory-wide collection count (619 selected,
10 deselected) was independently confirmed via a fast `--collect-only` pass with the same `-m`
expression, which completed in under a second and shows no anomaly in what gets deselected.

## Plan Deviations

- **Gate 3 scope**: narrowed from `oracle/bimodal_logic/tests/` (whole directory) to
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (the single file this task
  modified), after the full-directory run did not complete inside a 580s bounded foreground
  timeout. See "Gate 3 narrowing" above for the full justification and the collect-only
  cross-check that stands in for the untested remainder of the directory.
- No other deviations. All Phase 6 documentation tasks (8.9 "Currently marked", "Where the
  deselection is wired", promotion-streak limitation, classifier-location note, 8.8 staleness
  check) were completed exactly as scoped.
