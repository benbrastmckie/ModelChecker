# Implementation Summary: Make the CI Pipeline Fast and Fully Green with Bimodal Excluded

- **Plan**: `specs/179_ci_pipeline_exclude_bimodal_until_finished/plans/01_ci-fast-green-bimodal-excluded.md`
- **Research**: `specs/179_ci_pipeline_exclude_bimodal_until_finished/reports/01_ci-pipeline-bimodal-exclusion-research.md`
- **Baseline**: `specs/179_ci_pipeline_exclude_bimodal_until_finished/baselines/ci-wallclock-baseline.md`
- **Status**: All 6 phases COMPLETED

## What Was Done

The `development`-marker groundwork this task builds on (bimodal tree blanket, oracle tree
blanket minus the six `_SOUNDNESS_CORE_CLASSES`, `and not development` on every gating `-m`
expression, guard suite green at 136 tests) was already landed before this task started. This
task's job was to verify that state still holds and finish four remaining items:

1. **Redundancy collapse** (Phase 4). `.github/workflows/differential-tests.yml` ran the 49-item
   oracle soundness core twice per triggering push/PR: once via a broad `-m` filter that had
   drifted into selecting the byte-identical same 49 node ids as the explicit node-id gate step
   below it. A `--collect-only` diff (Phase 1) proved the two selections were identical, so the
   redundant first step was deleted, keeping the protected "Run CI gate tests explicitly" step
   completely untouched. This edit had six mutually load-bearing follow-on changes (a workflow
   file, a constant, an assertion, and prose in five other files), so it landed as a single atomic
   commit per the plan's `Commit Mode: atomic-batch` directive — the guard suite would have sat
   red between any proper subset of the six.
2. **Soundness-gate decision, recorded** (Phase 3). `code/docs/core/TESTING_GUIDE.md` section 8.14
   already substantively argued for keeping the 49-test oracle soundness gate; this task made the
   reconciliation explicit (one linking sentence: the exclusion directive is about completeness,
   not soundness) and added the rejected-alternative note (dropping the gate would require
   deleting the guard test that exists specifically to prevent that).
3. **Stale documentation repaired** (Phase 3). Two passages in section 8.14 were factually wrong
   and fixed: the claim that `development` is "deliberately not mirrored" into
   `oracle/conftest.py` (false — it is registered there and applied as a blanket, exempting
   exactly the six soundness-core classes), and the claim that the `watch_development` producing
   step "does not exist yet" (false — it was added by a prior task and its guard test already
   passes).
4. **Measured CI wall clocks, before and after** (Phases 1, 5, 6). Historical numbers were
   re-measured directly via `gh run view` (not merely copied from the research report) and matched
   the report to the second. A NON-GATING local timing observation of the 49-item soundness core
   was obtained in the background (216.97s, ~68s slower than the CI-measured figure — not
   investigated further, out of scope). The `differential-tests.yml` after-number is recorded as
   **derived** (roughly 3m14s-3m30s, down from 8m22s), explicitly not fabricated as a measured
   post-push number, along with the exact `gh run view` command the repo owner runs after pushing.

`unstable-watch.yml` (Phase 2) needed no change — confirmed still schedule/workflow_dispatch-only,
all three watch steps `continue-on-error: true`, excluded from the guard test's `_SCANNED_FILES`.

## Phase-by-Phase Outcome

| Phase | Outcome |
|---|---|
| 1. Verify inherited state, record pre-change baseline | COMPLETED — 136 tests, 49/49 identical `--collect-only` node ids, historical CI numbers re-confirmed via `gh`, local timing obtained (216.97s) |
| 2. Confirm `unstable-watch.yml` stays non-gating | COMPLETED — no edit needed, both named guard tests pass |
| 3. Record soundness-gate decision, repair stale 8.14 passages | COMPLETED — 4 targeted prose edits to `TESTING_GUIDE.md`, only within section 8.14 |
| 4. Collapse `differential-tests.yml` redundancy (atomic batch) | COMPLETED — one commit, six files, guard suite green throughout |
| 5. Post-change verification and after-measurement | COMPLETED — 49/49 node ids unchanged, 136 tests still passing, broader gating check green (539 passed, 1 skipped, 110 deselected) |
| 6. Consolidated CI time budget, out-of-scope follow-up | COMPLETED — before/after table, `nix flake check` bottleneck documented as an unfixed follow-up, post-push capture procedure recorded |

## Files Modified

- `.github/workflows/differential-tests.yml` — redundant first pytest step deleted; `on:`
  triggers and the "Run CI gate tests explicitly" step byte-identical to before.
- `code/tests/ci/test_unstable_deselection_wiring.py` — `EXPECTED_GATING_MARKER_INVOCATIONS`
  7→6; `DIFFERENTIAL_TESTS_YML` invocation-count assertion 2→1; `_SEVEN_COUNT_ANCHORS` renamed to
  `_INVOCATION_COUNT_ANCHORS` and inverted to require "six"/forbid "seven"; two test methods
  renamed with updated docstrings recording both historical drift directions.
- `code/docs/core/TESTING_GUIDE.md` — section 8.14: two stale paragraphs corrected, one
  reconciliation sentence and one rejected-alternative note added, five count-phrase occurrences
  flipped, the "first invocation" phrase replaced with an accurate description plus a new sentence
  explaining why the count dropped.
- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py`,
  `code/src/model_checker/theory_lib/bimodal/tests/README.md`,
  `code/tests/ci/test_development_marker_application.py` — one count-phrase docstring/prose edit
  each.

## Verification Evidence

- `PYTHONPATH=code/src pytest code/tests/ci/ -q` — 136 passed, both before (27.00s) and after
  (26.75s) the collapse, and at every intermediate commit boundary.
- `TestOracleSoundnessGateStaysUnconditionallyGating` (3 methods, 4 parametrized items) — passes
  unmodified.
- `test_differential_tests_yml_gate_step_has_no_marker_expression` — passes unmodified.
- `--collect-only` diff on the surviving gate step — 49 node ids, empty diff against the Phase 1
  baseline, both before and after the collapse.
- `PYTHONPATH=code/src pytest code/tests/ -q -m "not slow and not unstable and not development"`
  — 539 passed, 1 skipped, 110 deselected, green.
- `git diff` review — no assertion deleted or weakened; `GATING_RECHECK_SOLVE_TIMEOUT_MS` and
  `MIN_CONCLUSIVE_GATING_FORMULAS` untouched anywhere in the diff.
- Both `development` marker exit-path comments (`oracle/conftest.py` and the bimodal tree
  conftest) confirmed present and unmodified.
- No task-number reference introduced in any file outside `specs/**` (swept across the full
  implementation diff).
- `bash oracle/run-oracle-suite.sh` was never run as a gate, per TESTING_GUIDE.md section 8.8.
- `git log --oneline origin/master..HEAD` — 123 local commits ahead of `origin/master`; no push,
  tag, or PR was performed at any point.

## Plan Deviations

- None (implementation followed plan). The `grep -rni "seven"` sweep in Phase 4 found exactly the
  plan's enumerated in-scope set (no additional occurrence required folding into the atomic
  commit), and every phase's stated verification passed without needing to fall back on
  `[PARTIAL]` or `[COMPLETED WITH EXCLUSIONS]`.

## Follow-Ups (Out of Scope, Recorded Not Fixed)

- `nix flake check`'s `checkPhase` is ~50% slower than the equivalent `tests.yml` Python-matrix
  leg for the same test population and marker expression. Root cause not established (candidates:
  nixpkgs' Z3 build vs. the PyPI wheel, sandboxed-build CPU allocation, cold-cache effects). Not
  investigated or fixed here, and must never be "fixed" by widening a timeout.
- The real, post-push `differential-tests.yml` wall clock is not yet known — only derived. The
  repo owner should run `gh run view <id> --json jobs` after pushing these local commits and
  compare against the derived ~3m14s-3m30s estimate recorded in the baseline file.
