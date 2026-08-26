# Implementation Plan: Mark the Oracle Gating Scan `unstable` and Extend the Watch Classifier

- **Task**: 160 - Verify bimodal oracle budget and watch unstable marker
- **Status**: [COMPLETED]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: `specs/160_verify_bimodal_oracle_budget_and_watch_unstable_marker/reports/01_gating-floor-unstable-marker-and-xdist-lead.md`
- **Artifacts**: plans/01_unstable-marker-and-watch-classifier.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Mark `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` (in
`oracle/bimodal_logic/tests/test_cross_oracle_differential.py`) with `@pytest.mark.unstable`
under TESTING_GUIDE.md section 8.9's four mandatory entry criteria, so the documented residual
CI shortfall stays observed by `.github/workflows/unstable-watch.yml` rather than silently
dropped or repeatedly re-litigated. The marker alone is insufficient: `unstable-watch.yml`'s
`classify()` function recognizes only `BM_CM_1`'s `max_time`-plus-`"Test failed for example:"`
signature, so every real occurrence of this test's structurally different `_assert_scan_report`
failure would fall through to `NEW`, fail the nightly job loudly, and prevent the promotion
streak from ever accumulating. The classifier must therefore be extended as a first-class
companion change, and — because it currently lives as an inline heredoc inside YAML and is
consequently untestable — it must first be extracted into an importable module so the project's
mandatory TDD requirement (`code/docs/core/TESTING_GUIDE.md`) can actually be satisfied.
Definition of done: the marker is in place with all four criteria recorded at the source site,
the classifier correctly classifies this test's floor failure as `TIMING` while provably refusing
to launder a `disagreements != 0` failure into that bucket, the deselection is wired everywhere a
gating run reaches this test, and every change is covered by unit tests that failed before the
implementation and pass after.

### Research Integration

The research report is ground truth for this plan and supplies: the exact four-criteria comment
text and marker placement; the precise failure-message strings on both `_assert_scan_report`
assertions; the classifier's `MAX_TIME_BY_NODEID_FRAGMENT` / `FAILURE_SIGNATURE` structure and
its `if max_time is None: return "NEW"` fall-through; the constraint that a genuine
`disagreements != 0` failure must never be classified `TIMING`; the correction that the
`xdist_serial` isolation lead is closed rather than open (the class has carried the marker since
2026-08-06 and `differential-tests.yml` invokes pytest with no `-n` flag at all); and the finding
that the seven timing-out formulas' individual identities are unrecoverable from available CI
artifacts, so the marker text must say so honestly rather than assert a same-7 claim.

**Two additional findings this plan adds, discovered while verifying the report against the
tree** — both are wiring gaps the report did not reach, and both would otherwise turn a
"complete" marking into a locally-red suite or a false promotion signal:

1. **`oracle/run-oracle-suite.sh` carries no `unstable` deselection.** Its serial pass runs
   `pytest "$repo_root/oracle" -m "xdist_serial and not slow"`, which is exactly the pass this
   test lands in. `BM_CM_1` lives in `code/`, so this oracle-tree driver was never touched when
   the `unstable` category was introduced; this is the first oracle-tree marking, so it is the
   first time the gap bites. TESTING_GUIDE 8.9's "Where the deselection is wired" paragraph
   enumerates `tests.yml`, `differential-tests.yml`, and `flake.nix` — it does not yet name this
   script, and must.
2. **The promotion streak is `NEW`-sensitive only.** `unstable-watch.yml` computes
   `this_run_success = not any_new` and takes historical entries from `gh run list` job
   conclusions, and a `TIMING` failure deliberately leaves the job green. `READY TO PROMOTE`
   therefore fires after 20 nights even if the marked test `TIMING`-failed on every one of them —
   directly contradicting both `BM_CM_1`'s and this test's "20 consecutive runs recording zero
   failures" exit criterion. Adding a second marked test that is *expected* to fail regularly
   makes this materially worse, so the plan corrects what is cheaply correctable and records the
   residual limitation honestly rather than claiming a fix it does not deliver.

### Prior Plan Reference

No prior plan for this task. The closely related archived plan
`specs/archive/159_fix_bimodal_flake_and_unstable_category/plans/01_bimodal-flake-unstable-category.md`
established the `unstable` category, the `unstable-watch.yml` workflow, and the `BM_CM_1`
marking pattern this task follows; it deliberately deferred marking `TestGatingConclusiveScan`
until the budget repair had been CI-verified. That verification has now happened and failed to
move the number, which is what unblocks this task.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no ROADMAP.md consultation was
requested. No roadmap phases are included.

## Goals & Non-Goals

**Goals**:
- Mark `test_known_conclusive_population_self_consistent` `@pytest.mark.unstable` with all four
  TESTING_GUIDE 8.9 entry criteria recorded explicitly and separately identifiably at the source
  site.
- Make `unstable-watch.yml`'s classifier recognize this test's `_assert_scan_report`
  conclusive-floor failure as `TIMING`, while provably refusing to classify a
  `disagreements != 0` failure on the same test as anything but `NEW`.
- Make the classifier unit-testable by extracting it from the YAML heredoc into an importable
  module, so this change is developed test-first per the project's mandatory TDD requirement.
- Wire the `unstable` deselection into every gating invocation that reaches this test, including
  `oracle/run-oracle-suite.sh`, and make that wiring executable as a contract test.
- Correct every comment across the repository that this marking makes stale.

**Non-Goals**:
- Lowering `MIN_CONCLUSIVE_GATING_FORMULAS` (stays 100). Standing, twice-affirmed verdict.
- Widening `GATING_RECHECK_SOLVE_TIMEOUT_MS` a third time (stays 40000). The 20000 -> 40000
  widening was CI-verified and bought exactly zero additional conclusive formulas.
- Re-running or re-verifying the CI measurement expecting a different answer.
- Re-tuning `max_time` for `BM_CM_1`.
- Pursuing the `xdist_serial` isolation lead. It is closed, not open — see Research Integration.
- Identifying the seven timing-out formulas. Their identity is not recoverable from available
  artifacts; enabling `_generate_differential_report`'s `progress_path`/`artifact_dir`
  instrumentation to recover it is a possible future round, explicitly out of scope here.
- Re-tightening `differential-tests.yml`'s `--timeout=1500`. It remains a safe, harmless value
  and 8.9 does not require it.
- Building a true per-test promotion streak (would require downloading prior runs'
  `unstable-watch-record.jsonl` artifacts). Out of scope; the residual limitation is documented
  instead.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Classifier extraction silently changes `BM_CM_1`'s existing classification behavior | H | M | Phase 1 writes characterization tests pinning the *current* BM_CM_1 behavior before Phase 2 moves a single line; Phase 2 is behavior-preserving by contract and is verified green against those tests before Phase 3 adds anything |
| A future genuine `disagreements != 0` soundness bug gets laundered into the `TIMING` bucket and silently ignored | H | M | The gating-floor branch gates on the floor-assertion message string AND requires `disagreements=0` in the captured text; a dedicated Phase 1 test asserts a disagreements-message failure on this exact node id classifies `NEW`. This test is the guard, not the comment |
| Workflow YAML breaks (the classify step is a heredoc; extraction touches indentation-sensitive YAML) | H | M | Phase 2 is `atomic-batch`: script + workflow rewire land together, with a YAML-parse check and a local end-to-end invocation of the extracted script against synthetic JUnit XML before commit |
| Marking the test `unstable` turns `oracle/run-oracle-suite.sh`'s serial pass red locally | M | H | Phase 5 wires `and not unstable` into both passes, driven by a Phase 1 RED contract test that enumerates gating invocations |
| `READY TO PROMOTE` fires spuriously after 20 `TIMING`-failing nights | M | H | Phase 3 suppresses the promotion notice on any run with a failure and relabels the streak as an upper bound; the residual (historical component stays `NEW`-sensitive) is recorded at the marker site and in TESTING_GUIDE so exit-criterion evaluation is a human check against the uploaded per-run records |
| Test module cannot import `.github/scripts/...` under `nix flake check` (its `src = ./code` sandbox has no `.github/`) | M | H | Reuse the established skip guard already used by `code/tests/ci/test_workflow_parity.py` for exactly this situation; the guard's own comment explains why the real coverage still happens in the full-checkout CI job |
| Scope creep into re-measuring the shortfall or re-tuning budgets | H | L | Non-Goals above are explicit; no phase runs the gating scan for measurement purposes, and no phase edits either constant's value |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: RED — Contract tests for the classifier and the deselection wiring [COMPLETED]

**Goal**: Establish the failing tests that define correct behavior, before any implementation
exists. Both new test modules must fail for the right reason and be observed doing so.

**Tasks**:
- [x] Create `code/tests/ci/test_unstable_watch_classifier.py`. Load the not-yet-existing
      `.github/scripts/unstable_watch_classify.py` by absolute path via `importlib.util`,
      following the established in-repo pattern in
      `oracle/bimodal_logic/tests/test_timeout_skip_inventory.py::_load_oracle_conftest`.
- [x] Add the `nix flake check` skip guard at module scope, copying the mechanism and the
      explanatory comment shape from `code/tests/ci/test_workflow_parity.py`'s
      `_MISSING_REPO_ROOT_FILES` block (the `src = ./code` sandbox has no `.github/`).
- [x] Characterization tests pinning CURRENT `BM_CM_1` behavior (these define what Phase 2 must
      not change):
  - [x] node id containing `BM_CM_1-example_case7`, `duration=60.94`, failure text containing
        `"Test failed for example:"` -> `"TIMING"`.
  - [x] same node id, `duration=3.0` (well under `0.8 * 60`), same text -> `"NEW"`.
  - [x] same node id, `duration=60.94`, a different assertion message -> `"NEW"`.
  - [x] an unrecognized node id, any duration, any text -> `"NEW"`.
- [x] New-signature tests for the gating scan (these define Phase 3):
  - [x] node id containing `test_known_conclusive_population_self_consistent` with failure text
        carrying the floor message `"budget/performance regression to investigate, not a
        semantic one"` AND `"disagreements=0"` -> `"TIMING"`.
  - [x] **Laundering guard**: same node id, failure text carrying the disagreements message
        `"Self-comparison produced 3 disagreements among conclusive results"` -> `"NEW"`.
        Assert explicitly, with a comment naming this as the guard the research identified.
  - [x] same node id, floor message present but `"disagreements=0"` ABSENT from the text ->
        `"NEW"` (cannot confirm the soundness half held).
  - [x] same node id, floor message present but text also contains a nonzero-disagreements
        substring -> `"NEW"`.
  - [x] same node id, an `error`-shaped failure (e.g. `OracleTimeoutError` traceback, no
        assertion message) -> `"NEW"`.
  - [x] the gating branch is duration-independent: the same floor-message-plus-`disagreements=0`
        input classifies `"TIMING"` at both a small and a large `duration`, confirming no
        `max_time` threshold was smuggled in.
- [x] Tests for `parse_junit`: a synthetic JUnit XML fixture (written to `tmp_path`) covering a
      passed case, a `<failure>` case, an `<error>` case, and a `<skipped>` case; plus the
      missing-file case yielding nothing.
- [x] Test for the promotion-notice honesty rule (defines Phase 3): a helper that, given
      "this run had at least one failure of any classification", reports the streak as `0` and
      withholds `READY TO PROMOTE`.
- [x] Create `code/tests/ci/test_unstable_deselection_wiring.py`: regex-extract every pytest
      invocation from `.github/workflows/tests.yml`, `.github/workflows/differential-tests.yml`,
      `flake.nix`, and `oracle/run-oracle-suite.sh`; assert every invocation that carries an
      `-m` marker expression includes `not unstable`. Explicitly exclude
      `.github/workflows/unstable-watch.yml` (it selects `-m unstable` by design) and explicitly
      allow node-id-selecting invocations that carry no `-m` at all (differential-tests.yml's
      "Run CI gate tests explicitly" step). Use the regex approach, not `yaml.safe_load` —
      PyYAML is not installed in either CI toolchain, per `test_workflow_parity.py`'s own
      module docstring.
- [x] Run both modules and CONFIRM RED. Record the observed failure text for each in the
      progress notes; a module that errors at import for an unrelated reason is not a valid RED.

**Timing**: 1.25 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts two new test files and approximately 16 test functions.
Confirm at implementation time by running
`PYTHONPATH=code/src pytest code/tests/ci/test_unstable_watch_classifier.py code/tests/ci/test_unstable_deselection_wiring.py --collect-only -q`
and recording the actual collected count; the count is a hypothesis, the RED status of every
collected item is the requirement. It also asserts that
`code/tests/ci/test_workflow_parity.py`'s skip-guard mechanism is reusable verbatim — confirm by
reading that file's `_MISSING_REPO_ROOT_FILES` block before copying, not by assuming.

**Files to modify**:
- `code/tests/ci/test_unstable_watch_classifier.py` - NEW. Unit tests for the extracted
  classifier module.
- `code/tests/ci/test_unstable_deselection_wiring.py` - NEW. Contract test that every gating
  pytest invocation carries `not unstable`.
- `code/tests/ci/__init__.py` - update the module docstring's guard inventory to name the two
  new modules alongside `test_workflow_parity.py` and `test_timing_marker_coverage.py`.

**Verification**:
- Both new modules collect without import errors in their own right (the classifier module's
  loader failing to find the not-yet-created script is the EXPECTED failure, and must be
  reported as a clear, named failure rather than an opaque one).
- Every new test fails. Record the failure text.
- `PYTHONPATH=code/src pytest code/tests/ci/ -q` shows the pre-existing guards in that directory
  still pass, unaffected.

---

### Phase 2: GREEN A — Extract the classifier into an importable module (behavior-preserving) [COMPLETED]

**Goal**: Move the `unstable-watch.yml` classify step's inline Python into
`.github/scripts/unstable_watch_classify.py` with ZERO behavior change, and rewire the workflow
to invoke it. The characterization tests from Phase 1 turn green; the new-signature tests stay
red.

**Tasks**:
- [x] Create `.github/scripts/unstable_watch_classify.py` containing, verbatim in behavior, the
      current heredoc's `MAX_TIME_BY_NODEID_FRAGMENT`, `FAILURE_SIGNATURE`, `parse_junit`,
      `classify`, the record-building loop, the `gh run list` trend query, the step-summary
      writer, and the exit-code contract. Stdlib only — the watch job installs no PyYAML and no
      third-party parsing dependency, and none may be added.
- [x] Preserve the module docstring's existing explanation of the non-gating contract and the
      `TIMING` vs `NEW` rationale; carry it over rather than rewriting it.
- [x] Guard the entry point under `if __name__ == "__main__":` calling a `main()` that returns
      the exit code, so importing the module for tests has no side effects (no file writes, no
      `gh` subprocess, no `sys.exit`).
- [x] Keep the JUnit input paths (`/tmp/watch-code.xml`, `/tmp/watch-oracle.xml`) and the output
      path (`unstable-watch-record.jsonl`) parameterizable with the current values as defaults,
      so tests can drive the module against `tmp_path` fixtures.
- [x] Rewire `.github/workflows/unstable-watch.yml`'s "Classify results and build the trend
      report" step to `python3 .github/scripts/unstable_watch_classify.py`, deleting the heredoc.
      Preserve the step's `id`, `env` block (`GH_TOKEN`, `GITHUB_REPOSITORY`, `GITHUB_RUN_ID`),
      and its position between the two watch steps and the artifact upload.
- [x] Correct the now-false inline comment in the `watch_oracle` step. It currently reads "the
      oracle tree has no unstable-marked test, so this branch is expected to hit exit code 5
      every run"; after Phase 4 the oracle tree has exactly one. Reword to describe exit code 5
      as the tolerated no-collection case generally, not as the expected steady state.
- [x] Verify the workflow YAML still parses and the step structure is intact.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: interface

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts a two-file batch (`.github/scripts/unstable_watch_classify.py`
created, `.github/workflows/unstable-watch.yml` edited) and that the extraction is exactly
behavior-preserving. Confirm behavior preservation by the Phase 1 characterization tests going
green with no edits to them; confirm the file set by `git status --short` before staging. If the
extraction turns out to require a third file, that is a hypothesis miss to record, not to absorb
silently.

**Files to modify**:
- `.github/scripts/unstable_watch_classify.py` - NEW. The extracted, importable classifier.
- `.github/workflows/unstable-watch.yml` - replace the heredoc with a script invocation; correct
  the stale `watch_oracle` comment.

**Verification**:
- All Phase 1 BM_CM_1 characterization tests and all `parse_junit` tests pass, with the test file
  unmodified since Phase 1.
- The Phase 1 gating-signature tests still fail (nothing has been added yet).
- YAML parse check on `unstable-watch.yml` (e.g. `python3 -c "import yaml,sys;
  yaml.safe_load(open('.github/workflows/unstable-watch.yml'))"` in any local env that has
  PyYAML available; if none does, a structural diff review of the step block plus confirming the
  `run:` scalar is a single well-formed line is the fallback and must be recorded as such).
- End-to-end smoke: write two synthetic JUnit XML files to the default paths in a scratch
  directory, run the script with `GITHUB_STEP_SUMMARY` pointed at a temp file and no `GH_TOKEN`,
  and confirm it exits 0 on an all-passed input and 1 on a `NEW`-classified input, and that the
  `gh run list` failure path degrades to the existing `::warning::` rather than crashing.
- Atomic-batch discipline: intermediate per-file states are expected red and MUST NOT be
  committed; the two files land in one commit.

---

### Phase 3: GREEN B — Add the gating-floor TIMING signature and the promotion-notice honesty fix [COMPLETED]

**Goal**: Teach the classifier this test's failure shape, with the disagreements-laundering
guard, and stop the promotion notice from firing on nights the marked test actually failed. All
Phase 1 classifier tests go green.

**Tasks**:
- [x] Add the two signature constants to `.github/scripts/unstable_watch_classify.py`, named and
      commented so a future third marking has one obvious place to extend:
      `GATING_FLOOR_NODEID_FRAGMENT = "test_known_conclusive_population_self_consistent"` and
      `GATING_FLOOR_SIGNATURE = "budget/performance regression to investigate, not a semantic one"`.
      Take both strings from `_assert_scan_report`'s actual assertion message in
      `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — copy them, do not retype
      from memory.
- [x] Add a `DISAGREEMENT_SIGNATURE = "Self-comparison produced"` constant for the negative
      guard.
- [x] Extend `classify()` with a dedicated branch, evaluated BEFORE the `max_time` fall-through,
      that returns `"TIMING"` only when the node id matches the gating fragment AND the floor
      signature is present AND `"disagreements=0"` is present AND the disagreement signature is
      absent; otherwise `"NEW"`. Duration must play no part in this branch — the budget is
      per-formula across up to 103 formulas, so no single wall-clock threshold is meaningful.
      **Deviation**: probing pytest's actual default JUnit XML output for this exact
      print()-then-assert shape (`python3 -m pytest ... --junitxml=...` against a local
      reproduction of `_assert_scan_report`) showed the "disagreements=0" text this branch
      checks for is NEVER present in `<failure>`'s message/text under pytest's default
      `junit_logging` setting — only a sibling `<system-out>` element carries it, and only when
      `junit_logging` includes stdout (default is `no`). Without a fix, the "disagreements=0"
      check the plan specifies would make this branch permanently unreachable in real CI (every
      genuine floor failure would fall through to NEW, defeating the entire point of this
      phase). Fixed by: (1) extending `parse_junit()` (same file, in scope) to read a
      testcase's `<system-out>` sibling and fold it into `failure_text` for failed/error
      outcomes, and (2) adding `-o junit_logging=system-out` to
      `.github/workflows/unstable-watch.yml`'s oracle-tree pytest invocation (a workflow edit
      the Scope Hypothesis below flagged as a Phase-2-completeness signal, but this is not a
      Phase 2 gap -- the flag is needed only once this gating branch exists, so it is
      intrinsically a Phase 3 concern). Also required extending
      `code/tests/ci/test_unstable_watch_classifier.py` with a new
      `TestParseJunitSystemOut` case and correcting the `FLOOR_MESSAGE`/`FLOOR_ASSERTION_MESSAGE`
      Phase 1 fixtures to the realistic system-out-prefixed shape -- the original Phase 1
      fixture, taken literally, could never have exercised a true TIMING classification against
      real CI JUnit XML. See the phase's Verification section for the confirming test/smoke
      evidence.
- [x] Comment the branch with the reason the laundering guard exists: a `disagreements != 0`
      failure is a real soundness bug, and the two `_assert_scan_report` assertions fire in
      order (disagreements first, floor second), so a floor failure necessarily implies the
      disagreements assertion passed.
- [x] Update `MAX_TIME_BY_NODEID_FRAGMENT`'s "UPDATE THIS DICT whenever a new test is marked
      `unstable`" comment to point at the new signature constants, so the two extension patterns
      are discoverable from one place rather than found independently.
- [x] Replace `currently_unstable = sorted(MAX_TIME_BY_NODEID_FRAGMENT.keys())` with a single
      list covering BOTH marked-test patterns, so the `READY TO PROMOTE` notice names the right
      tests.
- [x] Promotion-notice honesty: track whether this run recorded ANY failure (`TIMING` or `NEW`),
      not just `NEW`. When it did, report the streak as `0` and withhold the `READY TO PROMOTE`
      notice. Keep the job's exit code driven by `NEW` only — the non-gating contract is
      unchanged and must stay unchanged.
- [x] Relabel the step-summary streak line to state that its historical component derives from
      job conclusions, which are `NEW`-sensitive only, so the number is an UPPER BOUND on the
      true zero-failure streak; direct the reader to the uploaded per-run
      `unstable-watch-record.jsonl` artifacts for the authoritative per-test history. Do not
      claim a per-test streak the mechanism does not compute.

**Timing**: 1.25 hours

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that all changes are confined to
`.github/scripts/unstable_watch_classify.py` (no workflow edit needed, because Phase 2 already
reduced the workflow to a one-line invocation). Confirm with `git status --short` at phase close;
a workflow edit appearing here means Phase 2's extraction was incomplete and should be recorded
as such.

**Hypothesis miss, recorded per this section's own instruction**: `git status --short` at phase
close shows THREE files, not one: `.github/scripts/unstable_watch_classify.py` (as hypothesized),
plus `.github/workflows/unstable-watch.yml` and `code/tests/ci/test_unstable_watch_classifier.py`.
The workflow edit is NOT a Phase-2-completeness gap (Phase 2's classify-step reduction to a
one-line invocation is intact and unchanged by this phase) -- it is a new `-o
junit_logging=system-out` flag that only became necessary once this phase's gating branch made
"disagreements=0" load-bearing; see the classify()-branch task's own Deviation note above for the
full empirical finding and fix. The test-file edit is the corresponding RED-then-GREEN coverage
for that same fix, not a violation of "test file unmodified since Phase 1" taken as a blanket
rule -- the alternative (leaving the fixture as originally written) would have shipped a
classifier branch that silently never fires TIMING against real CI JUnit XML, which the
Pre-Edit Verification Gate obligation this codebase runs under does not permit passing over
silently.

**Files to modify**:
- `.github/scripts/unstable_watch_classify.py` - new signature constants, the gating branch, the
  laundering guard, the promotion-notice honesty fix, and the updated extension-pointer comments;
  plus `parse_junit()` folding a testcase's `<system-out>` into `failure_text` (see Deviation).
- `.github/workflows/unstable-watch.yml` (deviation, not hypothesized) - `-o
  junit_logging=system-out` on the oracle-tree pytest invocation, so `<system-out>` is actually
  populated for `parse_junit()` to read.
- `code/tests/ci/test_unstable_watch_classifier.py` (deviation, not hypothesized) - new
  `TestParseJunitSystemOut` case; `FLOOR_MESSAGE`/`FLOOR_ASSERTION_MESSAGE` fixture correction.

**Verification**:
- Every Phase 1 classifier test passes. All 16 tests in
  `test_unstable_watch_classifier.py` pass (10 from Phase 1 unmodified in substance, plus the
  fixture correction and 1 new `TestParseJunitSystemOut` test from this phase's deviation). In
  particular the laundering guard test and the `"disagreements=0"`-absent test pass.
- `PYTHONPATH=code/src pytest code/tests/ci/ -q`: 34 passed, 1 failed --
  `test_unstable_deselection_wiring.py`'s `run-oracle-suite.sh` case, which stays red until
  Phase 5 as expected.
- Re-ran the Phase 2 end-to-end smoke with a synthetic JUnit XML carrying this test's floor
  failure (including the `<system-out>` element the fix requires): exit code 0, summary row
  classified `TIMING`, streak reported as `0`, no `READY TO PROMOTE` notice -- confirmed.
- Re-ran it with a synthetic disagreements failure on the same node id: exit code 1, an
  `::error title=UNSTABLE-WATCH: NEW FAILURE MODE::` annotation emitted -- confirmed.
- YAML parse check on the updated `unstable-watch.yml` and an `ast.parse` syntax check on the
  updated classifier module both passed.

---

### Phase 4: Mark the test `unstable` with the four-criteria record [COMPLETED]

**Goal**: Apply `@pytest.mark.unstable` to
`test_known_conclusive_population_self_consistent` and record all four TESTING_GUIDE 8.9 entry
criteria explicitly at the source site.

**Tasks**:
- [x] Add `@pytest.mark.unstable` directly above the method (method level, not class level —
      consistent with how `test_bimodal.py` marks individual cases rather than whole classes).
      Leave the class-level `@pytest.mark.xdist_serial` and the existing docstrings untouched.
- [x] Replace the stale `USER ACTION REQUIRED: this 40000ms multiplier is NOT YET VERIFIED on
      real CI ...` tail of `GATING_RECHECK_SOLVE_TIMEOUT_MS`'s comment block with the verified
      outcome and the four-criteria record, substantially as drafted in the research report's
      "Code change 2". Preserve the rest of that comment block's measurement history — 8.9 is
      explicit that the history of what was tried is worth more than a clean diff.
- [x] The verified-outcome paragraph must state: verified on real CI 2026-08-25 at commit
      93cda5b9, `agreements=96 disagreements=0 timeout_count=7 conclusive=96/103`, byte-for-byte
      identical to the pre-widening 20000ms measurement; doubling the budget bought zero
      additional conclusive formulas; do not widen again and do not re-verify expecting a
      different answer.
- [x] Criterion (1) WHAT FAILS AND WHY: the floor assertion's concrete counts across all three
      recorded runs (`31628414697`: 96/103, 7 timeouts; `31628228088`: 95/103, 8 timeouts;
      93cda5b9 at 2x budget: 96/103, 7 timeouts) against local 103/103 both unrestricted and
      under `taskset -c 0,1`.
- [x] Criterion (2) DEMONSTRABLY NOT SEMANTIC: zero disagreements on every recorded run;
      `_assert_scan_report`'s two assertions are separate and ordered, and only the second has
      ever fired.
- [x] Criterion (3) GENUINE FIX ATTEMPTED AND RECORDED: the CI-verified 2x widening that bought
      nothing; local 2-core restriction not reproducing the shortfall; and the closed
      `xdist_serial` lead — state plainly that the marker has been in place since 2026-08-06,
      predating both shortfall runs, and that `differential-tests.yml` uses no `-n` flag at all,
      so pytest-xdist sibling-worker contention was never live and must not be re-opened.
      State that `MIN_CONCLUSIVE_GATING_FORMULAS` is deliberately NOT lowered.
- [x] Record honestly that the seven timing-out formulas' individual identities are NOT
      recoverable from available CI artifacts (no `upload-artifact` step in
      `differential-tests.yml`; logs print aggregate counts only; the call site passes none of
      `_generate_differential_report`'s `progress_path` / `heartbeat_every` / `artifact_dir`
      parameters), and that the 7-vs-8 count difference rules out a strictly identical fixed
      subset while leaving a mostly-stable heavy-tailed subset open. Name enabling that
      instrumentation as the actionable path for a future round. Do NOT assert a same-7 claim.
- [x] Criterion (4) EXIT CRITERION: 20 consecutive `unstable-watch` runs with zero recorded
      failures of this test (verified against the uploaded per-run
      `unstable-watch-record.jsonl` artifacts, because the step-summary streak's historical
      component is `NEW`-sensitive only and is an upper bound — see Phase 3), OR a genuine
      CI-runner/harness fix (explicitly NOT a further budget widening) demonstrated to reach
      103/103 conclusive with 0 disagreements. A single green run never qualifies.
- [x] Add a one-line pointer from `test_known_conclusive_population_self_consistent`'s docstring
      to the criteria block, mirroring `test_bimodal.py`'s convention of keeping the prose at the
      marker's definition site.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that the marker's collection effect is exactly one test
added to the `unstable` set and exactly one test removed from the `not unstable` set in this
file, and that the enumerated dependent invocations are the complete set. Confirm at
implementation time with:
`PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py --collect-only -q -m unstable`
(expect exactly 1) and the `-m "not slow and not differential and not unstable"` collection count
before and after the edit (expect a difference of exactly 1). Do not assume; record both numbers.

**Files to modify**:
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - add `@pytest.mark.unstable`;
  rewrite the stale tail of `GATING_RECHECK_SOLVE_TIMEOUT_MS`'s comment block into the
  four-criteria record; add the docstring pointer.

**Verification**:
- `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py --collect-only -q -m unstable`
  collects exactly `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`
  (1/72; was 0/72 before this phase) -- confirmed.
- The same file with `-m "not slow and not differential and not unstable"` no longer collects it:
  62/72 collected (was 63/72 before this phase, a difference of exactly 1) -- confirmed.
- `-m "xdist_serial"` still collects it — the two markers are orthogonal and both must apply --
  confirmed.
- `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestGatingConclusiveScanMechanism -q`
  passes: 3 passed -- confirmed, the Z3-free mechanism proofs are unaffected by the marking.
- `oracle/conftest.py` needs no change (`unstable` is already registered there); confirmed by
  reading, and no `PytestUnknownMarkWarning` appeared in the collect output.
- No line in the diff changes the value of `GATING_RECHECK_SOLVE_TIMEOUT_MS` or
  `MIN_CONCLUSIVE_GATING_FORMULAS` -- confirmed with `git diff`.

**Deviation (phase-ordering, recorded per Phase 5's own ordering note)**: Phase 5's edits
(`oracle/run-oracle-suite.sh`, `.github/workflows/differential-tests.yml`) were made in the
working tree BEFORE this phase's marker landed, discovering that one of Phase 5's own
verification bullets (`--collect-only -q` not collecting the marked test under
`xdist_serial and not slow and not unstable`) implicitly depends on this phase's marker already
existing -- an unstated cross-phase dependency the wave table's `[4, 5]` grouping did not
surface. Corrected by closing this phase (4) first and Phase 5 second, despite Phase 5's edits
having been drafted first; Phase 5's own handoff records the completed ordering and the final
confirmation of that verification bullet.

---

### Phase 5: Wire the `unstable` deselection into the oracle suite driver [COMPLETED]

**Goal**: Close the gap this task's finding surfaced — `oracle/run-oracle-suite.sh` runs the
newly-marked test in its serial pass with no `unstable` deselection — and make the wiring
executable via the Phase 1 contract test.

**Tasks**:
- [x] Add `and not unstable` to `oracle/run-oracle-suite.sh`'s serial pass marker expression
      (`-m "xdist_serial and not slow"` -> `-m "xdist_serial and not slow and not unstable"`).
- [x] Add `and not unstable` to the parallel pass's expression as well, matching the defensive
      both-passes convention already used by `.github/workflows/tests.yml` and `flake.nix`. It
      changes nothing today (the marked test is `xdist_serial`) and prevents the next marking
      from reopening the same gap.
- [x] Add a short comment at the serial pass recording WHY the filter is there and pointing at
      TESTING_GUIDE 8.9, so a future reader does not remove it as redundant.
- [x] Annotate the script's header comment about `TestGatingConclusiveScan` running "in this
      second pass" — after this change it is deselected from that pass; correct the statement
      rather than deleting the paragraph's history.
- [x] Annotate (do NOT revert) `.github/workflows/differential-tests.yml`'s `--timeout=1500`
      rationale comment: its 7-8-timeouts-add-140-160s estimate assumed `TestGatingConclusiveScan`
      still runs in that step, which is no longer true. Record that 1500 is retained as a safe,
      harmless value and that 8.9 does not require re-tightening it.
- [x] Confirm `code/tests/ci/test_unstable_deselection_wiring.py` now passes.

**Timing**: 0.75 hours

**Depends on**: 3

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that the complete set of gating pytest invocations
needing `not unstable` is: `tests.yml` (2, already correct), `flake.nix` (2, already correct),
`differential-tests.yml` (1 of 2 — the node-id-selecting "Run CI gate tests explicitly" step has
no `-m` and does not name `TestGatingConclusiveScan`, verified against its explicit six-class
list), and `run-oracle-suite.sh` (2, both being fixed here). Confirm at implementation time with
`grep -rn "pytest" .github/workflows/ flake.nix oracle/run-oracle-suite.sh` and enumerate every
hit before concluding the set is closed; the Phase 1 contract test is the durable version of this
check.

**Files to modify**:
- `oracle/run-oracle-suite.sh` - `and not unstable` on both passes; comment corrections.
- `.github/workflows/differential-tests.yml` - annotate the now-stale `--timeout=1500` rationale.
  No functional edit: the gating step's `-m` already carries `and not unstable`.

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ci/test_unstable_deselection_wiring.py -q` passes:
  7 passed — confirmed (deferred until after Phase 4 landed the marker; see the ordering
  deviation recorded on Phase 4).
- `bash -n oracle/run-oracle-suite.sh` parses clean — confirmed.
- `PYTHONPATH=code/src pytest oracle -m "xdist_serial and not slow and not unstable" --collect-only -q`
  does not collect `test_known_conclusive_population_self_consistent` — confirmed (count: 0).
- `PYTHONPATH=code/src pytest code/tests/ci/test_workflow_parity.py -q` still passes — 5 passed,
  confirmed; the `tests.yml`/`flake.nix` parity invariant is untouched by this phase.
- `python3 -c "import yaml; yaml.safe_load(open('.github/workflows/differential-tests.yml'))"`
  parses clean after the annotation edit.
- Full `PYTHONPATH=code/src pytest code/tests/ci/ -q`: 35 passed, 0 failed — every guard in this
  directory (including the two from Phase 1) is now green.

---

### Phase 6: Documentation, final gate, and close-out [COMPLETED]

**Goal**: Bring TESTING_GUIDE.md's 8.9 record in line with reality and run the complete gate set
before the task closes.

**Tasks**:
- [x] Extend TESTING_GUIDE 8.9's "Currently marked" paragraph with a second entry for
      `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`, using the
      same one-line-pointer-to-the-source-of-truth convention `BM_CM_1` uses. Do not duplicate
      the four-criteria text into the guide.
- [x] Extend 8.9's "Where the deselection is wired" paragraph to name
      `oracle/run-oracle-suite.sh`'s two passes, and state that the oracle tree is now in scope
      for the deselection rule (it was not while `BM_CM_1` was the only marking).
- [x] Add a short subsection or paragraph to 8.9 recording the promotion-streak limitation: the
      workflow's streak counter is `NEW`-sensitive in its historical component and is therefore
      an upper bound; exit-criterion evaluation for a test that fails `TIMING`-style regularly
      must be checked against the uploaded per-run `unstable-watch-record.jsonl` artifacts.
- [x] Note in 8.9 that `unstable-watch.yml`'s classifier now lives in
      `.github/scripts/unstable_watch_classify.py` with unit tests in
      `code/tests/ci/test_unstable_watch_classifier.py`, and that adding a third `unstable`
      marking means extending that module (and its tests) — not editing YAML.
- [x] Check TESTING_GUIDE 8.8's mention of `TestGatingConclusiveScan` (around the gating vs.
      exhaustive split) for staleness introduced by the marking; correct only if it now asserts
      something false. (Confirmed no false claim introduced; no edit needed.)
- [x] Run the full gate set (below) and record the results. (Gate 3 narrowed — see Deviations in
      the implementation summary.)
- [x] Write the implementation summary to
      `specs/160_verify_bimodal_oracle_budget_and_watch_unstable_marker/summaries/01_unstable-marker-and-watch-classifier-summary.md`.

**Timing**: 1 hour

**Depends on**: 4, 5

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that TESTING_GUIDE 8.9 and 8.8 are the only prose
documents needing a change. Confirm with
`grep -rn "unstable" code/docs/ docs/ oracle/*.md --include=*.md` and enumerate every hit that
makes a now-false claim before concluding; record any additional file found rather than
absorbing it silently.

**Files to modify**:
- `code/docs/core/TESTING_GUIDE.md` - 8.9 "Currently marked", "Where the deselection is wired",
  the streak-limitation note, and the classifier-location note; 8.8 only if a statement became
  false.
- `specs/160_verify_bimodal_oracle_budget_and_watch_unstable_marker/summaries/01_unstable-marker-and-watch-classifier-summary.md` - NEW.

**Verification**:
- Full gate set, all green:
  - `PYTHONPATH=code/src pytest code/tests/ci/ -v`
  - `cd code && PYTHONPATH=src pytest tests/ -q`
  - `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -m "not slow and not differential and not unstable" -q`
    (excludes the newly-marked test by design; the run must not attempt it)
  - `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -m unstable --collect-only -q`
    collects exactly one test
- `git diff` review confirming no phase changed `MIN_CONCLUSIVE_GATING_FORMULAS`,
  `GATING_RECHECK_SOLVE_TIMEOUT_MS`, or any `max_time` value.
- No task-number references introduced outside `specs/**` (per
  `.claude/rules/no-task-references-in-deliverables.md`) — the marker comment must cite durable
  anchors (constant names, file names, CI run ids, dates), never a task number.

---

## Testing & Validation

- [ ] Every new test in `code/tests/ci/test_unstable_watch_classifier.py` was observed failing in
      Phase 1 before the corresponding implementation existed (RED recorded), and passes after.
- [ ] The disagreements-laundering guard test passes: a `disagreements != 0` failure on the
      marked test's node id classifies `NEW`, not `TIMING`.
- [ ] `code/tests/ci/test_unstable_deselection_wiring.py` passes across all four gating drivers.
- [ ] `code/tests/ci/test_workflow_parity.py` and `code/tests/ci/test_timing_marker_coverage.py`
      still pass — no regression to the pre-existing CI contract guards.
- [ ] `pytest --collect-only -m unstable` on the oracle tree collects exactly one test; on the
      `code/` tree it still collects the `BM_CM_1` case.
- [ ] `pytest --collect-only -m "not slow and not differential and not unstable"` on
      `test_cross_oracle_differential.py` excludes the marked test.
- [ ] `oracle/run-oracle-suite.sh` passes `bash -n` and its serial pass no longer selects the
      marked test.
- [ ] `.github/workflows/unstable-watch.yml` parses as valid YAML and its classify step invokes
      the extracted script.
- [ ] End-to-end smoke of the extracted classifier against synthetic JUnit XML covering: green,
      `BM_CM_1` TIMING, gating-floor TIMING, gating disagreements NEW. Exit codes 0/0/0/1.
- [ ] No CI run is dispatched or re-verified as part of this task.

## Artifacts & Outputs

- `.github/scripts/unstable_watch_classify.py` - extracted, importable, unit-tested classifier.
- `code/tests/ci/test_unstable_watch_classifier.py` - classifier unit tests including the
  laundering guard.
- `code/tests/ci/test_unstable_deselection_wiring.py` - executable contract that every gating
  pytest invocation carries `not unstable`.
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - `@pytest.mark.unstable` plus
  the four-criteria entry record.
- `.github/workflows/unstable-watch.yml` - script invocation replacing the heredoc; corrected
  oracle-step comment.
- `oracle/run-oracle-suite.sh` - `not unstable` on both passes.
- `.github/workflows/differential-tests.yml` - annotated stale timeout rationale.
- `code/docs/core/TESTING_GUIDE.md` - updated section 8.9.
- `specs/160_verify_bimodal_oracle_budget_and_watch_unstable_marker/summaries/01_unstable-marker-and-watch-classifier-summary.md`.

## Rollback/Contingency

Every phase is a self-contained commit, so rollback is `git revert` of the phase commits in
reverse order. The phases are independently revertible in the following sense:

- Reverting Phase 6 loses only documentation.
- Reverting Phase 5 restores the pre-existing (already-shipping) `run-oracle-suite.sh` behavior;
  the marked test would run locally in the serial pass again and can fail there.
- Reverting Phase 4 removes the marker and restores the test to the gating set. This is the
  meaningful rollback point if the marking is judged wrong; the classifier extension underneath
  it is harmless on its own (an unmatched node id simply never reaches the new branch).
- Reverting Phases 2-3 restores the inline heredoc classifier verbatim. Because Phase 2 is an
  atomic batch, its revert restores a consistent workflow; it must not be reverted partially.

Contingency if the extraction proves unworkable inside CI (e.g. a path-resolution problem in the
`actions/checkout` layout): keep the extracted module as the source of truth and have the
workflow step `cd` to the repository root explicitly before invoking it, rather than reverting to
an untestable heredoc. Reintroducing untestable inline logic would forfeit the TDD coverage this
plan's central risk mitigation depends on.
