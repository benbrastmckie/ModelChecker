# Implementation Plan: Fix unstable watch classifier laundering guard

- **Task**: 175 - Fix unstable watch classifier laundering guard
- **Status**: [IMPLEMENTING]
- **Effort**: 8 hours
- **Dependencies**: None
- **Research Inputs**: specs/175_fix_unstable_watch_classifier_laundering_guard/reports/01_laundering-guard-fix-design.md
- **Artifacts**: plans/01_laundering-guard-fix.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

`.github/scripts/unstable_watch_classify.py`'s gating-branch negative guard
(`DISAGREEMENT_SIGNATURE in failure_text`) matches `_assert_scan_report`'s own source listing,
which pytest embeds in every `<failure>` body, so every genuine gating-floor TIMING failure is
misclassified `NEW` and the nightly Unstable Watch job exits 1. This plan fixes the guard with an
anchored regex on the *rendered* message (research remedy (a)), lands a real-pytest-subprocess
regression test that the synthetic-string suite structurally cannot express, converts the
promotion streak from per-run to per-test using the already-uploaded per-run JSONL artifacts, and
records two findings (the zero-contention `xdist_serial` closure at the oracle constant's comment
block; two targeted `TESTING_GUIDE.md` section 8.9 edits). Done when the new real-pytest test
fails `NEW` against the current guard and passes `TIMING` after the fix, the disagreements
direction still classifies `NEW`, the streak is per-nodeid, and all pre-existing tests stay green.

### Research Integration

The report at `reports/01_laundering-guard-fix-design.md` is integrated as follows:

- **Remedy choice fixed to (a), not (b)** (report section 2), on blast-radius grounds:
  `_assert_scan_report` is a shared helper with at least five distinct call-site groups that pin
  its message text (`TestFullScanReport`, `TestGatingConclusiveScanMechanism`'s
  `pytest.raises(..., match="disagreements")`, the self-agreement group, and others). Remedy (b)
  would change what that helper prints and touch all of them; remedy (a) is confined to the
  classifier module. Phase 2 records this decision in-code, naming (b) as considered-and-declined
  so it is not re-litigated.
- **The regex is pre-verified** (report section 1): `re.search(r"Self-comparison produced \d+
  disagreements", ...)` does not match the source-listing line (which carries the
  `{report['disagreements']}` placeholder, never a literal digit) and does match a rendered
  failure. Phase 2 does not re-derive this.
- **`has_zero_disagreements` moves with the remedy for consistency, not because it shares the
  defect** (report section 2): the report confirmed empirically that `"disagreements=0"` never
  appears in a `<failure>` source listing (the value is interpolated), only in `<system-out>`.
  Phase 2 tightens it to a `scan report:`-anchored regex and states that asymmetry rationale
  explicitly.
- **`FAILURE_SIGNATURE` surveyed and found safe** (report section 2): it is the last statement of
  a single-assertion test, and pytest does not print source past the failure point, so no sibling
  assertion can leak it. Phase 2 records the survey as a comment rather than changing the code.
- **Real-pytest test design** (report section 3): self-contained fixture module (no
  `oracle`/`bimodal_logic`/Z3 import into `code/tests/ci`), `subprocess.run([sys.executable, "-m",
  "pytest", ...])` rather than a bare `pytest`, `-o junit_logging=system-out --junitxml=...`,
  driven through the real `parse_junit` + `classify`. Measured cost ~0.3-0.5s.
- **Per-test streak recommended as a fix, not a documented deferral** (report section 4): the
  per-run `unstable-watch-record-<run_id>` artifact already carries `nodeid` +
  `classification` per line, the marked set is 2 members today, and `gh` is already a dependency.
  Phases 3-4 build it; the report's fallback (document why it stays per-run) is retained only as
  this plan's contingency.
- **Finding sites located** (report sections 5-6): the oracle comment-block append point after
  item (3) near `GATING_RECHECK_SOLVE_TIMEOUT_MS`, and the two `TESTING_GUIDE.md` 8.9 paragraphs
  ("Promotion-streak limitation"; the "classifier lives in an importable module" paragraph).

### Prior Plan Reference

No prior plan for this task. Design history for the module being extended lives in task 160's
plan, which the research report consulted; its explicitly-deferred item ("a true per-test
promotion streak would require downloading prior runs' artifacts -- out of scope") is precisely
what Phases 3-4 now discharge.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context. `specs/ROADMAP.md` exists but contains
no item matching this task's subject (unstable watch, classifier, test-reliability); no roadmap
phases are added and ROADMAP.md is not modified.

## Goals & Non-Goals

**Goals**:
- The gating-floor negative guard discriminates the *rendered* disagreement count from the
  assertion's own source listing, so a genuine floor failure classifies `TIMING`.
- A genuine `disagreements != 0` failure on the same node id still classifies `NEW` — the
  soundness-laundering hole stays closed.
- A regression test that generates its JUnit XML by actually invoking pytest in a subprocess
  covers both directions; it fails against the current guard and passes after the fix.
- The promotion streak is computed per node id from the per-run JSONL artifacts, and
  `READY TO PROMOTE` names only the node id(s) that individually earned it.
- The zero-contention `xdist_serial` finding is recorded at the oracle constant's comment block.
- `TESTING_GUIDE.md` section 8.9 reflects the new streak mechanism and carries the generalizable
  rendered-vs-source lesson for whoever adds a third `unstable` marking.

**Non-Goals**:
- Remedy (b) (a machine-readable `UNSTABLE-SIGNATURE:` line emitted by `_assert_scan_report`).
  Declined with reasons; not implemented.
- Any change to `MIN_CONCLUSIVE_GATING_FORMULAS` (stays 100) or `GATING_RECHECK_SOLVE_TIMEOUT_MS`
  (stays 40000).
- Removing or weakening the `unstable` marker on the oracle test.
- Making the classify step non-gating (`continue-on-error: true`) or otherwise altering
  `unstable-watch.yml`'s non-gating contract (no `needs:`, no `push`/`pull_request`/`tags`
  trigger, no branch protection). The workflow file is outside this task's `file_scope`.
- Investigating or fixing the underlying 96/103 oracle floor shortfall. This task fixes the
  observer, not the observed.
- Deleting or rewriting the 16 existing synthetic tests.
- Any third-party dependency in the classifier. `re`, `json`, `subprocess`, `zipfile` are stdlib
  and permitted; PyYAML and friends are not.
- Pushing, dispatching the workflow, or opening a PR. Final CI confirmation is user-only.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The new subprocess-pytest test passes for the wrong reason (fixture never reproduces the two-assertion source echo), so the RED state is a construction error rather than the defect | H | M | Phase 1 asserts the *specific* observed RED: `classify(...) == "NEW"` with the source-listing echo positively confirmed present in the parsed `failure_text` before the classification is asserted. A missing echo fails the test with its own distinct message. |
| Subprocess pytest inherits the outer run's `-p` plugins, addopts, or rootdir `conftest.py` and behaves differently in CI than locally | M | M | Invoke with `-p no:cacheprovider`, an explicit `--rootdir` on the tmp fixture directory, and `-o junit_logging=system-out` set on the command line so no repo `pytest.ini`/`pyproject` value can override it. Assert the subprocess's own returncode is 1 (tests ran and one failed) before parsing the XML. |
| Tightening `has_zero_disagreements` to a `scan report:`-anchored regex over-anchors and stops matching the real CI text (e.g. the `<system-out>` line wraps or `re.DOTALL` is needed across the newline) | H | M | Phase 2 validates the tightened regex against the real captured text reproduced by Phase 1's subprocess XML, not against a hand-typed string; use `re.search` with an explicit `[\s\S]*?` or `re.DOTALL` span and a bounded gap. If it cannot be made to match the real text, leave `has_zero_disagreements` as the bare substring and record why in-code — the anchored guard fix is the load-bearing half. |
| `gh run download` for a prior run's artifact fails (expired artifact, network, rate limit), breaking the nightly classify step | H | M | Wrap every per-run artifact fetch in its own try/except following the existing `gh run list` pattern; a fetch failure yields "no record for that run" which conservatively breaks the streak rather than extending it, and emits a `::warning::`. The classify step's exit code stays driven solely by `any_new`. |
| Phase 3-4's streak rewrite regresses the existing `TestPromotionStreakHonesty` contract | M | M | Keep `compute_promotion_streak`'s existing signature and semantics intact as the per-run primitive; add the per-test computation as a new function alongside it. Phase 3 runs the existing streak tests unmodified as its own gate. |
| Artifact-download volume grows unbounded as more tests are marked `unstable` | L | L | Bound the fetch to the current marked set (2 node ids) x the same 25-run history window `gh run list` already uses; state the bound in-code so a future third marking inherits it. |
| The oracle-file comment edit accidentally crosses out of the comment block into the constant's value | H | L | Phase 5 is `prose` tier with an explicit post-edit assertion that `GATING_RECHECK_SOLVE_TIMEOUT_MS == 40000` and `MIN_CONCLUSIVE_GATING_FORMULAS == 100` are byte-identical to their pre-edit values, plus a clean collection check on the oracle test module. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3, 5 | -- |
| 2 | 2, 4 | 1, 3 |
| 3 | 6 | 2, 4 |
| 4 | 7 | 2, 4, 5, 6 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Real-pytest regression test (RED) [COMPLETED]

**Goal**: Add the non-negotiable real-pytest-subprocess regression test to
`code/tests/ci/test_unstable_watch_classifier.py`, covering both directions, and confirm it fails
against the *current* (unfixed) guard for the documented reason.

**Tasks**:
- [x] Add a helper that writes a self-contained fixture module into `tmp_path` reproducing
      `_assert_scan_report`'s exact two-assertion shape: a passing
      `assert report["disagreements"] == 0, f"Self-comparison produced {report['disagreements']} disagreements among ..."`
      followed by a failing floor assert carrying the verbatim
      `"budget/performance regression to investigate, not a semantic one"` text and an
      unconditional `print()` of `scan report: agreements=... disagreements=0 timeout_count=... conclusive=96/103`.
      Copy both assertion strings verbatim from `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`'s
      `_assert_scan_report` (line ~748), following this module's existing verbatim-copy convention.
      Do NOT import `oracle`, `bimodal_logic`, or `z3` from the fixture.
- [x] Add a helper that runs `subprocess.run([sys.executable, "-m", "pytest", str(fixture),
      "-o", "junit_logging=system-out", f"--junitxml={xml}", "-p", "no:cacheprovider"], ...)`,
      asserts the returncode is 1, and returns the XML path.
- [x] Test A (`test_real_pytest_floor_failure_classifies_timing`): name the fixture's test
      function so the parsed nodeid contains `GATING_FLOOR_NODEID_FRAGMENT`; drive
      `parse_junit` -> `classify`; first assert the source-listing echo IS present in the parsed
      `failure_text` (so a fixture that fails to reproduce the echo fails distinctly), then assert
      `classify(...) == "TIMING"`.
- [x] Test B (`test_real_pytest_disagreement_failure_still_classifies_new`): a second fixture
      variant where the FIRST (disagreements) assert is the one that fails, with a rendered
      non-zero count; assert `classify(...) == "NEW"`.
- [x] Group both under a new `class TestRealPytestJunitRoundTrip` with a docstring stating why a
      synthetic-string test cannot express this defect.
- [x] Run `PYTHONPATH=code/src pytest code/tests/ci/test_unstable_watch_classifier.py -v` and
      record the RED state: Test A fails asserting `TIMING` but receiving `"NEW"`; Test B passes
      (the guard is already correct in that direction).
- [x] Confirm the 16 pre-existing tests are untouched and still pass in the same run.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: The report states 16 existing tests, all currently passing, across five
classes (`TestClassifyBMCM1Characterization`, `TestClassifyGatingFloorSignature`,
`TestParseJunit`, `TestParseJunitSystemOut`, `TestPromotionStreakHonesty`). Confirm at
implementation time by running the file and reading the collected/passed counts from pytest's own
output before adding anything; if the count differs, record the actual number and proceed — the
count is not load-bearing, only the "none of them regress" property is.

**Files to modify**:
- `code/tests/ci/test_unstable_watch_classifier.py` - add subprocess/fixture helpers and
  `TestRealPytestJunitRoundTrip` with two tests; add `subprocess`/`sys` imports.

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ci/test_unstable_watch_classifier.py -v` shows exactly
  one failure (Test A), failing with the literal classification `"NEW"` where `"TIMING"` was
  expected — the documented RED, not a construction error.
- Test A's echo pre-assertion passes, proving the fixture reproduces the source-listing echo.
- All pre-existing tests still pass.

---

### Phase 2: Fix the laundering guard (GREEN) [NOT STARTED]

**Goal**: Replace the bare-substring negative guard with an anchored regex on the rendered
message, tighten `has_zero_disagreements` alongside it, record the remedy decision and the
`FAILURE_SIGNATURE` safety survey in-code, and turn Phase 1's RED test green.

**Tasks**:
- [ ] Add `import re` to `.github/scripts/unstable_watch_classify.py` (stdlib; permitted).
- [ ] Convert `DISAGREEMENT_SIGNATURE` from a bare substring to an anchored pattern
      `r"Self-comparison produced \d+ disagreements"` (keep the constant name; a precompiled
      `re.compile` at module level is preferred over a per-call `re.search` literal). Update
      `classify()`'s `has_disagreement_failure` to use it.
- [ ] Tighten `has_zero_disagreements` to a `scan report:`-anchored regex matching the rendered
      report line, validated against the real captured text from Phase 1's subprocess XML rather
      than a hand-typed string. If it cannot be made to match the real text, leave the bare
      substring in place and record that outcome in-code with its reason.
- [ ] Rewrite the comment at `DISAGREEMENT_SIGNATURE`'s definition site: keep the existing
      reasoning for WHY the guard exists (a `disagreements != 0` failure must never launder into
      TIMING) unchanged; replace only the HOW to describe matching the rendered count. Add a
      one-sentence note that remedy (b) (a machine-readable `UNSTABLE-SIGNATURE:` line from
      `_assert_scan_report`) was considered and declined on blast-radius grounds, pointing at
      `specs/175_fix_unstable_watch_classifier_laundering_guard/reports/01_laundering-guard-fix-design.md`.
- [ ] Update `classify()`'s docstring's laundering-guard paragraph: the "mutually exclusive
      outcomes" reasoning is true of BEHAVIOR and false of the TEXT, which is why the guard must
      match the rendered count.
- [ ] Add a comment near `FAILURE_SIGNATURE`'s definition recording the survey result: it is the
      last statement of a single-assertion test, pytest prints source only up to the failure
      point, and it is a positive confirmation signature rather than a negative guard against a
      co-located different failure mode — so it does not share this exposure and is deliberately
      left unchanged.
- [ ] Add a synthetic companion test asserting the raw source-listing f-string
      (`{report['disagreements']}`, no literal digit) does NOT match the new pattern, so the
      discrimination property is pinned independently of the subprocess path.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: The report asserts the ONLY live instance of this defect class is
`DISAGREEMENT_SIGNATURE`, with `has_zero_disagreements` sharing the brittleness class but not the
defect, and `FAILURE_SIGNATURE` safe. Confirm at implementation time by re-reading all three
signature checks in `classify()` and, for each, checking whether a *sibling textually-preceding*
assertion in the corresponding source function could echo it. If a fourth check is found, extend
this phase rather than deferring it.

**Files to modify**:
- `.github/scripts/unstable_watch_classify.py` - `import re`; `DISAGREEMENT_SIGNATURE` pattern;
  `classify()`'s two gating-branch checks; three comment/docstring blocks.
- `code/tests/ci/test_unstable_watch_classifier.py` - add the source-listing-does-not-match
  synthetic companion test.

**Verification**:
- Phase 1's Test A now passes (`TIMING`); Test B still passes (`NEW`).
- `PYTHONPATH=code/src pytest code/tests/ci/test_unstable_watch_classifier.py -v` is fully green
  with no test removed or modified from the pre-existing 16.
- `python -c "import ast,sys; ast.parse(open('.github/scripts/unstable_watch_classify.py').read())"`
  parses clean, and the module imports with stdlib only (no new third-party import).
- Enumerated direct dependents built/run: `code/tests/ci/` in full (the only in-repo importer of
  the classifier module).

---

### Phase 3: Per-node-id streak core (pure function + tests) [NOT STARTED]

**Goal**: Add a network-free, per-node-id streak computation alongside the existing per-run
`compute_promotion_streak`, with tests, before any artifact-download plumbing exists.

**Tasks**:
- [ ] Add `compute_per_test_promotion_streak(nodeid, this_run_classification, past_run_classifications)`
      (or equivalent signature) returning `(streak, ready_to_promote)` for a single node id.
      Apply the same honesty rule the per-run function already implements: ANY failure
      classification (`TIMING` or `NEW`) for THAT node id zeroes THAT node id's streak; a run with
      no record for the node id is treated as breaking the streak (conservative), not extending it.
- [ ] Leave `compute_promotion_streak`'s signature and semantics untouched — it remains the
      per-run primitive and its existing tests must pass unmodified.
- [ ] Add a docstring stating that this function's history component is now
      classification-accurate (derived from the per-run JSONL records), unlike
      `compute_promotion_streak`'s job-conclusion-derived, NEW-sensitive-only history — the
      residual limitation the module docstring records for the per-run path does not apply here.
- [ ] Add a `class TestPerTestPromotionStreak` covering: a clean 20-run history reaching
      `ready_to_promote`; a single `TIMING` in the window zeroing the streak; a single `NEW`
      zeroing it; a missing record breaking it; and two node ids with divergent histories yielding
      divergent streaks (the defect this fixes).

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `.github/scripts/unstable_watch_classify.py` - add `compute_per_test_promotion_streak`.
- `code/tests/ci/test_unstable_watch_classifier.py` - add `TestPerTestPromotionStreak`.

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ci/test_unstable_watch_classifier.py -v` green,
  including `TestPromotionStreakHonesty` unmodified.
- The divergent-histories test demonstrably fails if the two node ids' streaks are coupled.

---

### Phase 4: Per-run artifact history and READY TO PROMOTE wiring [NOT STARTED]

**Goal**: Fetch prior runs' `unstable-watch-record-<run_id>` artifacts, derive per-node-id
classification history from them, wire the per-test streak into `run()`, and make
`READY TO PROMOTE` name only the node id(s) that individually earned it.

**Tasks**:
- [ ] Add a `fetch_past_classifications(repo, nodeids, past_run_ids)` helper that, for each past
      run id, downloads `unstable-watch-record-<run_id>` via `gh run download <id> -n
      unstable-watch-record-<id> -D <tmpdir>` (or `gh api .../actions/artifacts` + zip extraction),
      parses the JSONL, and returns `{nodeid: [classification_or_None, ...]}` ordered
      newest-first.
- [ ] Wrap every fetch in its own try/except following the existing `gh run list` pattern; on
      failure emit `::warning::` and record `None` (streak-breaking) for that run rather than
      raising. The classify step's exit code must stay driven solely by `any_new`.
- [ ] Bound the work explicitly: iterate only `currently_unstable` (the already-computed
      `set(MAX_TIME_BY_NODEID_FRAGMENT) | {GATING_FLOOR_NODEID_FRAGMENT}`) against the same 25-run
      window `gh run list` already uses; state the `O(marked_tests x 25)` bound in a comment so a
      future third marking inherits it.
- [ ] Collect this run's own per-node-id classification from the `records` list `run()` already
      builds (match by `GATING_FLOOR_NODEID_FRAGMENT`-style substring against each record's
      `nodeid`, consistent with how `classify()` matches).
- [ ] Compute a per-node-id streak for each marked test; fire `READY TO PROMOTE` naming ONLY the
      node ids whose own streak reached 20, not the whole `currently_unstable` set.
- [ ] Update the step-summary text: replace the single global "Consecutive green streak: N / 20"
      plus its UPPER BOUND caveat with a per-test breakdown (one row or line per marked node id).
      Keep the per-run number only if it still carries meaning, clearly labelled as such.
- [ ] Add tests driving `run()` directly against `tmp_path` JUnit fixtures with the artifact
      fetch monkeypatched/injected, asserting: a clean BM_CM_1 history plus a failing gating test
      yields `READY TO PROMOTE` for BM_CM_1 alone (never both), and a failing BM_CM_1 yields no
      notice.
- [ ] Confirm `run()` still returns 1 only when a `NEW` classification is present, unchanged.

**Timing**: 2 hours

**Depends on**: 3

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: The marked set is asserted to be exactly 2 node ids today
(`BM_CM_1-example_case7` from `MAX_TIME_BY_NODEID_FRAGMENT`, plus
`test_known_conclusive_population_self_consistent`), and the uploaded artifact is asserted to be
named `unstable-watch-record-${{ github.run_id }}` containing `unstable-watch-record.jsonl` with
per-line `nodeid` and `classification` fields. Confirm at implementation time by re-reading
`MAX_TIME_BY_NODEID_FRAGMENT`/`GATING_FLOOR_NODEID_FRAGMENT` and the `upload-artifact` step in
`.github/workflows/unstable-watch.yml` (read-only — that file is outside `file_scope` and must not
be edited), and by checking the JSONL record dict `run()` writes. If the artifact name or record
shape differs, adjust the fetch helper to what is actually there.

**Files to modify**:
- `.github/scripts/unstable_watch_classify.py` - `fetch_past_classifications` helper; `run()`'s
  streak/notice/summary block.
- `code/tests/ci/test_unstable_watch_classifier.py` - `run()`-level per-test streak tests.

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ci/test_unstable_watch_classifier.py -v` fully green.
- A simulated fetch failure produces a `::warning::` and a broken (not extended) streak, and does
  not change `run()`'s return code.
- `run()`'s return value is still 1 iff a `NEW` classification was recorded.
- Enumerated direct dependents built/run: `code/tests/ci/` in full.

---

### Phase 5: Record the zero-contention finding at the oracle constant [NOT STARTED]

**Goal**: Append a dated note to the `GATING_RECHECK_SOLVE_TIMEOUT_MS` comment block in
`oracle/bimodal_logic/tests/test_cross_oracle_differential.py` retiring the sibling-worker
contention sub-hypothesis, so the next investigator does not repeat the experiment.

**Tasks**:
- [ ] Append a new item (after the existing item (3), e.g. as item (3b)) to the comment block
      above `GATING_RECHECK_SOLVE_TIMEOUT_MS` recording: `unstable-watch.yml` installs no
      pytest-xdist and passes no `-n`, i.e. true single-process execution with zero sibling
      workers — strictly stronger isolation than `@pytest.mark.xdist_serial` provides; five
      consecutive nightly runs (33091941820 / 2026-08-27, 33193518591 / 2026-08-28,
      33250263772 / 2026-08-29, 33306220265 / 2026-08-30, 33386925098 / 2026-08-31) reproduced the
      identical 96/103 conclusive, 7-timeout, 0-disagreement result; this retires the
      sibling-worker-contention sub-hypothesis specifically, leaving hypothesis (1)'s pure
      runner-hardware-capacity framing untouched and unresolved.
- [ ] Add one sentence recording the duration drift as an observation only: 761.61s (08-27) ->
      898.78s (08-30) -> 808.64s (08-31) against the job's `timeout-minutes: 20` (1200s) — real
      headroom today (worst case ~75% of budget), worth a sentence for the next investigator, not
      a change to any budget or timeout value.
- [ ] Make no change to any constant value, assertion, or executable statement in this file.

**Timing**: 45 minutes

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: The edit is asserted to be confined to the comment block preceding
`GATING_RECHECK_SOLVE_TIMEOUT_MS` (whose assignment currently sits at line ~217, with the
comment block spanning roughly lines 97-216 and item (3) beginning near line 187). Confirm at
implementation time by locating the block by its item-(3) text rather than by line number, and by
diffing to prove every changed hunk lies inside a `#` comment region.

**Files to modify**:
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - comment block above
  `GATING_RECHECK_SOLVE_TIMEOUT_MS` only.

**Verification**:
- `git diff` read-through confirms every changed hunk lies inside a `#`-prefixed comment region
  (the `prose` tier's own check).
- `grep -n "^GATING_RECHECK_SOLVE_TIMEOUT_MS = 40000" oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
  and the corresponding `MIN_CONCLUSIVE_GATING_FORMULAS = 100` line are byte-identical to their
  pre-edit values — the `prose` tier's comment-boundary blind spot, closed explicitly.
- `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py --collect-only -q`
  collects clean (no syntax damage). Do not run the full oracle suite — the floor shortfall is out
  of scope and expected.

---

### Phase 6: TESTING_GUIDE.md section 8.9 targeted edits [NOT STARTED]

**Goal**: Update the two identified paragraphs in section 8.9 to match what Phases 2-4 actually
landed, and record the generalizable rendered-vs-source lesson.

**Tasks**:
- [ ] Rewrite the "Promotion-streak limitation" paragraph (currently beginning
      "`unstable-watch.yml`'s step-summary streak counter's historical component...") to describe
      the per-node-id mechanism Phase 4 built: history is now derived from the per-run
      `unstable-watch-record-<run_id>` JSONL artifacts and is classification-accurate rather than
      job-conclusion-derived; each marked test's streak is independent; `READY TO PROMOTE` names
      only the test that earned it. State the residual bounds honestly: the 25-run window, GitHub's
      artifact retention, and a fetch failure conservatively breaking a streak.
- [ ] Add a one- or two-sentence caution near the existing "The classifier lives in an importable
      module, not YAML" paragraph, for whoever adds a third `unstable` marking: a negative/guard
      signature must match the *rendered* failure text (a regex anchored to a concrete rendered
      shape, or a `<system-out>`-only structured line), never a bare substring that could appear
      verbatim in the assertion's own source listing when a JUnit `<failure>` echoes a function
      body containing more than one assertion — and the test proving it must drive real pytest
      output, not a synthetic string.
- [ ] Touch no other subsection (8.6, 8.8, 8.10, 8.11 are unrelated).
- [ ] Use durable anchors only — no task-number references (this file is outside `specs/**`).

**Timing**: 45 minutes

**Depends on**: 2, 4

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: Exactly two paragraphs in section 8.9 are asserted to need editing, located
near lines 972-985 ("The classifier lives in an importable module, not YAML" at ~972;
"Promotion-streak limitation" at ~979). Confirm at implementation time by re-reading section 8.9
in full and locating both paragraphs by their opening text rather than by line number; if a third
paragraph is stale after Phases 2-4, edit it too and note the addition.

**Files to modify**:
- `code/docs/core/TESTING_GUIDE.md` - section 8.9, two paragraphs.

**Verification**:
- `git diff code/docs/core/TESTING_GUIDE.md` shows changes confined to section 8.9.
- `grep -nE '\btasks? [0-9]+\b' ` over the diff finds no task-number reference (per
  `.claude/rules/no-task-references-in-deliverables.md`).
- Every cross-reference named in the new text (constant names, artifact name, file paths) resolves
  to something that actually exists after Phases 2-4 — the `prose` tier's broken-cross-reference
  blind spot, closed explicitly.

---

### Phase 7: Full gate and consistency pass [NOT STARTED]

**Goal**: Run the complete gate set across the whole change, confirm the exit condition's
locally-verifiable half, and confirm every hard constraint held.

**Tasks**:
- [ ] `PYTHONPATH=code/src pytest code/tests/ci/ -v` fully green.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q` to confirm no wider regression in the general
      test tree.
- [ ] `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py --collect-only -q`
      collects clean.
- [ ] Re-verify the exit condition's locally-checkable half: check out the pre-Phase-2 classifier
      into a scratch copy, run the new real-pytest test against it, and confirm it fails `NEW`;
      then confirm it passes `TIMING` against the fixed module. Record both results.
- [ ] Hard-constraint audit against the final diff: `MIN_CONCLUSIVE_GATING_FORMULAS` still 100;
      `GATING_RECHECK_SOLVE_TIMEOUT_MS` still 40000; the `unstable` marker untouched; no
      `continue-on-error` added to any classify step; `.github/workflows/unstable-watch.yml`
      unmodified (`git diff --stat` names no workflow file); the classifier imports stdlib only;
      no existing test deleted or weakened.
- [ ] Confirm the diff touches only the four `file_scope` paths plus `specs/**`.
- [ ] State explicitly in the implementation summary that final CI confirmation is user-only: an
      agent may author and commit but cannot push or `workflow_dispatch`, so the exit condition's
      last step lands on the next nightly run or a user-initiated dispatch.

**Timing**: 30 minutes

**Depends on**: 2, 4, 5, 6

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- None (verification only). Any defect found is fixed in the owning phase's file.

**Verification**:
- The complete gate set above passes.
- The before/after classification of the new regression test is recorded with both literal values
  (`NEW` -> `TIMING`).
- The hard-constraint audit is recorded item by item with the command output backing each.

---

## Testing & Validation

- [ ] The new real-pytest-subprocess test fails with the literal classification `"NEW"` against
      the unfixed guard and passes with `"TIMING"` against the fixed one (both recorded).
- [ ] A genuine `disagreements != 0` failure driven through the same real-pytest path still
      classifies `NEW`.
- [ ] A synthetic test pins that the raw source-listing f-string does not match the new pattern.
- [ ] All 16 pre-existing tests in `code/tests/ci/test_unstable_watch_classifier.py` pass,
      unmodified.
- [ ] Two marked node ids with divergent histories produce divergent streaks; `READY TO PROMOTE`
      names only the earner.
- [ ] A simulated artifact-fetch failure warns, breaks the streak conservatively, and does not
      change `run()`'s return code.
- [ ] `run()` returns 1 iff a `NEW` classification was recorded (non-gating contract preserved).
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q` shows no regression.
- [ ] The oracle differential module collects clean and both protected constants are unchanged.

## Artifacts & Outputs

- `.github/scripts/unstable_watch_classify.py` - anchored rendered-message guard, tightened
  zero-disagreements check, recorded remedy decision and `FAILURE_SIGNATURE` survey,
  `compute_per_test_promotion_streak`, `fetch_past_classifications`, per-test
  `READY TO PROMOTE`/step-summary wiring.
- `code/tests/ci/test_unstable_watch_classifier.py` - `TestRealPytestJunitRoundTrip`,
  `TestPerTestPromotionStreak`, `run()`-level per-test streak tests, source-listing companion
  test; 16 pre-existing tests untouched.
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - comment-only addition at the
  `GATING_RECHECK_SOLVE_TIMEOUT_MS` block.
- `code/docs/core/TESTING_GUIDE.md` - two updated paragraphs in section 8.9.
- `specs/175_fix_unstable_watch_classifier_laundering_guard/summaries/01_laundering-guard-fix-summary.md`
  - implementation summary, including the user-only final-verification note.

## Rollback/Contingency

- Every phase is a separate commit; revert individually. The classifier change (Phase 2) and the
  streak change (Phases 3-4) are independent and revertible without each other.
- If Phase 4's artifact-download approach proves infeasible in practice (artifact retention too
  short, `gh` permissions insufficient, or the cost judged disproportionate), fall back to the
  research report's documented escape hatch: keep the per-run streak, and in Phase 6 rewrite the
  "Promotion-streak limitation" paragraph substantively — stating plainly that the global per-run
  design couples every marked test's promotion path to every other marked test's failures, that
  this is now actively blocking the BM_CM_1 exit criterion rather than hypothetical, and the
  reason for accepting the coupling. Phase 3's pure function can still land (it is network-free
  and independently useful) or be reverted with Phase 4. Taking this fallback must be recorded
  explicitly in the summary, not left silent.
- If the tightened `has_zero_disagreements` regex cannot be made to match the real captured text,
  revert that single check to the bare substring and record why in-code; the anchored
  `DISAGREEMENT_SIGNATURE` guard is the load-bearing half and stands alone.
- Phases 5 and 6 are comment/prose-only and revert cleanly with no behavioral consequence.
