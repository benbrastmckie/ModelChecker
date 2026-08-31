# Implementation Plan: Task #177

- **Task**: 177 - Bimodal in-development status and CI non-gating
- **Status**: [IMPLEMENTING]
- **Effort**: 7 hours
- **Dependencies**: None
- **Research Inputs**: specs/177_bimodal_in_development_status_and_ci_non_gating/reports/01_bimodal-ci-gating-ground-truth.md
- **Artifacts**: plans/01_bimodal-in-development-ci-non-gating.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Bimodal is already non-gating in CI for *completeness* claims (the `development` marker is applied
to all 313 bimodal tests and deselected by every `-m`-bearing gating invocation), but three gaps
remain: the one deliberately-retained soundness gate is undocumented and untested, the unified
`run_tests.py` runner cannot reproduce or select the marker at all, and the already-implemented
`DEV_STATUS` observer path in `unstable-watch.yml` has no producing step so it never runs. This
plan closes those three gaps, corrects a documented invocation count that is wrong in seven places
(seven, not six) and makes that count executable, and fixes four false claims in
`.github/workflows/README.md` plus a self-contradicting comment block in `tests.yml`. Definition of
done: criteria (a), (b), and (c) from the task are each proven by a real assertion or a recorded
command transcript, not by prose.

### Research Integration

Findings from `reports/01_bimodal-ci-gating-ground-truth.md` that shape this plan and supersede the
original task description:

- **The count is SEVEN, not six** (§1.2): `tests.yml` (2) + `flake.nix` (2) +
  `differential-tests.yml` (1) + `run-oracle-suite.sh` (2). No executable test asserts the
  aggregate today — which is exactly how "six" propagated silently across seven files.
- **GAP 1 is a decision to KEEP, not a hole to close** (§2): `differential-tests.yml`'s "Run CI
  gate tests explicitly" step is a genuine soundness check (`TestCIGate::test_oracle_baseline_agreement`
  fails only on resolved-and-wrong, never on a timeout). It stays unconditionally gating; the work
  is to make that legible and pin it with a test.
- **GAP 2's `addopts` half is already resolved and documented** (§1.5, §3): do NOT add `-m` to
  `code/pyproject.toml` `addopts` — that would recreate the silent-green failure mode TESTING_GUIDE
  8.14 exists to prevent. The real gap is `run_tests.py`'s dead `TestConfig.markers` field
  (declared line 56, populated line 133 from an argparse option that does not exist), with no test
  file for `run_tests.py` anywhere in the tree.
- **GAP 3 needs ZERO classifier code changes** (§1.6, §4): `unstable_watch_classify.py`'s `main()`
  already resolves `dev_junit_path` to `DEFAULT_DEV_JUNIT_PATH = "/tmp/watch-development.xml"`, and
  the whole DEV_STATUS branch is already unit-tested. Only the producing workflow step is missing.
- **Critical correction to the task's own framing** (§1.6): the existing "exactly 2 matches of
  `-m unstable`" assertion in `test_unstable_deselection_wiring.py` is scoped to the literal
  `-m unstable` substring. Adding an `-m development` step adds ZERO matches to it. That `2` MUST
  NOT become `3`.
- **Do not edit task 173's plan file** (§1.7, §5 item 7): the canonical reconciliation already
  happened at TESTING_GUIDE 8.14's "Currently marked" paragraph, following task 153's deliberate
  precedent of not rewriting another task's historical record.

### Prior Plan Reference

No prior plan for this task. Task 153's plan
(`specs/153_assert_missing_frame_axioms_in_bimodal_semantics/plans/01_seriality-interpolation-axioms.md`)
is referenced only as precedent for two decisions this plan inherits: (1) do not rewrite another
task's plan file to reconcile a stale criterion — update the canonical source of truth instead;
(2) do not add a default `-m "not development"` to `addopts`.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no `roadmap_flag` is set. No roadmap
phases added.

## Goals & Non-Goals

**Goals**:

- Make the retained oracle soundness gate an explicit, tested, documented decision rather than an
  implicit accident (criterion (c)).
- Give `run_tests.py` a `--markers`/`-m` passthrough so the unified runner can reproduce the gating
  selection and explicitly select the in-development set (criterion (b) via the unified entry point).
- Wire the `-m development` producing step in `unstable-watch.yml` so bimodal regressions are
  VISIBLE-but-non-gating in the nightly observer.
- Make the gating-invocation count executable so it cannot drift again, and correct all seven stale
  "six" claims.
- Correct the four false claims in `.github/workflows/README.md` and the contradictory comment block
  in `tests.yml` lines 102-113.
- End with an executable/recorded proof of criteria (a) scoped-to-completeness, (b), and (c).

**Non-Goals**:

- Changing bimodal's semantics, frame-class constraints, operators, or examples.
- Adding `-m` to `code/pyproject.toml`'s `addopts` (explicitly rejected — §1.5, §3).
- Weakening `differential-tests.yml`: no `continue-on-error`, no narrowing of its `paths:` trigger,
  no deselection of `TestCIGate`.
- Removing bimodal from `AVAILABLE_THEORIES` or from the wheel.
- Weakening, skipping, or deselecting any logos, exclusion, imposition, or core test.
- Removing any of the three containment tests — they are extended, never deleted or narrowed.
- Editing `specs/173_add_development_marker_for_in_progress_theories/plans/01_development-marker.md`.
- Fixing bimodal's 5 known failing tests (out of scope; they are accepted and non-gating).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Guard tests written against already-true state are vacuous (pass without asserting anything real) | H | H | Every guard assertion in Phases 1-3 requires recorded RED evidence via temporary mutation of the asserted file, then revert. No phase closes without that transcript. |
| Implementer changes the existing "exactly 2 `-m unstable`" assertion to 3 | H | M | Called out as a MUST NOT in Phase 3's tasks, in Non-Goals, and re-asserted in Phase 6's verification (`git diff` on that assertion must be empty). |
| A prose-only edit accidentally crosses out of a comment/string boundary in `conftest.py` or a YAML `run:` block | H | L | Phase 1 and 2 run the full `code/tests/ci/` suite; Phase 3 additionally parses the modified YAML. |
| `run_tests.py --markers` plumbing misses one of the five command-building sites, leaving a silently-unfiltered path | M | M | Phase 4's tests parametrize over all five sites explicitly before implementation; Scope Hypothesis requires re-deriving the site list by grep, not trusting the report's line numbers. |
| Adding `-m` to `run_tests.py` argparse collides with an existing short flag | M | L | Report §1.5 enumerated every `add_argument` call: only `-v` and `-x` exist. Phase 4 re-confirms by grep before adding. |
| The new `unstable-watch.yml` step breaks the workflow's YAML or the classifier's input contract | M | L | Phase 3 verifies the YAML parses and that the local `-m development` selection collects the expected non-zero count before the step is considered done. |
| Correcting "six" -> "seven" misses an occurrence or corrects an unrelated "six" | M | M | Phase 1's Scope Hypothesis requires an independent repo-wide grep, and the new docs-consistency assertion fails on any surviving stale claim in the anchored files. |
| `./run_tests.py bimodal` exits non-zero after Phase 4 and is mistaken for a regression | M | M | This is the intended, pre-existing behavior (5 known bimodal failures) and is criterion (b) working as designed. Stated explicitly in Phase 4's tasks so it is not "fixed". |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 4, 5 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 6 | 1, 2, 3, 4, 5 |

Phases within the same wave can execute in parallel. Phases 1, 2, and 3 are serialized against each
other solely because all three edit `code/tests/ci/test_unstable_deselection_wiring.py` — they have
no logical dependency beyond that shared file territory.

---

### Phase 1: Make the gating-invocation count executable and correct "six" to "seven" [COMPLETED]

**Goal**: The aggregate count of `-m`-bearing gating invocations is asserted by a real test, and
every documentation site that states the number states seven.

**Tasks**:

- [ ] RED: add `test_total_gating_marker_expression_count_is_seven` to
      `TestGatingInvocationsDeselectQuarantineMarkers` in
      `code/tests/ci/test_unstable_deselection_wiring.py`, deriving the count from `_SCANNED_FILES`
      by counting invocations for which `_MARKER_EXPR_RE.search(inv)` is not None, against a
      module-level `EXPECTED_GATING_MARKER_INVOCATIONS = 7`. Record RED evidence by temporarily
      setting the constant to `6`, running the test, capturing the failure, then restoring `7`.
      Do NOT modify `test_scanned_invocation_counts_match_known_shape` — its per-file counts
      (2/2/2/2 = 8 invocations, one of which legitimately carries no `-m`) remain correct.
- [ ] RED: add a docs-consistency assertion (a second new test in the same class) parametrized over
      the anchor files below, asserting each contains the corrected seven-claim and contains no
      surviving "six"-worded gating-invocation claim. This test is genuinely RED before the prose
      edits land — capture that failure before fixing anything.
- [ ] GREEN: correct "six" -> "seven" at the seven anchors reported in §5 item 6:
      `code/docs/core/TESTING_GUIDE.md` lines 972, 1388, 1391, 1487;
      `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` line 25;
      `code/src/model_checker/theory_lib/bimodal/tests/README.md` line 10;
      `code/tests/ci/test_development_marker_application.py` line 13.
- [ ] Add one sentence to TESTING_GUIDE 8.14's "Where the deselection is wired" paragraph,
      immediately after the (now-corrected) "Seven invocations in total", recording §1.3 /
      §5 item 8: two of the seven live in `oracle/run-oracle-suite.sh`, which is invoked by no
      workflow — it is a manual `nix develop --command bash oracle/run-oracle-suite.sh` driver, and
      those two carry the filter so a local gating-reproduction run does not get a false red from an
      in-development theory.
- [ ] Confirm every edit at the four `conftest.py`/`README.md`/`test_*.py` anchors lies strictly
      inside a comment, docstring, or markdown region.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: The plan asserts (i) exactly seven documentation anchors carry a stale "six"
claim and (ii) the true aggregate `-m`-bearing invocation count is seven. Confirm (i) at
implementation time with an independent repo-wide grep (e.g.
`grep -rni "six" --include='*.md' --include='*.py' --include='*.yml' --include='*.nix' --include='*.sh' . | grep -vi specs/`)
and reconcile any occurrence not in the seven-item list — correct it if it is a gating-invocation
claim, leave it if it is unrelated. Confirm (ii) by running the new count test and by reading each
of the four scanned drivers directly, not by trusting this plan's number.

**Files to modify**:

- `code/tests/ci/test_unstable_deselection_wiring.py` - two new test methods plus one module-level
  constant; existing assertions untouched
- `code/docs/core/TESTING_GUIDE.md` - four count corrections plus the manual-driver sentence
- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` - comment count correction only
- `code/src/model_checker/theory_lib/bimodal/tests/README.md` - count correction only
- `code/tests/ci/test_development_marker_application.py` - docstring count correction only

**Verification**:

- `PYTHONPATH=code/src pytest code/tests/ci/ -v` passes with the two new tests present.
- RED transcripts recorded for both new tests (constant flipped to 6; prose test run before the
  prose fix).
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ --collect-only -q`
  still collects the same count as before the conftest comment edit (proves the comment edit did
  not cross into code).

---

### Phase 2: Record and enforce the retained oracle soundness gate (GAP 1) [NOT STARTED]

**Goal**: The decision that `differential-tests.yml` stays unconditionally gating for bimodal edits
is stated where a reader of that workflow will see it, and is enforced by three assertions that fail
if anyone silently weakens it. Satisfies criterion (c).

**Tasks**:

- [ ] RED: add three assertions to `code/tests/ci/test_unstable_deselection_wiring.py` (new methods
      on the existing class, or a new sibling class in the same file — do not create a new file, this
      file already owns this workflow's contract):
      1. the "Run CI gate tests explicitly" step carries no `continue-on-error` key;
      2. `TestCIGate` is present among the node-id-selected classes in that step (the existing
         `test_differential_tests_yml_gate_step_has_no_marker_expression` only asserts
         `TestGatingConclusiveScan` is ABSENT — add the positive assertion, do not modify that test);
      3. the workflow's `paths:` trigger still includes both `oracle/bimodal_logic/**` and
         `code/src/model_checker/theory_lib/bimodal/**`, on both the `push` and `pull_request`
         triggers.
- [ ] Use regex/text extraction, not `yaml.safe_load` — PyYAML is not an installed dependency in
      either CI toolchain, as both `test_workflow_parity.py` and this file's own docstring state.
- [ ] Record RED evidence for each of the three: temporarily (a) add `continue-on-error: true` to the
      gate step, (b) remove the `::TestCIGate` node id, (c) delete one `paths:` entry — confirming
      each mutation fails the matching assertion — then revert all three. `git diff` on
      `.github/workflows/differential-tests.yml` must show only the intended comment addition
      afterwards.
- [ ] GREEN: add a comment block immediately above the "Run CI gate tests explicitly" step in
      `.github/workflows/differential-tests.yml` stating: this step is unconditionally gating for
      bimodal edits BY DESIGN; it is a soundness check, not a completeness check; it is distinct from
      the `code/`-tree `development` blanket, which quarantines only completeness claims; it must
      never gain `continue-on-error`, lose `TestCIGate`, or have its `paths:` trigger narrowed; and
      `code/tests/ci/test_unstable_deselection_wiring.py` enforces all three.
- [ ] Add a paragraph to `code/docs/core/TESTING_GUIDE.md` section 8.14 documenting plainly why a
      bimodal-only edit legitimately gates on `differential-tests.yml`: the marker quarantines
      completeness claims about the `code/`-tree implementation, never semantic-correctness claims,
      and `TestCIGate::test_oracle_baseline_agreement` fails only on a real semantic disagreement
      (resolved-and-wrong), never on a timeout.
- [ ] State the scoped reading of criterion (a) in that same paragraph: a bimodal-only change cannot
      turn any *completeness* check red; the oracle soundness gate is the one deliberate,
      named, tested exception.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: The plan asserts the gate step node-id-selects exactly six classes and that
`paths:` lists exactly two globs on each of two triggers. Confirm both by reading
`.github/workflows/differential-tests.yml` directly at implementation time; if the shape has
changed, assert the shape actually present rather than the shape this plan names.

**Files to modify**:

- `code/tests/ci/test_unstable_deselection_wiring.py` - three new assertions
- `.github/workflows/differential-tests.yml` - comment block only, no functional change
- `code/docs/core/TESTING_GUIDE.md` - section 8.14 soundness-vs-completeness paragraph

**Verification**:

- `PYTHONPATH=code/src pytest code/tests/ci/ -v` passes.
- Three RED transcripts recorded and all three mutations reverted.
- `git diff .github/workflows/differential-tests.yml` shows comment lines only — no change to any
  `run:`, `paths:`, or step key.

---

### Phase 3: Wire the `-m development` producing step in unstable-watch.yml (GAP 3) [NOT STARTED]

**Goal**: `/tmp/watch-development.xml` is produced, so the already-implemented `DEV_STATUS`
classifier path receives real input and bimodal regressions become visible-but-non-gating in the
nightly observer.

**Tasks**:

- [ ] RED: add a new test method asserting the new step's shape — selects `-m development`, writes
      `--junitxml=/tmp/watch-development.xml`, is `continue-on-error: true`, and tolerates exit codes
      0 and 5. Use a dedicated narrow regex (mirroring the existing
      `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable` approach), not
      `_extract_pytest_invocations` — that workflow's classify step embeds Python prose the general
      extractor false-positives on. Confirm RED before touching the workflow.
- [ ] **MUST NOT** change `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable`'s
      `assert len(matches) == 2`. That regex matches the literal `-m unstable` substring; an
      `-m development` step adds zero matches. The `2` is correct and stays `2`.
- [ ] GREEN: add a third watch step to `.github/workflows/unstable-watch.yml`, positioned alongside
      `watch_code` and `watch_oracle`, mirroring `watch_code`'s exact shape:
      `id: watch_development`, `continue-on-error: true`, `cd code`, `set +e`,
      `PYTHONPATH=src pytest tests/ src/model_checker -m development -v --junitxml=/tmp/watch-development.xml`,
      capture `$?` into `$GITHUB_OUTPUT` as `exit_code`, exit 0 on code 0 or 5, else exit the code.
      Include a comment explaining the exit-5 tolerance (it would only fire if the bimodal blanket
      were removed without replacement — the 8.14 "Exit path" graduation trigger).
- [ ] Make NO changes to `.github/scripts/unstable_watch_classify.py`. Confirm by reading
      `main()` that it already calls `run()` with no explicit `dev_junit_path`, resolving to
      `DEFAULT_DEV_JUNIT_PATH`.
- [ ] Verify the modified YAML still parses (use PyYAML if locally available; otherwise confirm the
      new step's indentation matches `watch_code`'s exactly, character for character).

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: The plan asserts `unstable-watch.yml` has exactly two watch steps today and
that `-m development` over `tests/ src/model_checker` collects a non-zero count (313 at the time of
the research report). Confirm the step count by reading the file, and confirm the collection count by
running `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m development --collect-only -q`
and recording the actual number — assert what you observe, not 313.

**Files to modify**:

- `.github/workflows/unstable-watch.yml` - one new step
- `code/tests/ci/test_unstable_deselection_wiring.py` - one new test method

**Verification**:

- `PYTHONPATH=code/src pytest code/tests/ci/ -v` passes, including the unchanged "exactly 2" test.
- RED transcript recorded for the new step-shape test.
- `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m development --collect-only -q`
  collects a non-zero count, recorded.
- `PYTHONPATH=code/src pytest code/tests/ci/test_unstable_watch_classifier.py -v` still passes
  (classifier untouched).
- `git diff` confirms `.github/scripts/unstable_watch_classify.py` is unmodified.

---

### Phase 4: `run_tests.py --markers`/`-m` passthrough with a new TDD test module (GAP 2) [NOT STARTED]

**Goal**: The unified runner can reproduce the gating selection and explicitly select the
in-development set, with the dead `TestConfig.markers` field finally wired — and with the
default-unfiltered behavior locked down by test so criterion (b) cannot silently regress.

**Tasks**:

- [ ] Re-derive the plumbing sites by grep rather than trusting line numbers: locate every place a
      pytest command list is built in `code/run_tests.py` (report §1.5 names
      `_run_logos_example_tests`, `_run_standard_example_tests`, the logos unit-test path, the
      standard unit-test path, and `_build_pytest_command`). Confirm the count and identity of these
      sites before writing tests.
- [ ] Confirm by grep that `-m` is not already an argparse short flag in `create_argument_parser()`
      (report §1.5: only `-v` and `-x` exist).
- [ ] RED: create `code/tests/ci/test_run_tests_markers.py` — a genuinely new module, no test file
      for `run_tests.py` exists anywhere in the tree. Load `code/run_tests.py` by path (it is a
      script, not a package module). Assert, before any implementation:
      1. the parser accepts `--markers "not development"` and its `-m` short form, and
         `TestConfig.markers` receives the value;
      2. for each of the command-building sites identified above, the built command contains
         `-m <expr>` when markers are supplied;
      3. for each of those same sites, the built command contains NO `-m` token at all when markers
         are not supplied — this is the regression guard on "stays runnable and failing by default";
      4. `--markers` has no default value (a bare invocation leaves `config.markers` falsy).
- [ ] Confirm all four assertion groups are RED before implementing.
- [ ] GREEN: add `--markers`/`-m MARKER_EXPR` to `create_argument_parser()` as a plain passthrough
      with no default, and thread `config.markers` through every command-building site so `-m <expr>`
      is appended only when supplied.
- [ ] Add the two canonical invocations to `create_argument_parser()`'s `epilog` (it already exists
      at line ~928): `./run_tests.py bimodal --markers "not development"` (reproduce the gate) and
      `./run_tests.py bimodal --markers development` (explicitly select the in-development set).
- [ ] Do NOT touch `code/pyproject.toml`'s `addopts` — see Non-Goals.
- [ ] Record, do not "fix", that `./run_tests.py bimodal` with no `--markers` still runs the full
      bimodal suite and exits non-zero on bimodal's 5 known failures. That is criterion (b) working
      as intended and is the behavior assertion group 3 above protects.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: The plan asserts five command-building sites in `code/run_tests.py` and that
the script has no importers (so a new CLI flag has no downstream call sites to update). Confirm the
site count by grep at implementation time and adjust the parametrized test list to what is actually
present; confirm the no-importers claim with
`grep -rn "run_tests" code/ --include='*.py' | grep -v "^code/run_tests.py"` and enumerate any hit as
a direct dependent to rebuild.

**Files to modify**:

- `code/tests/ci/test_run_tests_markers.py` - NEW test module
- `code/run_tests.py` - argparse option, per-site `-m` threading, epilog examples

**Verification**:

- `PYTHONPATH=code/src pytest code/tests/ci/test_run_tests_markers.py -v` passes; RED transcript
  recorded for all four assertion groups.
- `cd code && ./run_tests.py bimodal --markers "not development"` runs and reports zero bimodal tests
  selected, exiting 0.
- `cd code && ./run_tests.py bimodal --markers development` selects the in-development set.
- `cd code && ./run_tests.py bimodal` still runs the full suite with a real exit code (expected
  non-zero — recorded, not fixed).
- `cd code && ./run_tests.py logos` unchanged in behavior (no `-m` emitted).
- `git diff code/pyproject.toml` is empty.

---

### Phase 5: Correct the false claims in .github/workflows/README.md and tests.yml [NOT STARTED]

**Goal**: The workflow documentation states the real filter expression and the real worker count, and
`tests.yml`'s comment block no longer contradicts its own filter.

**Tasks**:

- [ ] `.github/workflows/README.md` lines 22-23: replace `-m "not packaging"` at `-n 6` with the real
      five-clause expression
      `-m "not packaging and not performance and not unstable and not xdist_serial and not development"`
      and `-n 4`.
- [ ] `.github/workflows/README.md` line 26: same filter correction for the `flake-check` /
      `checks.default` description.
- [ ] `.github/workflows/README.md` lines 54-58: the "Why `-n 6` and never xdist's auto worker-count
      mode" bullet — correct `-n 6` to `-n 4` (both `tests.yml:187` and `flake.nix:179` use `-n 4`,
      changed on measured evidence per `tests.yml`'s own comment at lines 51-59 and 115-132).
- [ ] `.github/workflows/README.md` lines 60-62: correct both the filter and the worker count, and
      note that `flake.nix`'s invocation also carries `--timeout=300 --timeout-method=thread`.
- [ ] Consider consolidating the four passages into one accurate restatement, since they currently
      repeat the same two errors four times (report §5 item 4).
- [ ] `.github/workflows/tests.yml` lines 102-113: reword the "this job deliberately does NOT exclude
      bimodal" claim. Do NOT simply delete it — the underlying point (bimodal is not filtered out of
      *collection*; the cross-toolchain coverage is real) is still true. Restate it as: bimodal's
      tests still execute and report here, but are gating-excluded via the `development` marker,
      consistent with 8.14's "quarantines without hiding or skipping it" framing.
- [ ] Verify every changed number and expression against the source line, not against this plan.

**Timing**: 45 minutes

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: The plan asserts five specific passages carry false claims, at
`.github/workflows/README.md` lines 22-23, 26, 54-58, 60-62 and `.github/workflows/tests.yml` lines
102-113, and that the true values are the five-clause expression and `-n 4`. Confirm each line
anchor and each true value by reading `.github/workflows/tests.yml:187` and `flake.nix:179` directly
before editing; also grep the README for any further `-n 6` or single-clause-filter occurrence beyond
the four listed.

**Files to modify**:

- `.github/workflows/README.md` - four passages
- `.github/workflows/tests.yml` - comment block only, lines ~102-113

**Verification**:

- Diff read-through confirming every changed hunk lies inside markdown prose or a `#` comment.
- `git diff .github/workflows/tests.yml` shows comment lines only — no change to the `run:` block or
  the `-m` expression at line 187.
- `PYTHONPATH=code/src pytest code/tests/ci/test_workflow_parity.py -v` passes (parity contract
  unaffected).

---

### Phase 6: Document the canonical invocations and prove criteria (a), (b), (c) [NOT STARTED]

**Goal**: The two `run_tests.py` invocations are documented alongside the existing raw-pytest ones,
and each of the three verification criteria has a recorded proof.

**Tasks**:

- [ ] Document `./run_tests.py bimodal --markers "not development"` and
      `./run_tests.py bimodal --markers development` side by side with the existing raw-pytest
      equivalents in `code/src/model_checker/theory_lib/bimodal/tests/README.md`'s "Running the
      Tests" section and in `code/docs/core/TESTING_GUIDE.md` section 8.14 (which already documents
      the raw-pytest gating reproduction).
- [ ] Give the local gating-reproduction command documented status in 8.14: name it explicitly as the
      supported way to reproduce the gating drivers' selection locally.
- [ ] Record the task-173 pointer note in this task's own summary artifact (NOT by editing
      `specs/173_.../plans/01_development-marker.md`): if task 173 is ever resumed to close its
      Phase 6, that dispatch must either strike or re-scope its "`pytest --collect-only -m development
      -q` collects zero tests" criterion to "zero tests outside the authorized bimodal blanket"
      before it can be checked off. TESTING_GUIDE 8.14's "Currently marked" paragraph is already the
      correct, current source of truth.
- [ ] Criterion (a) proof (scoped to completeness checks, per §6): run both gating passes and record
      that bimodal contributes zero selected tests to either —
      `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial and not development" --collect-only -q`
      and the `xdist_serial` serial-pass equivalent. Record the deliberate exception: the oracle
      soundness gate, now named, documented, and tested in Phase 2.
- [ ] Criterion (b) proof: record that `cd code && ./run_tests.py bimodal` runs the full bimodal
      suite with a real, non-zero exit code on its known failures, and that
      `PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/ -v` reports them visibly.
- [ ] Criterion (c) proof: point at Phase 2's three assertions and their recorded RED transcripts.
- [ ] Confirm the containment tests still exist and were extended, not narrowed:
      `test_development_marker_application.py`, `test_unstable_deselection_wiring.py`,
      `test_workflow_parity.py` — and that
      `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable`'s `== 2` is
      unchanged.
- [ ] Run the full gate set (see Testing & Validation below) and record results.

**Timing**: 1.25 hours

**Depends on**: 1, 2, 3, 4, 5

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/tests/README.md` - runner invocations
- `code/docs/core/TESTING_GUIDE.md` - section 8.14 runner invocations and documented-status note
- `specs/177_bimodal_in_development_status_and_ci_non_gating/summaries/01_*.md` - criteria proofs and
  the task-173 pointer note

**Verification**:

- All commands under Testing & Validation run and recorded.
- Each of criteria (a), (b), (c) has a named command transcript or a named test.
- `git status` shows no modification to `specs/173_add_development_marker_for_in_progress_theories/`.

---

## Testing & Validation

- [ ] `cd code && PYTHONPATH=src pytest tests/ -v` — full `code/tests/` suite green.
- [ ] `cd code && PYTHONPATH=src pytest tests/ci/ -v` — every CI contract test green, including all
      new assertions from Phases 1-4.
- [ ] Gating parallel pass:
      `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial and not development" -n 4 -q`
      — exit 0, zero bimodal tests selected.
- [ ] Gating serial pass:
      `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable and not development" -q`
      — exit 0.
- [ ] `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m development --collect-only -q` —
      collects the full bimodal set (non-zero, count recorded).
- [ ] `cd code && PYTHONPATH=src pytest src/model_checker/theory_lib/logos src/model_checker/theory_lib/exclusion src/model_checker/theory_lib/imposition -q`
      — unchanged, zero new failures (no other theory weakened).
- [ ] `cd code && ./run_tests.py bimodal --markers "not development"` — zero bimodal tests, exit 0.
- [ ] `cd code && ./run_tests.py bimodal` — full suite, real exit code (non-zero expected).
- [ ] `git diff` confirms `code/pyproject.toml`, `.github/scripts/unstable_watch_classify.py`, and
      `specs/173_*/` are all unmodified.
- [ ] `git diff` confirms the `assert len(matches) == 2` in
      `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable` is unchanged.
- [ ] RED transcripts exist for every new assertion added in Phases 1-4.

## Artifacts & Outputs

- `code/tests/ci/test_run_tests_markers.py` (new) — TDD coverage for the `--markers` passthrough.
- `code/tests/ci/test_unstable_deselection_wiring.py` (extended) — executable seven-count, docs
  consistency, three GAP-1 soundness-gate assertions, one GAP-3 step-shape assertion.
- `code/run_tests.py` (modified) — `--markers`/`-m` argparse option, per-site threading, epilog.
- `.github/workflows/unstable-watch.yml` (modified) — new `watch_development` step.
- `.github/workflows/differential-tests.yml` (modified) — soundness-gate decision comment block.
- `.github/workflows/tests.yml` (modified) — corrected comment block.
- `.github/workflows/README.md` (modified) — corrected filter expression and worker count.
- `code/docs/core/TESTING_GUIDE.md` (modified) — seven-count corrections, manual-driver sentence,
  soundness-vs-completeness paragraph, runner invocations.
- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` and `.../tests/README.md` (modified) —
  count corrections and runner invocations.
- `specs/177_bimodal_in_development_status_and_ci_non_gating/summaries/01_*.md` — criteria proofs and
  the task-173 pointer note.

## Rollback/Contingency

Every phase is an independently committable green milestone, so rollback is per-phase
`git revert` of that phase's commit(s):

- Phases 1, 2, 5 are prose plus additive test assertions — reverting them restores the previous
  (inaccurate but functional) documentation with zero behavioral change.
- Phase 3 is one additive, `continue-on-error: true` workflow step. If it misbehaves in CI, delete
  the step and its guard test; the classifier returns to its previously inert state with no other
  effect (no other step consumes `/tmp/watch-development.xml`).
- Phase 4 is the only production-code change. `--markers` has no default, so reverting it restores
  exactly today's behavior at every call site; the new test module is deleted alongside it.
- No phase modifies bimodal semantics, `AVAILABLE_THEORIES`, wheel contents, `code/pyproject.toml`,
  or the classifier script, so no rollback can affect the shipped package.
- If Phase 2's soundness-gate mutations are ever left un-reverted, `git diff
  .github/workflows/differential-tests.yml` at Phase 6 catches it before task completion.
