# Implementation Plan: Task #179

- **Task**: 179 - Make the CI pipeline fast and fully green by excluding bimodal until it is finished
- **Status**: [IMPLEMENTING]
- **Effort**: 4.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/179_ci_pipeline_exclude_bimodal_until_finished/reports/01_ci-pipeline-bimodal-exclusion-research.md
- **Artifacts**: plans/01_ci-fast-green-bimodal-excluded.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The `development`-marker work this task builds on is already landed (bimodal tree blanket, oracle
tree blanket minus the six `_SOUNDNESS_CORE_CLASSES`, `and not development` on every gating `-m`
expression, guard suite green at 136 tests). What remains is: collapse the now-proven redundancy
in `.github/workflows/differential-tests.yml` (two pytest steps selecting the byte-identical same
49 node ids), record the open keep-or-drop decision on the 49-test oracle soundness gate with its
rationale, correct three stale/contradictory passages in `TESTING_GUIDE.md` section 8.14, and
record measured before/after gating-CI wall clocks rather than an impression.

The redundancy collapse is one edit that spans a workflow file, an executable guard test's
constants and assertions, and eight prose "seven"-count occurrences; it is planned as a single
atomic-batch phase so `code/tests/ci/test_unstable_deselection_wiring.py` never sits red between
commits.

### Research Integration

Findings carried directly into this plan (verified independently while planning, not re-derived
from prose alone):

- Both `differential-tests.yml` pytest steps select the same 49 node ids (`--collect-only` diff,
  zero output). Deleting the first step ("Run differential tests (non-slow, no BimodalHarness)")
  loses nothing and does not touch the protected second step: `_gate_step_block()` in
  `code/tests/ci/test_unstable_deselection_wiring.py` anchors on `- name: Run CI gate tests
  explicitly` and `_trigger_block()` on the `on:` triggers — neither reads the first step.
- Follow-on bookkeeping confirmed by direct file read: `EXPECTED_GATING_MARKER_INVOCATIONS = 7`
  (line 51), `assert len(_invocations_for(DIFFERENTIAL_TESTS_YML)) == 2` (line 212), and the
  seven `_SEVEN_COUNT_ANCHORS` entries (lines 74-112).
- **Planning-time addition to the research's list**: `TESTING_GUIDE.md` line 1441 ("Two of those
  seven live in `oracle/run-oracle-suite.sh`") states the same aggregate count but is **not** one
  of the seven anchored strings, so the anchor test would not catch it going stale. The same
  paragraph's phrase "`.github/workflows/differential-tests.yml`'s first invocation" (line ~1436)
  also becomes false once the first invocation is deleted. Both must change with the rest.
- **Second planning-time addition**: `TESTING_GUIDE.md` line 1411 states the `development` marker
  is "**deliberately not mirrored** into `oracle/conftest.py` ... so no oracle-tree test can
  register or claim `development`". That is now flatly contradicted by the same section's own
  lines 1504-1533 (the oracle blanket, `_SOUNDNESS_CORE_CLASSES` exemption) and by
  `oracle/conftest.py` lines 93-177, which register and apply the marker. Section 8.14 currently
  contradicts itself; the decision-record phase fixes it.
- Baseline CI wall clocks (most recent pushed run, pre-oracle-blanket): `tests.yml` total 6m16s,
  bounded by `nix flake check` at 6m12s (not the 3-version Python matrix at ~3m45-3m56s per leg);
  `differential-tests.yml` total 8m22s (4m56s + 3m14s across the two now-redundant steps).
- `unstable-watch.yml` is `schedule` + `workflow_dispatch` only, all three watch steps
  `continue-on-error: true`, deliberately excluded from `_SCANNED_FILES`. No change needed.

### Prior Plan Reference

No prior plan. This is the first plan for this task.

### Roadmap Alignment

`specs/ROADMAP.md` was read for context only (not modified, and no roadmap phases are added —
no `roadmap_flag` in the delegation context). Two Phase 1 items are adjacent:

- *"Oracle differential-suite cadence decision"* — still open. This task does **not** close it:
  it removes a proven-duplicate step, which is a cost reduction, not a cadence change. The
  push/PR trigger and its `paths:` filter stay exactly as they are (and must, per the guard test).
- *"Merge and publish 1.3.0"* [USER-ONLY] — benefits from a fast, green gating pipeline, but this
  task performs no publish, push, tag, or PR step.

## Goals & Non-Goals

**Goals**:
- Remove the measured redundancy in `differential-tests.yml` without weakening the unconditional
  soundness gate, keeping the guard suite green at every commit boundary.
- Resolve and record, explicitly and with rationale, whether the 49-test oracle soundness gate
  keeps running while bimodal is in development.
- Repair `TESTING_GUIDE.md` section 8.14's three stale/contradictory passages so a future reader
  is not misled about where `development` is wired or what the oracle tree does.
- Record measured gating-CI wall clocks (before, and every "after" number obtainable without a
  push), plus the exact command the repo owner runs to capture the authoritative post-push number.

**Non-Goals**:
- Re-doing the already-landed `development`-marker work (bimodal blanket, oracle blanket, marker
  registration, `and not development` on gating expressions). Verify it holds; do not redo it.
- Investigating why `nix flake check`'s `checkPhase` (~5m14s) is ~50% slower than the equivalent
  step on a Python-matrix leg (~3m25s) for the same test population. Recorded as an out-of-scope
  follow-up; not fixed here, and never "fixed" by widening a budget.
- Any change to `unstable-watch.yml`, to `GATING_RECHECK_SOLVE_TIMEOUT_MS`, to
  `MIN_CONCLUSIVE_GATING_FORMULAS`, to any `--timeout` value, or to any assertion's strength.
- Pushing, tagging, opening a PR, or running a release step. Local commits only.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Guard suite sits red between commits while the 7->6 edit is half-applied | H | H if split | Phase 4 is `atomic-batch`: workflow + constants + assertions + all prose in one objective, one commit, verified green before committing |
| New 8.14 prose accidentally reproduces an anchor's `must_not_contain` string, turning the anchor test red | M | M | Before writing prose, re-read the live `_SEVEN_COUNT_ANCHORS` values and avoid every `must_not_contain` phrase verbatim; run the ci suite after each prose edit |
| An unanchored count occurrence is missed (e.g. "Two of those seven"), leaving 8.14 self-contradictory with no test catching it | M | M | Phase 4 does a `grep -rni "seven"` sweep over `code/ .github/ oracle/ flake.nix` and classifies every hit as in-scope or unrelated before editing |
| Deleting the first workflow step silently drops coverage | H | L | `--collect-only` diff (Phase 1) is the evidence; re-run it in Phase 5 against the surviving step and assert the same 49 node ids |
| Deleting the step discards its `--timeout=1500` / `GATING_RECHECK_SOLVE_TIMEOUT_MS` rationale comment | M | M | Confirm before deleting that `test_cross_oracle_differential.py`'s constant carries the full justification in its own comment (the workflow comment explicitly defers to it); do not modify the constant |
| Local Z3 timing runs are slow or time out on a contended machine and get misread as a regression | M | H | Every timing run in this plan is explicitly NON-GATING. Per TESTING_GUIDE 8.6, a contended machine is fixed by re-running idle, never by widening a budget. A missing local number is recorded as "not obtained", never fabricated |
| An "after" CI wall clock is fabricated because no push is permitted | H | M | Phases 5-6 record only what was actually measured, and hand the repo owner the exact `gh run view` command to capture the authoritative post-push number |
| A TESTING_GUIDE edit cites a task number, violating `.claude/rules/no-task-references-in-deliverables.md` (blocking write-time hook) | M | M | All prose outside `specs/**` cites durable anchors only: workflow step names, class names, file paths — never "task N" |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Verify inherited state and record the pre-change baseline [COMPLETED]

**Goal**: Confirm the already-landed `development` work still holds, re-confirm the
differential-tests.yml redundancy with `--collect-only`, and write down the measured "before"
numbers before anything changes.

**Tasks**:
- [ ] Confirm `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` still applies the
      path-scoped `development` blanket, and `oracle/conftest.py` still applies its blanket while
      exempting exactly the six `_SOUNDNESS_CORE_CLASSES`.
- [ ] Run `PYTHONPATH=code/src pytest code/tests/ci/ -q` and record the pass count and duration.
- [ ] Re-run the `--collect-only` comparison of `differential-tests.yml`'s two pytest steps:
      collect each step's selection with `-q --collect-only`, sort the node ids, `diff` them, and
      record that the diff is empty and the count is 49.
- [ ] Capture the historical CI baseline with `gh run view <run-id> --json jobs` for the most
      recent pushed runs of `tests.yml` and `differential-tests.yml` (run ids in the research
      report). If `gh` is unavailable or unauthenticated, record the research report's table
      verbatim and label it as sourced from the report, not re-measured.
- [ ] Optionally, as a NON-GATING observation, time one local run of the 49-item soundness core
      (the gate step's node-id selection) using a background/long-timeout bash invocation. Record
      the number, or record "not obtained (machine contention)" — never estimate it as if measured.
- [ ] Write all of the above to
      `specs/179_ci_pipeline_exclude_bimodal_until_finished/baselines/ci-wallclock-baseline.md`.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: Asserts the inherited state is 313 bimodal items marked, 595/644 oracle
items marked with 49 exempt, 136 passing tests in `code/tests/ci/`, and 49 identically-selected
node ids in both workflow steps. Confirm each number by running the command that produces it and
recording the observed value; if an observed number differs, record the observed value and stop
to reassess rather than proceeding on the planned number.

**Files to modify**:
- `specs/179_ci_pipeline_exclude_bimodal_until_finished/baselines/ci-wallclock-baseline.md` -
  new file: the recorded before-state (test counts, collect-only evidence, CI wall clocks).

**Verification**:
- The baseline file exists and every number in it is annotated with the command that produced it
  and whether it was measured locally, measured via `gh`, or carried from the research report.
- No file outside `specs/**` is modified in this phase.

---

### Phase 2: Confirm unstable-watch.yml stays non-gating [COMPLETED]

**Goal**: Close item (d) with a recorded confirmation, and make explicit that this workflow must
not become gating.

**Tasks**:
- [ ] Read `.github/workflows/unstable-watch.yml` and confirm: triggers are `schedule` +
      `workflow_dispatch` only (no `push`, no `pull_request`, no tag trigger); all three watch
      steps (`watch_code`, `watch_oracle`, `watch_development`) carry `continue-on-error: true`.
- [ ] Confirm the file appears in no other workflow's `needs:` (`grep -rn "unstable-watch"
      .github/`).
- [ ] Confirm it remains excluded from `_SCANNED_FILES` in
      `code/tests/ci/test_unstable_deselection_wiring.py`, and that
      `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable` and
      `test_watch_development_step_selects_development_and_writes_junit` both pass.
- [ ] Record the confirmation (with the grep/pytest evidence) in the Phase 1 baseline file under a
      "(d) unstable-watch.yml" heading. No workflow edit.

**Timing**: 0.25 hours

**Depends on**: none

**Verification Tier**: prose

**Files to modify**:
- `specs/179_ci_pipeline_exclude_bimodal_until_finished/baselines/ci-wallclock-baseline.md` -
  append the (d) confirmation section.

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ci/test_unstable_deselection_wiring.py -q` passes.
- `.github/workflows/unstable-watch.yml` is byte-identical to its pre-phase state
  (`git diff --stat` shows no change to it).

---

### Phase 3: Record the soundness-gate decision and repair section 8.14's stale passages [COMPLETED]

**Goal**: Resolve item (b) explicitly on the record — the 49-test oracle soundness gate **keeps
running** — and fix the two factually stale passages in the same section, without touching any
invocation-count prose (that belongs to Phase 4).

**Decision to record (this is the plan's resolution of the open decision, to be written down, not
re-litigated silently)**: **Keep the gate.** Rationale to state in the file:

1. The repo owner's directive to exclude bimodal until it is finished is honored in full for
   *completeness* claims — both `development` blankets quarantine exactly those — and is
   deliberately **not** extended to this one *soundness* check, because "bimodal is incomplete"
   and "bimodal is wrong" are different claims and only the first is what the directive is about.
2. `TestCIGate::test_oracle_baseline_agreement` fails only on a real semantic disagreement between
   the `code/`-tree implementation and the reference oracle — never on a timeout or an unresolved
   formula — so keeping it gating cannot produce the slow-and-red failure mode the exclusion was
   meant to eliminate.
3. The rejected alternative, stated so the record shows it was weighed: dropping the gate would
   require deleting
   `test_unstable_deselection_wiring.py::TestOracleSoundnessGateStaysUnconditionallyGating`, which
   exists precisely to prevent that happening by accident, and would leave no independent check
   that bimodal's semantics are correct while it is under construction.

**Tasks**:
- [ ] Add one linking sentence near the top of the "**Why a bimodal-only edit can still
      legitimately gate on `differential-tests.yml`**" paragraph (currently line ~1417) stating
      point (1) above outright in one sentence, so the reconciliation is self-evident to a reader
      who has not derived it.
- [ ] Add the rejected-alternative note (point 3) to the "Soundness stays gating" bullet under
      "*What this accepts, stated plainly*" (line ~1531).
- [ ] Fix the stale "**What it must not hide**" paragraph (line ~1411): it claims `development` is
      "deliberately not mirrored" into `oracle/conftest.py` and that "no oracle-tree test can
      register or claim `development`". Both are false today — `oracle/conftest.py` registers the
      marker (line ~93) and applies it as a tree blanket (line ~177) exempting
      `_SOUNDNESS_CORE_CLASSES`. Rewrite so the invariant it was protecting is stated in its now-
      true form: the *soundness core* is exempt from the marker, which is what keeps the
      differential harness categorically gating; the rest of the oracle tree is marked.
- [ ] Fix the stale "**The producing workflow step does not exist yet**" paragraph (line ~1464):
      `unstable-watch.yml` already has the `watch_development` step (`-m development`, writes
      `/tmp/watch-development.xml`, `continue-on-error: true`, tolerates exit 0/5) and
      `test_watch_development_step_selects_development_and_writes_junit` already asserts its shape
      and passes. Rewrite to describe the step as implemented.
- [ ] Do NOT touch any "seven"/"six" count phrasing or the "first invocation" phrase in this phase.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: local

Rationale for `local` rather than `prose`: the edits are prose, but this file is read by
executable tests (`_SEVEN_COUNT_ANCHORS` parametrizes over `TESTING_GUIDE_MD`), so a prose edit
here genuinely can turn a test red — outside `prose`'s stated blind spot. Verification is the
single guard module that consumes the file.

**Files to modify**:
- `code/docs/core/TESTING_GUIDE.md` - section 8.14: one reconciliation sentence, one
  rejected-alternative note, and two stale paragraphs rewritten.

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ci/ -q` still passes at the Phase 1 count.
- `grep -n "deliberately not mirrored\|does not exist yet" code/docs/core/TESTING_GUIDE.md`
  returns no hit inside section 8.14 for the two repaired claims.
- No occurrence of "task", a task number, or any `specs/` path was introduced into
  `TESTING_GUIDE.md` (`.claude/rules/no-task-references-in-deliverables.md`).
- `git diff` confirms only section 8.14 prose changed; no count phrasing moved.

---

### Phase 4: Collapse the differential-tests.yml redundancy (atomic batch) [COMPLETED]

**Goal**: Delete the proven-duplicate workflow step and land every follow-on bookkeeping edit in
the same commit, so the guard suite is green before and after and never in between.

**Tasks**:
- [ ] Pre-edit sweep: `grep -rni "seven" --include=*.py --include=*.md --include=*.yml
      --include=*.nix --include=*.sh --include=*.toml code/ .github/ oracle/ flake.nix` and
      classify every hit as (i) this aggregate count, or (ii) unrelated (e.g.
      `test_example_budget_floor.py`'s "seven files", `TESTING_GUIDE.md`'s "seven workflows" and
      "seven closed encoding-tuning avenues", `models/tests/conftest.py`'s `'seven'` bitvector).
      Record the classified list before editing.
- [ ] Confirm `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`'s
      `GATING_RECHECK_SOLVE_TIMEOUT_MS` comment carries the full 20000->40000 justification (the
      workflow comment about to be deleted defers to it). Do not modify the constant.
- [ ] `.github/workflows/differential-tests.yml`: delete the entire `- name: Run differential
      tests (non-slow, no BimodalHarness)` step, including its comment block. Leave the `on:`
      triggers, `paths:` filters, and the `- name: Run CI gate tests explicitly` step byte-identical.
- [ ] `code/tests/ci/test_unstable_deselection_wiring.py`:
      - `EXPECTED_GATING_MARKER_INVOCATIONS = 7` -> `6`, and update its explanatory comment
        (tests.yml 2 + flake.nix 2 + differential-tests.yml 0 + run-oracle-suite.sh 2 = 6).
      - `assert len(_invocations_for(DIFFERENTIAL_TESTS_YML)) == 2` -> `== 1`.
      - Invert every `_SEVEN_COUNT_ANCHORS` tuple's `must_contain`/`must_not_contain` so the
        anchors now require "six" and forbid the stale "seven" phrasing.
      - Rename the now-misleading identifiers so the names do not assert a false count:
        `_SEVEN_COUNT_ANCHORS` -> `_INVOCATION_COUNT_ANCHORS`,
        `test_total_gating_marker_expression_count_is_seven` ->
        `test_total_gating_marker_expression_count_matches_constant`,
        `test_seven_count_anchor_is_corrected` -> `test_invocation_count_anchor_is_current`.
        Update their docstrings to record the history in both directions: the count was once
        undercounted as "six" (a drift bug), and is now legitimately six again because a real
        invocation was removed — so a future reader does not "correct" it back to seven.
      - Re-verify `test_differential_tests_yml_gate_step_has_no_marker_expression` still passes
        unmodified (it asserts exactly one node-id-selecting invocation with no
        `TestGatingConclusiveScan`).
- [ ] Flip the prose occurrences of this aggregate count, all in the same commit:
      `code/docs/core/TESTING_GUIDE.md` (the four anchored phrases: "wired through the same seven
      invocations", "Seven invocations in total.", "across all seven.", "the seven gating `-m`
      expressions,"), plus the **unanchored** "Two of those seven live in
      `oracle/run-oracle-suite.sh`" sentence; and the three non-guide anchors in
      `code/src/model_checker/theory_lib/bimodal/tests/conftest.py`,
      `code/src/model_checker/theory_lib/bimodal/tests/README.md`, and
      `code/tests/ci/test_development_marker_application.py`.
- [ ] In `TESTING_GUIDE.md`'s "**Where the deselection is wired**" paragraph, replace
      "`.github/workflows/differential-tests.yml`'s first invocation" (now false) with the correct
      description, and add one sentence recording *why* the count dropped: the broad `-m` step was
      removed as a proven-duplicate of the node-id gate step (`--collect-only` on both selected
      the byte-identical same 49 node ids), so a future reader does not read "six" and conclude
      `development` deselection wiring regressed.
- [ ] Before committing, re-read the updated anchor values and confirm no newly written prose
      contains any `must_not_contain` string verbatim.
- [ ] Commit once, only after the full verification below is green.

**Timing**: 1.25 hours

**Depends on**: 2, 3

**Verification Tier**: full

**Commit Mode**: atomic-batch

Justification: the workflow edit, the constant, the assertion, and eight prose occurrences are
mutually load-bearing — any proper subset leaves
`test_unstable_deselection_wiring.py` red. The task brief requires exactly this batching. Per
`rules/git-workflow.md`'s Commit-Per-Green-Substep carve-out, intermediate red states are expected
and MUST NOT be committed; the declared file set below is the one objective.

**Scope Hypothesis**: Asserts six files change and that exactly eight prose occurrences state this
aggregate count (four anchored in `TESTING_GUIDE.md`, one unanchored in `TESTING_GUIDE.md`, three
in the other files) — the research report enumerated seven anchors; planning found the eighth
(unanchored) occurrence at `TESTING_GUIDE.md` line 1441. Confirm at implementation time via the
`grep -rni "seven"` sweep in the first task above; if the sweep finds a ninth in-scope occurrence,
include it in the same commit rather than deferring it.

**Files to modify**:
- `.github/workflows/differential-tests.yml` - delete the redundant first pytest step.
- `code/tests/ci/test_unstable_deselection_wiring.py` - constant 7->6, invocation assertion 2->1,
  anchor values inverted, three identifiers renamed, docstrings updated.
- `code/docs/core/TESTING_GUIDE.md` - five count occurrences, the "first invocation" phrase, and
  one new sentence recording why the count dropped.
- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` - one docstring count phrase.
- `code/src/model_checker/theory_lib/bimodal/tests/README.md` - one count phrase.
- `code/tests/ci/test_development_marker_application.py` - one docstring count phrase.

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ci/ -q` passes at the Phase 1 count (the renames and
  value flips change no test count; the anchor parametrization keeps its seven entries).
- `TestOracleSoundnessGateStaysUnconditionallyGating`'s three tests pass unmodified.
- `git diff .github/workflows/differential-tests.yml` shows only the first step removed — the
  `paths:` triggers, the `::TestCIGate` node id, and the absence of `continue-on-error` are
  untouched.
- No assertion was deleted or weakened, and no `--timeout`, `GATING_RECHECK_SOLVE_TIMEOUT_MS`, or
  `MIN_CONCLUSIVE_GATING_FORMULAS` value changed (`git diff` review).
- No task-number reference introduced outside `specs/**`.

---

### Phase 5: Post-change verification and after-measurement [COMPLETED]

**Goal**: Prove the collapse lost no coverage and record every "after" number that is obtainable
without a push.

**Tasks**:
- [ ] Re-run `--collect-only` on the surviving gate step's node-id selection and confirm it still
      selects the same 49 node ids as the Phase 1 baseline (diff the sorted lists against the
      recorded baseline list, not against a fresh re-derivation of the deleted step).
- [ ] Run the broader repo gate as a regression check:
      `PYTHONPATH=code/src pytest code/tests/ -q -m "not slow and not unstable and not development"`
      (use a long timeout or a background run; this is gating for this phase).
- [ ] Re-run `PYTHONPATH=code/src pytest code/tests/ci/ -q` and record the count and duration.
- [ ] Record the derived `differential-tests.yml` after-number: the job now runs one pass over the
      49-item soundness core instead of two, i.e. the historical 8m22s two-pass job reduces to
      roughly one pass (~3m14s at the historical rate). Label this explicitly as **derived from the
      recorded per-step baseline, not measured post-push**.
- [ ] As a NON-GATING observation, if the Phase 1 local timing of the 49-item core was obtained,
      record it again post-change for comparison. If either run was not obtained due to machine
      contention, say so; do not fabricate or interpolate. Per TESTING_GUIDE 8.6, a contended
      machine is re-run idle, never accommodated by widening a budget.
- [ ] Do NOT run `bash oracle/run-oracle-suite.sh` as a gate for this or any phase (TESTING_GUIDE
      8.8 forbids writing that into a task plan).

**Timing**: 0.75 hours

**Depends on**: 4

**Verification Tier**: full

**Scope Hypothesis**: Asserts the surviving step still selects 49 node ids and that
`code/tests/ci/` still reports its Phase 1 count. Confirm by running both commands and diffing
against the recorded baseline; a mismatch is a stop-and-reassess signal, not a number to update.

**Files to modify**:
- `specs/179_ci_pipeline_exclude_bimodal_until_finished/baselines/ci-wallclock-baseline.md` -
  append the after-state section.

**Verification**:
- The 49-node-id diff against the Phase 1 baseline is empty.
- The broader `code/tests/` gating selection is green.
- Every after-number in the baseline file is labelled measured / derived / not obtained.

---

### Phase 6: Record the CI time budget and the remaining out-of-scope follow-up [NOT STARTED]

**Goal**: Close item (c) with a recorded before/after table and an explicit statement of what only
the repo owner can measure.

**Tasks**:
- [ ] Consolidate the baseline file into one before/after table covering all three gating drivers:
      `tests.yml` (3-leg Python matrix + `nix flake check`), `differential-tests.yml`, and
      `flake.nix`'s `checks.default`.
- [ ] State plainly where `tests.yml`'s time actually goes: the workflow's wall clock is bounded by
      `nix flake check` (~6m12s, `checkPhase` ~5m14s), not by the Python matrix legs (~3m45-3m56s,
      which run concurrently). Reducing the matrix would not reduce the workflow's wall clock.
- [ ] Record the out-of-scope follow-up: `nix flake check`'s `checkPhase` is ~50% slower than the
      equivalent step on a Python-matrix leg for the same test population and marker expression
      (parity enforced by `code/tests/ci/test_workflow_parity.py`). Root cause unestablished;
      candidates are nixpkgs' Z3 build vs. the PyPI `z3-solver` wheel, sandboxed-build CPU
      allocation, and cold-cache effects. Explicitly note this must not be "fixed" by widening any
      budget.
- [ ] Record the authoritative-after procedure for the repo owner: after the local commits are
      pushed (agents must not push), capture the real numbers with
      `gh run list --workflow tests.yml --limit 1` / `gh run view <id> --json jobs` and the same for
      `differential-tests.yml`, and compare against this file's before table.
- [ ] Confirm the working tree has only the intended changes and that all commits are local
      (`git status`, `git log --oneline origin/master..HEAD`); do not push, tag, or open a PR.

**Timing**: 0.5 hours

**Depends on**: 5

**Verification Tier**: prose

**Files to modify**:
- `specs/179_ci_pipeline_exclude_bimodal_until_finished/baselines/ci-wallclock-baseline.md` -
  final consolidated before/after table and follow-up note.

**Verification**:
- The baseline file contains a complete before/after table with each cell labelled measured,
  derived, or pending-push.
- `git log` shows local commits only; no push, tag, or PR was performed.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/tests/ci/ -q` passes at the same count before and after the
      collapse, at every commit boundary.
- [ ] `TestOracleSoundnessGateStaysUnconditionallyGating` (three tests) passes unmodified.
- [ ] `test_differential_tests_yml_gate_step_has_no_marker_expression` passes unmodified.
- [ ] `test_scanned_invocation_counts_match_known_shape` passes with the updated `== 1`.
- [ ] `test_total_gating_marker_expression_count_matches_constant` passes with the constant at 6.
- [ ] Every renamed anchor test passes against the flipped "six" phrasing, in all six edited files.
- [ ] `--collect-only` on the surviving gate step selects the same 49 node ids recorded in the
      Phase 1 baseline.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q -m "not slow and not unstable and not development"`
      is green.
- [ ] No assertion deleted or weakened; no solve budget widened; `GATING_RECHECK_SOLVE_TIMEOUT_MS`
      and `MIN_CONCLUSIVE_GATING_FORMULAS` unchanged (verified by `git diff`).
- [ ] Both `development` exit paths remain documented and intact:
      `oracle/conftest.py`'s "delete the `development` half of this hook when bimodal is no longer
      in development" and the bimodal tree conftest's equivalent.
- [ ] No task-number reference introduced anywhere outside `specs/**`.

## Artifacts & Outputs

- `.github/workflows/differential-tests.yml` with the redundant first pytest step removed.
- `code/tests/ci/test_unstable_deselection_wiring.py` with the invocation count at 6, the
  per-file assertion at 1, anchors expecting "six", and three renamed identifiers.
- `code/docs/core/TESTING_GUIDE.md` section 8.14: the soundness-gate decision recorded with its
  reconciliation against the exclusion directive, two stale paragraphs repaired, and the
  invocation-count prose corrected with a note on why it dropped.
- Count-phrase updates in the bimodal tests conftest, the bimodal tests README, and
  `test_development_marker_application.py`.
- `specs/179_ci_pipeline_exclude_bimodal_until_finished/baselines/ci-wallclock-baseline.md` with
  the measured before/after table and the owner's post-push capture procedure.
- Local commits only. No push, tag, or PR.

## Rollback/Contingency

- Every phase is a separate local commit (Phase 4 is one atomic commit spanning six files), so any
  phase reverts cleanly with `git revert <sha>` without leaving the guard suite red.
- If the Phase 1 `--collect-only` diff is NOT empty (the two steps no longer select identically),
  stop: the redundancy premise has changed. Do not delete the step. Record the new selection
  difference in the baseline file and re-plan Phase 4 around what the broad step uniquely covers.
- If the `grep -rni "seven"` sweep finds an in-scope occurrence not listed in Phase 4, fold it into
  the same atomic commit rather than deferring it — a partial flip is exactly the drift the anchor
  tests exist to catch.
- If a local timing run cannot complete because of machine contention, record "not obtained" and
  proceed. Never widen a timeout, never relax an assertion, and never substitute an estimate for a
  measurement.
