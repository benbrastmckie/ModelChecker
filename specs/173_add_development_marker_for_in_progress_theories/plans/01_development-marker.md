# Implementation Plan: Add `development` pytest marker for in-progress theories

- **Task**: 173 - Add development marker for in progress theories
- **Status**: [IMPLEMENTING]
- **Effort**: 6.5 hours
- **Dependencies**: Task 158, Task 172, Task 175 (all landed; their edits to the four `-m` drivers and to `unstable_watch_classify.py` are the baseline this plan builds on)
- **Research Inputs**: `specs/173_add_development_marker_for_in_progress_theories/reports/01_development-marker-design.md`
- **Artifacts**: plans/01_development-marker.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Introduce a `development` pytest marker that lets a theory still under active construction
(bimodal today) carry known-incomplete tests without turning the package's CI red, while keeping
every marked test observed rather than forgotten. The work is CI-infrastructure-only: register
the marker, wire `and not development` into every gating `-m` expression, extend the existing
executable deselection contract, add a non-gating `DEV_STATUS` observability path to the
unstable-watch classifier, and document the whole category (including its boundaries and exit
path) in a new TESTING_GUIDE.md section. **No `theory_lib` test is marked by this task** — the
category is created without being applied, and that is stated honestly in the documentation.

Definition of done: `development` is registered and deselected from all six gating `-m`
invocations, the deselection contract test enforces that mechanically, the classifier can report
on `development`-marked tests without ever gating on them, and TESTING_GUIDE.md section 8.14
documents meaning, boundaries, wiring, observability, exit path, and marker-choice guidance.

### Research Integration

The research report (`reports/01_development-marker-design.md`) settles all six task decisions and
this plan implements its recommendations directly:

- **§1 Marker semantics** -> Phase 1's `pyproject.toml` entry text, and the per-test (not
  per-module, not per-theory `pytestmark`) granularity documented in Phase 5.
- **§2 What stays gating** -> the deliberate non-mirroring into `oracle/conftest.py` (Phase 1
  comment + Phase 5 documentation), and the defensive `and not development` in
  `run-oracle-suite.sh` (Phase 2).
- **§3 Deselection wiring** -> Phase 2's six `-m` edits plus the in-place extension of
  `test_unstable_deselection_wiring.py`.
- **§4 Observability** -> Phases 3 and 4's `DEV_STATUS` design, adapted below so it lands
  independently of any workflow-YAML change (see Scope Decisions).
- **§5 Exit path** -> Phase 5's documented per-test and theory-level exit criteria.
- **§6 Documentation** -> Phase 5's new section 8.14 with the four-marker decision table.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; `specs/ROADMAP.md` was not consulted.

## Scope Decisions (recorded, not re-openable)

These resolve the report's Section 0 gap and the orchestrator's scope ruling. Implementers must
apply them as written rather than re-deriving them.

1. **`file_scope` is widened by exactly one file: `.github/scripts/unstable_watch_classify.py`.**
   Rationale: the task's declared `file_scope` already contains
   `code/tests/ci/test_unstable_watch_classifier.py`, which loads that module by absolute path and
   whose docstring names it as its subject. Declaring a test file while excluding the module it
   tests is a task-creation oversight, not a deliberate boundary, and the task text itself names
   "extend the classifier module" as the preferred observability mechanism. This follows the same
   corollary-widening precedent used by task 158.

2. **`.github/workflows/unstable-watch.yml` is NOT edited.** The task text directs "extend the
   classifier module, never the YAML". The observability design in Phases 3-4 is therefore built
   so it lands and is fully unit-tested **without** any YAML change: the classifier gains a third,
   optional JUnit input path that simply does not exist today, so the new code path is inert in
   production until a follow-up task adds the producing step. See "Deferred `/spawn` candidate"
   below for the precise deferred change.

3. **`.github/workflows/release.yml` is NOT edited.** Its `test-and-release` no-op comment
   ("Any pytest suite added to this job in the future MUST carry `not unstable`...", and the
   `build` job's defensive `and not unstable`) would benefit from also naming `development`, and
   the task description asks for it by name. It is out of `file_scope` and belongs to tasks
   158/168. **Flagged, deliberately not done.** The implementer must record this in the
   implementation summary as a known, deliberate omission rather than silently skipping it.

4. **`oracle/conftest.py` is NOT edited, and that is the point.** That file's docstring instructs
   future editors to keep its marker mirror in sync with `code/pyproject.toml`. This task
   deliberately breaks that convention for this one marker so the differential/soundness oracle
   suite stays categorically outside the marker's reach: no oracle-tree test can legitimately
   claim `development`, because the marker is never registered there. This is a reasoned
   exception, not an oversight, and it is recorded at the two in-scope sites (the `pyproject.toml`
   marker entry's own text in Phase 1, and TESTING_GUIDE.md 8.14 in Phase 5).

### Deferred `/spawn` candidate (do not implement here)

A follow-up task should own `.github/workflows/unstable-watch.yml` plus
`code/tests/ci/test_unstable_deselection_wiring.py`, and make this change:

- Add a third watch step to `unstable-watch.yml`, mirroring the existing `watch_code` step but
  selecting `-m development` and writing `--junitxml=/tmp/watch-development.xml`, with the same
  `exit 0` tolerance for pytest exit codes 0 and 5.
- Update `test_unstable_deselection_wiring.py`'s
  `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable`, which currently
  asserts `len(re.findall(r'pytest\s+\S.*?-m\s+unstable\b', text)) == 2` against that workflow.
  A third step changes that shape and the assertion must be extended to also confirm the
  `-m development` selection.

The rest of the observability mechanism (classifier parsing, `DEV_STATUS` classification, record
schema, trend reporting) lands in this task and is unit-tested here. The deferred step is the
only thing standing between the code path and live data.

**Rejected alternative — a `DEVELOPMENT_NODEID_FRAGMENTS` registry inside the classifier**
(widening the existing `-m unstable` selection to `-m "unstable or development"`, one line per
step, and distinguishing the two sets by a static node-id list). It would be a smaller YAML delta
and matches the module's existing `MAX_TIME_BY_NODEID_FRAGMENT` idiom, but it requires keeping a
hand-maintained list in sync with the actual `@pytest.mark.development` decorators; a decorator
not present in the list would be classified `NEW`. The separate-JUnit-file design has no such
drift surface — the producing step's own `-m development` selection is the single source of truth
— and is completely inert until that step exists, which is exactly what landing independently of
the YAML requires.

## Goals & Non-Goals

**Goals**:
- Register a `development` marker in `code/pyproject.toml` with semantics distinct from
  `unstable`, `xdist_serial`, and `performance`.
- Deselect it from every gating pytest invocation across `tests.yml`, `differential-tests.yml`,
  `flake.nix`, and `oracle/run-oracle-suite.sh`.
- Make that deselection executable by extending `code/tests/ci/test_unstable_deselection_wiring.py`
  in place (not a parallel guard).
- Give `development`-marked tests a non-gating observability path in
  `.github/scripts/unstable_watch_classify.py`, unit-tested in
  `code/tests/ci/test_unstable_watch_classifier.py`.
- Document the category in a new TESTING_GUIDE.md section 8.14, including a four-marker decision
  table and a concrete exit path.

**Non-Goals**:
- Applying `development` to any test. No `theory_lib` source or test file is touched.
- Editing `.github/workflows/unstable-watch.yml`, `.github/workflows/release.yml`, or
  `oracle/conftest.py` (see Scope Decisions 2-4).
- Weakening, widening, or re-litigating the `unstable` / `xdist_serial` markers or their criteria.
- The xdist worker-crash investigation, the gating-floor investigation, or the
  `test_frame_class_mapping.py` serial-pass experiment — all owned elsewhere.
- Any change to the classify step's exit-code contract.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A `development` record silently zeroes an `unstable` test's promotion streak by feeding `any_failure` | H | M | Phase 3 makes exclusion from both `any_new` and `any_failure` an explicit, named unit test, not an incidental property |
| The new `DEV_STATUS` path changes the classify step's exit code | H | L | Phase 3 asserts the return value stays driven solely by `any_new`, with a test covering "failing dev test, zero unstable failures -> exit 0" |
| `-m "not development"` errors or warns in the oracle tree where the marker is unregistered | M | L | Phase 2 verifies by actually running `oracle/run-oracle-suite.sh`'s expressions (or an equivalent `--collect-only`) rather than assuming |
| TESTING_GUIDE.md edit collides with idle task 176, which also declares that file | M | M | Phase 5 keeps edits section-scoped: one new 8.14 block appended before `## Quick Reference`, plus at most one appended sentence in 8.9 with no restructuring |
| `test_scanned_invocation_counts_match_known_shape`'s per-file counts break | M | L | Phase 2 changes only the content of `-m` strings, never the number or shape of invocations; the count assertions stay untouched and are re-run as the check |
| The classifier's dev code path is dead in production until the deferred YAML step lands, and is then forgotten | M | M | Recorded explicitly in this plan's Deferred `/spawn` candidate section, in TESTING_GUIDE.md 8.14's observability paragraph, and required in the implementation summary |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3 | -- |
| 2 | 2, 4 | 1 (for 2), 3 (for 4) |
| 3 | 5 | 2, 4 |
| 4 | 6 | 1, 2, 3, 4, 5 |

Phases within the same wave can execute in parallel. Wave 1's two phases are territory-disjoint:
Phase 1 owns `code/pyproject.toml`; Phase 3 owns `.github/scripts/unstable_watch_classify.py` and
`code/tests/ci/test_unstable_watch_classifier.py`.

---

### Phase 1: Register the `development` marker [COMPLETED]

**Goal**: `code/pyproject.toml` declares `development` with semantics that distinguish it from
`unstable` and `xdist_serial`, and records the deliberate oracle non-mirroring at the one in-scope
site.

**Tasks**:
- [ ] Read `code/pyproject.toml`'s current `markers` list fresh (do not work from any quoted copy).
- [ ] Append a `development: ...` entry after the existing `xdist_serial` entry, matching the
      existing entries' one-line style. Its text must state: (a) the tests belong to a theory
      still under active construction, whose current failure is expected and tracked rather than a
      regression; (b) it is deselected from gating runs with `-m "not development"`; (c) it is
      distinct from `unstable` (an investigated, non-semantic instability in an otherwise-complete
      theory) and from `xdist_serial` (a routine contention classification); (d) a pointer to
      `code/docs/core/TESTING_GUIDE.md` section 8.14.
- [ ] In the same entry (or an adjacent comment), record the deliberate exception: unlike
      `xdist_serial`, this marker is **deliberately not mirrored** into `oracle/conftest.py`, so no
      oracle-tree test can claim it; the differential/soundness harness stays fully gating.
- [ ] Confirm `pytest --markers` lists `development` from the `code/` tree.

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

**Files to modify**:
- `code/pyproject.toml` - add the `development` marker entry plus the non-mirroring note

**Verification**:
- `cd code && PYTHONPATH=src pytest --markers | grep -A2 '^@pytest.mark.development'` shows the
  new entry.
- `cd code && PYTHONPATH=src pytest tests/ci/ -q` still passes (no wiring change yet, so this is a
  no-regression check only).

---

### Phase 2: Wire `and not development` into every gating invocation [NOT STARTED]

**Goal**: Every `-m`-bearing gating pytest invocation deselects `development`, and the existing
executable contract enforces it.

**Tasks**:
- [ ] Re-read all four driver files fresh and enumerate their `-m`-bearing invocations; confirm the
      Scope Hypothesis below before editing.
- [ ] Extend `code/tests/ci/test_unstable_deselection_wiring.py` **in place**:
      - Rename `TestGatingInvocationsDeselectUnstable` to
        `TestGatingInvocationsDeselectQuarantineMarkers` and update its docstring to cover both
        markers. (Verified: the class has no references outside its own file. Re-confirm with
        `grep -rn TestGatingInvocationsDeselectUnstable` before renaming.)
      - In `test_every_marker_expression_excludes_unstable`, add a second assertion over the
        **same** already-extracted `marker_expr` requiring `"not development" in marker_expr`,
        with its own failure message. Do not add a second parsing pass and do not duplicate the
        parametrization. Rename the method to name both markers.
      - Update the module docstring's opening contract statement to name both markers.
      - Leave `test_scanned_invocation_counts_match_known_shape`,
        `test_differential_tests_yml_gate_step_has_no_marker_expression`, and
        `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable` unchanged —
        parsing shape does not change, and `unstable-watch.yml` is not edited by this task.
- [ ] Add `and not development` to each of the six `-m` expressions:
      - `.github/workflows/tests.yml` parallel pass and serial pass
      - `.github/workflows/differential-tests.yml` first invocation only (the second is
        node-id-selecting with no `-m` and stays untouched, exactly as it already is for
        `unstable`)
      - `flake.nix` `checks.default` parallel pass and serial pass
      - `oracle/run-oracle-suite.sh` pass 1 and pass 2 (defensive no-op today, since the marker is
        unregistered in the oracle tree — keep it anyway for uniform contract shape and
        defence-in-depth)

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: Exactly six `-m`-bearing pytest invocations across exactly four files require
the edit (`tests.yml` x2, `differential-tests.yml` x1, `flake.nix` x2, `run-oracle-suite.sh` x2),
and `differential-tests.yml`'s second, node-id-selecting invocation requires none. Confirm at
implementation time with `grep -n '\-m "' .github/workflows/tests.yml
.github/workflows/differential-tests.yml flake.nix oracle/run-oracle-suite.sh` and by running
`test_scanned_invocation_counts_match_known_shape`, which independently asserts 2/2/2/2
invocations per file. If the count differs, stop and reconcile before editing.

**Rationale for `atomic-batch`**: the extended contract test is RED from the moment it is written
until all six driver edits land. The five-file set is pre-declared here; intermediate per-file
states are expected red and must not be committed individually.

**Files to modify**:
- `code/tests/ci/test_unstable_deselection_wiring.py` - class rename, second assertion, docstrings
- `.github/workflows/tests.yml` - 2 `-m` expressions
- `.github/workflows/differential-tests.yml` - 1 `-m` expression
- `flake.nix` - 2 `-m` expressions
- `oracle/run-oracle-suite.sh` - 2 `-m` expressions

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/ci/test_unstable_deselection_wiring.py -v` — all pass,
  including the unchanged count and `unstable-watch.yml` tests.
- Confirm the extended assertion actually bites: temporarily revert one driver's
  `and not development`, observe the test fail naming that file, then restore.
- Confirm `-m "not development"` is harmless where the marker is unregistered: run the oracle
  suite's pass-1 expression with `--collect-only -q` and confirm no error and no
  `PytestUnknownMarkWarning`-driven failure.
- `nix flake check` is not required; a syntax-only confirmation of `flake.nix` (e.g.
  `nix-instantiate --parse flake.nix`, or `nix flake show` if cheap) is sufficient.

---

### Phase 3: Classifier `DEV_STATUS` classification path [NOT STARTED]

**Goal**: `.github/scripts/unstable_watch_classify.py` can read a third, optional JUnit input of
`development`-marked results, classify each as `DEV_STATUS`, and record it — without ever
influencing `any_new`, `any_failure`, or the exit code.

**Tasks**:
- [ ] Write the unit tests first in `code/tests/ci/test_unstable_watch_classifier.py`, following
      the file's existing fixture/driving conventions (`run()` driven against `tmp_path` JUnit
      fixtures with injected `past_runs_fn` / `fetch_past_classifications_fn` fakes):
      - a failing `development`-marked test yields a record with `classification == "DEV_STATUS"`
        and its true `outcome`, and `run()` returns 0
      - the same failing dev test does **not** set `any_new` (no `::error title=UNSTABLE-WATCH:
        NEW FAILURE MODE::` annotation is emitted for it)
      - the same failing dev test does **not** feed `any_failure`, so a clean `unstable` test's
        promotion streak is unaffected — assert the streak value directly
      - a missing dev JUnit file is tolerated exactly like a missing code/oracle file (no records,
        no crash)
      - a passing dev-marked test is recorded with `outcome == "passed"` and
        `classification == "DEV_STATUS"` (not `"N/A"`), so pass/fail trend data exists for it
      - an `error` outcome (e.g. a collection-breaking `ImportError`) is recorded as `DEV_STATUS`
        too, and is still surfaced in the report rather than conflated with a semantic regression
      - a node id appearing in both the unstable and dev JUnit inputs is classified `DEV_STATUS`
        (development wins), and does not double-count
- [ ] Implement in `.github/scripts/unstable_watch_classify.py`:
      - `DEFAULT_DEV_JUNIT_PATH = "/tmp/watch-development.xml"` alongside the two existing
        defaults, with a comment stating it is produced by a workflow step that **does not exist
        yet** and naming the deferred follow-up (do not reference a task number — describe the
        change).
      - a `dev_junit_path=DEFAULT_DEV_JUNIT_PATH` parameter on `run()`; `main()` needs no change.
      - a second parse loop over `dev_junit_path` that appends records with
        `classification = "DEV_STATUS"` and the true `outcome`, and touches neither `any_new` nor
        `any_failure`.
      - collect the dev node ids seen this run into a separate list, and exclude dev records from
        the `currently_unstable` fragment-matching loop so a dev record can never supply an
        `unstable` node id's classification.
      - a module-docstring paragraph stating the `DEV_STATUS` contract: never gating, never
        signature-matched, distinct from TIMING/NEW, and why (a development-marked failure has no
        stable signature by construction — the theory's implementation is still changing).
- [ ] Run the full classifier test file and confirm every pre-existing test still passes unchanged.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase touches exactly two files
(`.github/scripts/unstable_watch_classify.py`, `code/tests/ci/test_unstable_watch_classifier.py`)
and changes exactly one public signature (`run()`, gaining one keyword argument with a default).
Confirm at implementation time that `run(` has no call sites beyond `main()` and that test file:
`grep -rn "unstable_watch_classify\|run(" code/tests/ci/test_unstable_watch_classifier.py | head`
plus `grep -rn "unstable_watch_classify" --include=* .` across the repo.

**Files to modify**:
- `.github/scripts/unstable_watch_classify.py` - new default path, `run()` parameter, dev parse
  loop, `DEV_STATUS` classification, docstring contract
- `code/tests/ci/test_unstable_watch_classifier.py` - the seven new tests above

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/ci/test_unstable_watch_classifier.py -v` — all pass,
  pre-existing tests unchanged.
- Confirm the exit-code contract explicitly: a run whose only failure is a `development` test
  returns 0.

---

### Phase 4: Development trend reporting [NOT STARTED]

**Goal**: The classifier reports, per `development`-marked node id, how many of the last N observed
runs it passed — a progress signal, never a gate — reusing the existing cross-run artifact
machinery rather than duplicating it.

**Tasks**:
- [ ] Write the unit tests first:
      - `fetch_past_classifications` with its new field selector returns `outcome` values while its
        default behaviour (returning `classification`) is byte-for-byte unchanged — assert the
        existing default path explicitly so the generalization cannot silently alter it
      - `compute_dev_pass_rate` returns `(passes, total)` counting only runs in which the node id
        has a record; a run with no record is excluded from **both** numerator and denominator (a
        missing artifact must not manufacture either progress or regression), and this run always
        counts since it comes from the JUnit input
      - the step-summary output contains a distinct Development Watch section listing each dev node
        id with its pass rate, and does **not** use the `READY TO PROMOTE` wording or the 20-run
        framing (that phrase means "the instability resolved", a different claim)
      - with no dev records at all, the summary omits the section (or states none were collected)
        and nothing else in the summary changes
- [ ] Implement:
      - add a `field="classification"` keyword parameter to `fetch_past_classifications`, used when
        extracting from each past run's JSONL record; default preserves today's behaviour exactly.
        Update its docstring.
      - add `compute_dev_pass_rate(nodeid, this_run_outcome, past_run_outcomes)` returning
        `(passes, total)`, with a docstring stating the missing-record rule and why it differs from
        `compute_per_test_promotion_streak`'s conservative streak-breaking rule (a streak is a
        promotion claim that must not be inflated; a pass rate is a progress observation that must
        not be distorted in either direction).
      - in `run()`, fetch past outcomes for this run's dev node ids via the same
        `fetch_past_classifications_fn` injection point (so tests keep working without network),
        compute each pass rate, and emit a `## Development Watch` step-summary section with a
        `| Node ID | This run | Passed in last N |` table plus a one-line statement that this
        section is informational and never gating.
      - keep the existing `## Unstable Watch` section's content and wording unchanged.
- [ ] Re-run the whole classifier test file.

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: interface

**Commit Mode**: atomic-batch

**Scope Hypothesis**: Same two files as Phase 3; one additional public signature change
(`fetch_past_classifications` gaining a defaulted keyword) and one new public function
(`compute_dev_pass_rate`). Confirm no other caller of `fetch_past_classifications` exists outside
`run()` and the test file before changing it.

**Files to modify**:
- `.github/scripts/unstable_watch_classify.py` - `field` parameter, `compute_dev_pass_rate`,
  Development Watch summary section
- `code/tests/ci/test_unstable_watch_classifier.py` - the four new tests above

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/ci/test_unstable_watch_classifier.py -v` — all pass.
- Drive `run()` end-to-end against a `tmp_path` summary file with one failing dev test and one
  clean unstable test; read the produced summary and confirm both sections are present, correct,
  and that the exit code is 0.

---

### Phase 5: TESTING_GUIDE.md section 8.14 [NOT STARTED]

**Goal**: A reader can tell what `development` means, what it must never hide, where its
deselection is wired, how it is observed, how it is retired, and how to choose between it and the
three sibling markers.

**Tasks**:
- [ ] Confirm 8.14 is still the next free subsection number and that `## Quick Reference` is still
      the section following 8.13 (see Scope Hypothesis).
- [ ] Insert `### 8.14 The \`development\` Marker` immediately after 8.13 and before
      `## Quick Reference`, mirroring 8.9's and 8.12's internal structure:
      - **What it means** — the marker definition from Phase 1, expanded.
      - **Granularity: per-test, not per-module or per-theory.** State the reasoning explicitly: a
        module-level `pytestmark` or theory-level blanket would silently deselect every test in the
        theory forever, including the ones that pass today, and is the version most capable of
        hiding a real regression. Point at the existing `UNSTABLE_EXAMPLES` set-membership idiom in
        `bimodal`'s test file as the application ergonomics to copy when many tests need marking.
      - **Entry criteria** — deliberately lighter than 8.9's four-point quarantine bar (this is a
        completeness tracker, not an investigated-defect quarantine), but not a rubber stamp:
        (a) the behaviour genuinely is not implemented yet, rather than being a workaround for a
        fixable bug elsewhere; (b) a one-line comment at the marking site naming what is missing.
      - **What it must not hide** — an explicit "must not be used for" list: differential and
        soundness-oracle tests, and any test whose pass/fail state encodes a semantic claim about
        the theory's correctness rather than its completeness. State the structural enforcement:
        the marker is **deliberately not mirrored** into `oracle/conftest.py`, breaking that file's
        own "keep in sync with pyproject.toml" convention on purpose, so no oracle-tree test can
        register or claim it.
      - **Where the deselection is wired** — name all four drivers and the six invocations, and
        name `code/tests/ci/test_unstable_deselection_wiring.py` as the executable contract. State
        the standing instruction: any new gating pytest invocation carries the filter as a matter
        of course.
      - **Observability** — describe the `DEV_STATUS` path in
        `.github/scripts/unstable_watch_classify.py`: non-gating by construction, no signature
        matching, pass-trend rather than failure-signature tracking. **State plainly that the
        producing workflow step does not exist yet**, describe the deferred change, and note the
        code path is inert until it lands.
      - **Exit path** — per-test: mechanical and immediate, the marker comes off when the behaviour
        is implemented and the test passes; no waiting window, unlike `unstable`'s 20-run
        promotion, because the marker never claimed instability. Theory-level: "no longer in
        development" means zero remaining `development`-marked tests in the theory's test tree,
        checkable with `grep -rn "pytest.mark.development"` or `pytest --collect-only -m
        development -q`. Record the 8.9 standing-rule analogue explicitly: a stalled marking is
        escalated against the theory's own milestone rather than a fixed two-month calendar window,
        because "still incomplete after two months" is not surprising for a from-scratch theory the
        way "still flaky after two months" is — and say that this deviation from 8.9 is deliberate.
      - **Marker-choice decision table** covering `development`, `unstable`, `xdist_serial`, and
        `performance` (one row each: meaning, and when to use).
      - **Currently marked** — state honestly that **no test carries `development` today**; this
        task created the category without applying it.
- [ ] Append at most **one** sentence to 8.9's "Where the deselection is wired" paragraph pointing
      to 8.14 for the sibling marker, so 8.9 does not read as if `unstable` were the only
      quarantine-style marker. Do not restructure or reflow 8.9. If a conflicting concurrent edit
      to 8.9 is observed, drop this sentence and note the omission — 8.14 is self-contained without
      it.

**Timing**: 1 hour

**Depends on**: 2, 4

**Verification Tier**: prose

**Scope Hypothesis**: `### 8.14` does not yet exist and 8.13 is the last numbered subsection before
`## Quick Reference`. Confirm with `grep -n '^### 8\.\|^## ' code/docs/core/TESTING_GUIDE.md`
before inserting. If an 8.14 has appeared (task 176 also declares this file), pick the next free
number and reconcile rather than overwriting.

**Files to modify**:
- `code/docs/core/TESTING_GUIDE.md` - new section 8.14; one appended sentence in 8.9

**Verification**:
- Every claim the new section makes about wiring is checked against the files as they now stand
  (six invocations, four drivers, the contract test's name).
- Section numbering is contiguous and `## Quick Reference` still follows the 8.x run.
- No task numbers appear anywhere in the added prose (this file is a deliverable, not a specs
  artifact) — the deferred workflow change is described, never cited by number.
- The diff touches only the inserted block and the single appended sentence in 8.9.

---

### Phase 6: Full-gate verification and deferred-item record [NOT STARTED]

**Goal**: The whole change set is verified together against the real gates, and every deliberate
omission is recorded where the next reader will find it.

**Tasks**:
- [ ] Run the full CI contract suite: `cd code && PYTHONPATH=src pytest tests/ci/ -v`.
- [ ] Run the broader in-repo suite the drivers actually gate on, using the newly edited parallel
      expression verbatim, to confirm the added filter changes nothing today (no test carries the
      marker): `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not
      performance and not unstable and not xdist_serial and not development" -n 4 -q
      --timeout=300 --timeout-method=thread`. Compare the collected count against the same command
      without `and not development`; they must be identical.
- [ ] Confirm `pytest --collect-only -m development -q` collects zero tests (the category exists,
      nothing claims it).
- [ ] Record in the implementation summary, explicitly: (a) the one-file `file_scope` widening to
      `.github/scripts/unstable_watch_classify.py` and its reasoning; (b) the deferred `/spawn`
      candidate (the `unstable-watch.yml` third step plus the
      `test_unstable_deselection_wiring.py` assertion it invalidates) verbatim from this plan's
      Scope Decisions; (c) the flagged, deliberately-unmade `release.yml` comment update and why;
      (d) the deliberate `oracle/conftest.py` non-mirroring.

**Timing**: 0.75 hours

**Depends on**: 1, 2, 3, 4, 5

**Verification Tier**: full

**Files to modify**:
- None (verification and summary-record phase only)

**Verification**:
- All of `code/tests/ci/` green.
- Identical collected-test counts with and without the new filter.
- Zero tests collected under `-m development`.
- The four deferred/flagged items are present in the summary.

## Testing & Validation

- [ ] `cd code && PYTHONPATH=src pytest tests/ci/test_unstable_deselection_wiring.py -v` passes,
      with the extended `not development` assertion demonstrated to bite (temporary-revert check).
- [ ] `cd code && PYTHONPATH=src pytest tests/ci/test_unstable_watch_classifier.py -v` passes, with
      every pre-existing test unchanged.
- [ ] A failing `development`-marked test in the classifier's dev JUnit input yields exit code 0
      and does not disturb any `unstable` test's promotion streak.
- [ ] The gating parallel expression collects exactly the same tests with and without
      `and not development`.
- [ ] `pytest --collect-only -m development -q` collects zero tests.
- [ ] `pytest --markers` lists `development`.
- [ ] `oracle/run-oracle-suite.sh`'s expressions collect without error despite the marker being
      unregistered in the oracle tree.
- [ ] TESTING_GUIDE.md section numbering is contiguous and the diff is confined to the new 8.14
      block plus one sentence in 8.9.

## Artifacts & Outputs

- `code/pyproject.toml` - `development` marker registered
- `.github/workflows/tests.yml` - 2 `-m` expressions carry `and not development`
- `.github/workflows/differential-tests.yml` - 1 `-m` expression carries `and not development`
- `flake.nix` - 2 `-m` expressions carry `and not development`
- `oracle/run-oracle-suite.sh` - 2 `-m` expressions carry `and not development`
- `code/tests/ci/test_unstable_deselection_wiring.py` - contract extended to both markers
- `.github/scripts/unstable_watch_classify.py` - `DEV_STATUS` path and Development Watch reporting
- `code/tests/ci/test_unstable_watch_classifier.py` - new coverage for both
- `code/docs/core/TESTING_GUIDE.md` - new section 8.14, one appended sentence in 8.9
- `specs/173_add_development_marker_for_in_progress_theories/summaries/01_development-marker-summary.md`

## Rollback/Contingency

Every phase is independently revertible and the whole change set is additive:

- Phases 1-2 (marker + wiring): reverting restores the exact pre-task `-m` strings and marker list.
  Nothing depends on the marker existing, since no test carries it.
- Phases 3-4 (classifier): the new code path is reached only when
  `/tmp/watch-development.xml` exists, which no workflow step produces today. Reverting is a clean
  removal with no production behaviour change either way.
- Phase 5 (docs): documentation-only.

If Phase 2's contract extension proves to conflict with a concurrent edit to the same `-m` strings,
stop and re-read all four drivers rather than resolving textually — the task's own ordering note
warns that conflicting edits to these exact strings are the expected failure mode.

If the classifier work in Phases 3-4 cannot be completed, Phases 1, 2, and 5 still deliver a
complete, useful marker (registration + deselection + documentation); in that case Phase 5's
observability paragraph must say the mechanism is deferred entirely, and the deferred `/spawn`
candidate widens to include the classifier work.
