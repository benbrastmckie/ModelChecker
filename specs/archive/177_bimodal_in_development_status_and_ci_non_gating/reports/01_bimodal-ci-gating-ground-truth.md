# Bimodal In-Development Status and CI Non-Gating: Ground-Truth Inventory and Recommendations

## 0. Method

Every claim in the task description was checked directly against the tree (not assumed). All
line numbers, filter expressions, trigger paths, and counts below were re-read at the time of
this report and are current as of commit `6ee88ed5` (task 177: create bimodal in-development
status and CI non-gating). Where the task description flagged a claim as suspected-false, the
verified truth is stated explicitly, not just repeated.

## 1. Verified Ground-Truth Inventory of the CI Gating Surface

### 1.1 The `development` marker and its one applier

- Registered at `code/pyproject.toml:97` (the `markers` list starts at line 88, ends `]` at line
  98 — confirmed by direct read; `addopts` itself is at line 87:
  `addopts = "--durations=0 -v --import-mode=importlib"`, carrying no `-m`).
- Applied by exactly one hook: `code/src/model_checker/theory_lib/bimodal/tests/conftest.py`'s
  `pytest_collection_modifyitems` (lines 21-60), path-scoped to
  `code/src/model_checker/theory_lib/bimodal/tests/` via `_BIMODAL_TESTS_DIR` (line 18) and the
  `item_path` containment check (lines 57-60). This is the sole authorized theory-wide blanket
  per `code/docs/core/TESTING_GUIDE.md` section 8.14 ("Granularity" and "Currently marked"
  paragraphs), landed by commit `74e6eb08` ("task 153 phase 8: apply development marker to the
  bimodal test tree") — NOT by task 173, which only registered/wired the marker without
  claiming it (see 1.5 below).
- Deliberately **not** registered in `oracle/conftest.py` (confirmed: that file's
  `pytest_configure`, lines 35-63, registers only `differential`, `slow`, `xdist_serial` —
  no `development`). Because the `code/`-tree bimodal conftest is not an ancestor directory of
  `oracle/`, its hook never loads for an oracle-rooted invocation, so no oracle-tree item can
  ever carry `development` regardless of registration. This is structural, not merely a matter of
  registration text.

### 1.2 The seven `-m`-bearing gating invocations (task's suspicion confirmed: it is seven, not six)

Verified directly, all four scanned drivers plus their invocation shapes:

| # | File | Line(s) | `-m` expression | Notes |
|---|------|---------|------------------|-------|
| 1 | `.github/workflows/tests.yml` | 187 | `not packaging and not performance and not unstable and not xdist_serial and not development` | parallel pass, `-n 4` |
| 2 | `.github/workflows/tests.yml` | 191 | `xdist_serial and not packaging and not unstable and not development` | serial pass, no `-n` |
| 3 | `flake.nix` | 179 | `not packaging and not performance and not unstable and not xdist_serial and not development` | parallel pass, `-n 4` |
| 4 | `flake.nix` | 180 | `xdist_serial and not packaging and not unstable and not development` | serial pass, no `-n` |
| 5 | `.github/workflows/differential-tests.yml` | 75 | `not slow and not differential and not unstable and not development` | first step only; the second step (lines 80-90, "Run CI gate tests explicitly") carries **no `-m` at all** — six explicit `::TestClassName` node ids |
| 6 | `oracle/run-oracle-suite.sh` | 191 | `not xdist_serial and not slow and not unstable and not development` | pass 1, `-n 6`, defensive (marker unregistered in oracle tree) |
| 7 | `oracle/run-oracle-suite.sh` | 199 | `xdist_serial and not slow and not unstable and not development` | pass 2, serial, defensive |

**Confirmed: the number is SEVEN, not six.** `tests.yml` (2) + `flake.nix` (2) +
`differential-tests.yml` (1) + `run-oracle-suite.sh` (2) = 7. Every "six" claim named in the task
is present verbatim and is wrong:
- `code/docs/core/TESTING_GUIDE.md:972` — "wired through the same six invocations and the same
  contract test."
- `code/docs/core/TESTING_GUIDE.md:1388` — "Six invocations in total."
- `code/docs/core/TESTING_GUIDE.md:1391` — "enforces both `not unstable` and `not development`
  across all six."
- `code/docs/core/TESTING_GUIDE.md:1487` — "the registration, the six gating `-m` expressions,"
- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py:25` — "All six release-gating
  pytest invocations already carry"
- `code/src/model_checker/theory_lib/bimodal/tests/README.md:10` — "all six release-gating pytest
  invocations across the repository's CI drivers deselect it"
- `code/tests/ci/test_development_marker_application.py:13` — "(all six gating invocations
  already carry `and not development`;"

**No executable test asserts the number today.** `code/tests/ci/test_unstable_deselection_wiring.py::test_scanned_invocation_counts_match_known_shape`
(lines 136-145) asserts each *file's own* invocation count (2 each for all four files, 8 total
invocations, of which one — `differential-tests.yml`'s node-id-selecting step — legitimately
carries no `-m`), but nothing anywhere asserts the aggregate "7 (or 6) invocations carry
`and not development`" claim as a number. This is exactly why it drifted; see §4 for the concrete
fix.

### 1.3 `oracle/run-oracle-suite.sh` is invoked by no workflow (confirmed)

Grepped `.github/workflows/*.yml` and `flake.nix` for `run-oracle-suite`: the only hit is a
**comment** in `tests.yml:148` ("mirroring `oracle/run-oracle-suite.sh`'s parallel/serial
structure"). No `run:` step anywhere invokes the script. Its own header (lines 56-58) confirms
this is by design: "This script assumes it is already running inside the project's Nix devShell
... run it as `nix develop --command bash oracle/run-oracle-suite.sh`" — a manual driver.
**Confirmed as intended, not a bug**: two of the seven counted "gating" invocations (the two
passes inside `run-oracle-suite.sh`) never execute in CI at all. They exist so a developer's local
gating-reproduction run (and `nix develop`-based manual QA) also deselects `development`/`unstable`
defensively, and their presence is what the wiring-contract test (`test_unstable_deselection_wiring.py`)
is checking — a manual-only driver still needs the filter so a human running it locally doesn't
get a false-red from an in-development theory. Recommend the debt-fix note this explicitly rather
than implying it runs in CI (see §5).

### 1.4 GAP 1's actual mechanism (task's suspicion confirmed, but framing needs sharpening)

`differential-tests.yml` triggers (`paths:`, lines 18-24) on `oracle/bimodal_logic/**` OR
`code/src/model_checker/theory_lib/bimodal/**`, on `push` (branches `**`, tags-ignore `**`) and
`pull_request`. Two steps:

- Step 1 ("Run differential tests...", lines 44-79): `-m "not slow and not differential and not
  unstable and not development"` over
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`. The `and not development` here
  is confirmed **inert by construction** (no test in this file can ever carry `development` —
  see §1.1) but harmless; it is future-proofing prose already present, not a bug.
- Step 2 ("Run CI gate tests explicitly", lines 80-90): **no `-m` at all**, six explicit node ids
  (`TestCIGate`, `TestFormulaEnumerator`, `TestDifferentialInfrastructure`,
  `TestKnownFormulaBaseline`, `TestDifferentialComparison`, `TestDifferentialReport`), **no
  `continue-on-error`**. Confirmed by direct read of the class bodies: `TestCIGate` (line 2633)
  is explicitly documented as "self-contained, no BimodalHarness dependency. These tests run in
  normal CI on every bimodal code change" and its `test_oracle_baseline_agreement` method is a
  genuine soundness check — it asserts the bimodal-logic package's own `Z3OracleProvider` agrees
  with a known-tautology/known-invalid baseline, failing only on "resolved-and-wrong" (a real
  semantic disagreement), never on a timeout. The other five classes are infrastructure/formula
  enumerator/report-structure tests supporting that harness. None of the six classes is
  `TestGatingConclusiveScan` (the file's one `unstable`-marked class), which is why
  `test_unstable_deselection_wiring.py::test_differential_tests_yml_gate_step_has_no_marker_expression`
  (lines 147-154) already documents this as an intentional, checked shape for the `unstable`
  marker specifically — but that existing test says nothing about `development`, and nothing
  anywhere pins down *why it is acceptable that this step stays unconditionally gating even
  though bimodal is declared non-gating*.

**Net effect, confirmed**: any commit touching only
`code/src/model_checker/theory_lib/bimodal/**` still triggers `differential-tests.yml`, and a
regression in `TestCIGate::test_oracle_baseline_agreement` (or any of the other five classes)
still fails that workflow with no escape hatch. This is real, and it is exactly what
`code/docs/core/TESTING_GUIDE.md` section 8.14 says must remain true ("no semantic claim about
bimodal correctness can be quarantined -- only completeness claims about the `code/`-tree
implementation"). The task's framing that this "turns CI still red" is accurate; whether that is
a hole to close or a guarantee to keep is the actual decision (§2).

Contextual note: `master` is currently unprotected (confirmed —
`.github/workflows/tests.yml:38` and `.github/workflows/packaging.yml:33` both state "master is
currently unprotected, but if required status checks are ever enabled..."). A red
`differential-tests.yml` run today produces a red X / notification, not a blocked merge. This
does not change the design question — the project's own non-gating contract for `unstable` and
`development` is about signal hygiene ("stays visible... without... failing the build"), not
merge-blocking specifically — but it is useful context for how much is actually at stake today.

### 1.5 GAP 2's ergonomics gap (confirmed exactly as described)

- `code/pyproject.toml:87` `addopts = "--durations=0 -v --import-mode=importlib"` — no `-m`.
  Confirmed: a bare `pytest` from `code/` (or `pytest <bimodal-subpath>`) collects and runs the
  313 `development`-marked bimodal tests and can fail. This is **already a documented, deliberate
  choice**, not an oversight: `code/docs/core/TESTING_GUIDE.md` section 8.14's "Currently marked"
  block states verbatim: *"What this deliberately did NOT do: `code/pyproject.toml`'s `addopts`
  was **not** given an `-m "not development"` default... Consequence, stated rather than hidden:
  a bare local `pytest` from `code/` still collects and can still fail on bimodal."* (also present
  almost verbatim as a comment block in `specs/173_add_development_marker_for_in_progress_theories/plans/01_development-marker.md`
  around its Phase 5 notes). So this half of GAP 2 is **already resolved and documented** — no
  action needed beyond making sure `run_tests.py` (below) doesn't quietly reintroduce the
  silent-green failure mode from a different angle.
- `code/run_tests.py`: confirmed exactly as described.
  - `TestConfig.markers: List[str]` declared at line 56.
  - Populated at line 133: `markers=getattr(args, 'markers', [])` — but `create_argument_parser()`
    (lines 923-1018) defines **no** `--markers` or `-m` argument anywhere (confirmed by grepping
    every `add_argument` call: `--examples`, `--unit`, `--package`, `targets`, `--theory`,
    `--component`, `--components` (deprecated/hidden), `--list`, `--verbose`/`-v`,
    `--failfast`/`-x` — nothing else). `getattr(args, 'markers', [])` therefore always evaluates
    to `[]`; `config.markers` is a dead field, write-only, never read anywhere else in the file
    (confirmed: no other reference to `.markers` or `config.markers` exists in `run_tests.py`).
  - Only `-k` (keyword) filtering is ever emitted, at four call sites: lines 346, 396
    (`_run_logos_example_tests` / `_run_standard_example_tests`, both `"-k", "example"`), 515
    (a dynamic `filter_expr` in a unit-test path), and 541 (`"-k", "not example"`).
  - Net effect confirmed: `./run_tests.py bimodal` runs the full, unfiltered bimodal suite (all
    313 `development`-marked tests) with a real, non-zero exit code on any bimodal failure —
    `run_tests.py` has no marker awareness at all, so it cannot reproduce the gating drivers'
    `-m "not development"` selection, nor can a caller opt into `-m development` explicitly
    through this entry point. There is no existing test file for `run_tests.py`'s own behavior
    (`find code -iname "*run_tests*"` returns only the script itself) — any new behavior here
    needs a fresh test module under the project's mandatory TDD policy.

### 1.6 GAP 3's inertness (confirmed, and the fix is smaller than it looks)

- `unstable-watch.yml` (full file read) has exactly two watch steps: `watch_code` (lines 41-58,
  `-m unstable` over `code/`, writes `/tmp/watch-code.xml`) and `watch_oracle` (lines 60-89,
  `-m unstable` over `oracle/bimodal_logic/tests/`, writes `/tmp/watch-oracle.xml`). No third step
  selects `-m development` or writes `/tmp/watch-development.xml`. Confirmed by full-file read —
  there is no other step besides "Classify results..." (line 91) and "Upload per-run record"
  (line 99).
- `.github/scripts/unstable_watch_classify.py:55` — `DEFAULT_DEV_JUNIT_PATH =
  "/tmp/watch-development.xml"` — confirmed present and already wired as `run()`'s
  `dev_junit_path` default parameter (line 431). `run()`'s DEV_STATUS branch (lines 483-500,
  docstring at lines 20-28) is fully implemented: every testcase from `dev_junit_path` is recorded
  with `classification == "DEV_STATUS"` and its true outcome, never sets `any_new` (never
  gating), never sets `any_failure` (never signature-matched, never corrupts an `unstable` test's
  promotion streak). `main()` (lines 641-645) calls `run()` with **no explicit path arguments**,
  so it already resolves `dev_junit_path` to the `DEFAULT_DEV_JUNIT_PATH` module constant — **this
  means the classifier script itself needs zero code changes** for GAP 3; the only missing piece
  is a workflow YAML step that produces the file.
- Test coverage confirmed fully in place and passing today against the (currently unreachable)
  DEV_STATUS path: `code/tests/ci/test_unstable_watch_classifier.py` has a dedicated "Phase 3"
  block starting at the comment on line 691 (`# Phase 3: DEV_STATUS classification path...`)
  running through `TestDevStatusClassification` (line 765), `TestFetchPastClassificationsFieldSelector`
  (line 944), `TestComputeDevPassRate` (line 973), and `TestDevelopmentWatchSummary` (line 1006,
  ending at EOF line 1054) — this matches the task's cited "693-1036" range (the class bodies
  span 691-1054; the outer boundary is the comment header, not a class line). All of these are
  unit tests against `classify_mod.run()` directly with `tmp_path` fixtures — they do not depend
  on the workflow YAML at all, which is exactly why they already pass despite the production path
  being inert.
- `code/tests/ci/test_unstable_deselection_wiring.py::test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable`
  (lines 156-173) asserts, via `re.findall(r'pytest\s+\S.*?-m\s+unstable\b', text)`, that
  `unstable-watch.yml` contains **exactly 2** matches of the literal `-m unstable` pattern.
  **Important correction to the task's own framing**: adding a third step selecting `-m
  development` (not `-m unstable`) will **not** change this count — the regex only matches the
  literal substring `-m unstable`, so a new `-m development` step adds zero matches to it. The
  task's phrase "requires extending" is therefore accurate only in the sense of *adding a new test
  method* to this file (or an adjacent one) that pins down the new step's shape (selects `-m
  development`, writes to `/tmp/watch-development.xml`, tolerates exit codes 0 and 5, is
  `continue-on-error: true` like its siblings) — **not** in the sense of changing the existing
  "exactly 2" assertion's expected value. A planner reading the task text alone could be misled
  into thinking the "2" needs to become "3"; it does not, and should not (that assertion is
  specifically about `-m unstable`, and correctly stays at 2).
- `code/docs/core/TESTING_GUIDE.md` section 8.14 already names this as the deferred follow-up in
  two places, confirmed: the "Where the deselection is wired" paragraph's parenthetical
  ("defensive there today, since the marker is unregistered...") and, more directly, the
  "**The producing workflow step does not exist yet.**" paragraph (which the task cites as
  "lines 1412-1414" — confirmed present, describing exactly the mirroring-`watch_code`,
  tolerate-0-and-5 shape needed).

### 1.7 The stale Phase 6 exit criterion (confirmed, and its provenance is more specific than the task states)

- Owning task: **173** (`specs/173_add_development_marker_for_in_progress_theories`), status
  `[IMPLEMENTING]` / `.return-meta.json` `"status": "partial"` — **still open**, not archived.
  Its plan (`specs/173_add_development_marker_for_in_progress_theories/plans/01_development-marker.md`)
  Phase 6 ("Full-gate verification and deferred-item record", `[PARTIAL]`) contains the stale
  criterion in three places: an unchecked checklist item at line 501 ("Confirm `pytest
  --collect-only -m development -q` collects zero tests (the category exists, nothing claims
  it)."), an "Established (verified, green)" Finding recorded at line 529 ("`pytest --collect-only
  -m development -q` -- collects 0 tests."), and a further unchecked item in the "Testing &
  Validation" section at line 588. All three were **true when task 173 ran them** — task 173 only
  registered and wired the marker (§1.1), it did not apply it to any test. The criterion became
  false only once **task 153** (a different, later task) added the path-scoped collection hook in
  its own Phase 8 (commit `74e6eb08`), which is the one place any test actually claims
  `development`.
- Confirmed the correct prior reconciliation already happened, exactly as the task states: task
  153's own plan (`specs/153_assert_missing_frame_axioms_in_bimodal_semantics/plans/01_seriality-interpolation-axioms.md`,
  lines 615-619) records: *"Interaction with the `development` marker's owning task: that task's
  Phase 6 exit criterion... is now false by design. Its intent... was satisfied at the time; this
  phase is the first claim on it. Section 8.14's 'Currently marked' paragraph, the single place
  that statement lived, has been updated."* Cross-checked against `TESTING_GUIDE.md`'s current
  "Currently marked" paragraph (§ around line 1461 onward): it correctly states "The **entire
  `bimodal` test tree** ... 313 items at the time of writing — carries `development`", i.e. the
  canonical source of truth is already accurate.
- **What is NOT yet reconciled**: task 173's own plan file still carries the three stale
  lines verbatim (they were never a "single source of truth" — TESTING_GUIDE was — but they are a
  durable artifact a future reader of task 173 specifically could misread as still-current, and
  task 173 is not archived, so a future `/implement 173` dispatch resuming Phase 6 would hit a
  criterion that can never be satisfied again as literally written). Recommendation for the
  planner: **do not rewrite task 173's plan from task 177** (that would repeat exactly the
  cross-task-artifact edit that task 153 deliberately declined to make, for the same reason: a
  plan file is a historical record of what was true and verified at that dispatch, and TESTING_GUIDE
  is the intended single source of truth it points back to). Instead, treat this as **already
  substantively reconciled** (TESTING_GUIDE is correct and is the source of truth cited by both
  the marker docstring and task 153's own plan), and record in task 177's own artifacts a pointer
  note: if/when task 173 is ever resumed to close its own Phase 6, its next dispatch needs to
  either strike the "collects zero tests" bullet or re-scope it to "zero tests **outside the
  authorized bimodal blanket**" before it can be checked off — that is task 173's own housekeeping,
  not a code or test change task 177 should make.

## 2. GAP 1 Recommendation: Keep the oracle differential/soundness suite unconditionally gating

**Recommendation: KEEP `differential-tests.yml` gating (do not exempt bimodal-triggered runs of
it), and make the intent explicit and enforced rather than leaving it implicit.**

**Rationale**:
1. This is the one thing standing between "bimodal is non-gating" and "bimodal's semantic
   correctness claims are unverifiable in CI." Section 8.14 already draws this line for the
   `code/`-tree blanket ("no semantic claim about bimodal correctness can be quarantined -- only
   completeness claims about the `code/`-tree implementation"); the entire "safe rather than
   merely quiet" framing of this task depends on that line holding. Weakening it (e.g. adding
   `continue-on-error: true` to the CI gate step, or path-scoping the trigger away from
   `code/.../bimodal/**`) would let a genuine soundness regression in bimodal's Z3 oracle land
   with zero CI signal at all, not even a non-blocking one — the opposite of "failures remain
   visible to a developer working on it" (verification criterion (b) in the task).
2. `TestCIGate::test_oracle_baseline_agreement` (verified above, §1.4) is not a completeness
   check — it directly tests whether the oracle *disagrees with a known-correct baseline*, which
   is precisely the "semantic claim about correctness" category 8.14 already reserves as
   permanently gating.
3. The counter-argument — "bimodal must stay fully non-gating in CI, full stop" — proves too
   much: taken literally it would also require deselecting `TestCIGate` itself, which is exactly
   the erosion 8.14 was written to prevent, and the task's own MOTIVATION section explicitly frames
   the theory owner's declaration as being about the theory's *completeness*, not its soundness
   claims.
4. Keeping it gating costs little in practice today: the trigger already only fires on paths that
   changed (`oracle/bimodal_logic/**` or the bimodal `code/` tree), so an unrelated commit to
   another theory never touches this workflow at all. The "genuine design question" the task poses
   is really "should a bimodal committer be exposed to differential-tests.yml failing," and the
   answer this task's own MOTIVATION text supports is yes — a bimodal committer needs to know
   immediately if their change broke the oracle's Z3 soundness properties, not just its
   completeness.

**What "record it and enforce it" concretely means** (for the planner, not decided here beyond
recommending the shape):
- Add explicit prose to `differential-tests.yml` itself (not just `oracle/conftest.py`'s
  docstring and `TESTING_GUIDE.md` 8.14, which a reader of the workflow file itself won't see)
  stating: this workflow stays unconditionally gating for bimodal edits *by design*, distinct from
  the `code/`-tree completeness blanket, and naming the concrete tests (`TestCIGate` at minimum)
  that carry the soundness claim.
- Add ONE new executable assertion (extending `test_unstable_deselection_wiring.py`, which already
  owns this file's contract, rather than a new file) that operationalizes the decision so it
  cannot silently regress:
  - Assert the "Run CI gate tests explicitly" step has no `continue-on-error` key (a
    `yaml.safe_load`-free regex/text check consistent with this file's existing approach, or, if
    PyYAML becomes available, a structural check — note `test_workflow_parity.py`'s and
    `test_unstable_deselection_wiring.py`'s own docstrings both state PyYAML is not an installed
    CI dependency, so a regex/text check is the precedent to follow).
  - Assert `TestCIGate` remains one of the six node-id-selected classes in that step (already
    partially covered indirectly by `test_differential_tests_yml_gate_step_has_no_marker_expression`,
    but that test only asserts `TestGatingConclusiveScan` is absent, not that `TestCIGate` is
    present — add the positive assertion).
  - Assert the workflow's `paths:` trigger still includes both `oracle/bimodal_logic/**` and
    `code/src/model_checker/theory_lib/bimodal/**` (so nobody can silently narrow the trigger to
    stop firing on bimodal `code/`-tree edits).

This satisfies verification criterion (c) directly: "whatever soundness guarantee is decided in
GAP 1 is enforced by a test, not merely documented."

## 3. GAP 2 Recommendation: Teach `run_tests.py` about the marker; do not touch `addopts`

**Recommendation: leave `code/pyproject.toml`'s `addopts` untouched (this is already correctly
decided and documented — see §1.5); extend `run_tests.py` with an explicit `-m`/`--markers`
passthrough option, and give the gating-reproduction command first-class documented status inside
`run_tests.py`'s own `--help` epilog.**

**Rationale**:
1. `addopts` gaining a default `-m "not development"` would recreate exactly the silent-green
   failure mode 8.14 exists to prevent — `pytest <bimodal path>` would report "0 tests, success"
   with no indication anything was skipped. This has already been explicitly rejected once (task
   153's Phase 8 record, quoted in §1.5) and the task description independently warns against
   "fixing this reflexively." Nothing changed since that record was written to revisit it.
2. `run_tests.py`, however, is a different surface with a different failure mode: it currently
   cannot reproduce the gating drivers' selection *at all* (no `-m` support, only `-k`), which
   means a developer who wants "run bimodal the way CI's non-development-marked tests would see
   it" (e.g. to sanity-check that a change doesn't accidentally leak outside the blanket) has no
   documented, unified-runner path to do that — they must drop to raw `pytest` invocations,
   defeating the point of having a unified runner.
3. Concretely: add a `--markers`/`-m MARKER_EXPR` argparse option (mirroring the existing `-k`
   plumbing at the four call sites identified in §1.5: lines 346, 396, 515, 541, plus
   `_build_pytest_command` at line 603 for package tests) that appends `-m <expr>` to the built
   pytest command when supplied, and is a plain passthrough with no default value — so
   `./run_tests.py bimodal` keeps today's "runs everything, exit code reflects reality" behavior
   unless the caller opts in, e.g. `./run_tests.py bimodal --markers "not development"` to
   reproduce the gate, or `./run_tests.py bimodal --markers development` to explicitly select the
   in-development set (a no-op today given the whole tree is already blanket-marked, but future-
   proof for per-test marking of other theories).
4. This is new user-facing behavior on a script with **no existing test file**
   (`find code -iname "*run_tests*"` returns only the script) — per the project's mandatory TDD
   requirement, this needs a new test module (e.g. `code/tests/ci/test_run_tests_markers.py` or
   similar) written FIRST, asserting the built pytest command line contains `-m "<expr>"` when
   `--markers` is passed and omits it entirely when not passed (regression-proofing the "stays
   runnable by default" property), before the argparse/plumbing change lands.
5. Document the two canonical invocations side by side in `bimodal/tests/README.md` (which
   already documents the `-m development` opt-in path at its "Running the Tests" section, lines
   28-40) and in `TESTING_GUIDE.md` section 8.14 (which already documents the raw-pytest gating
   reproduction command) — add the `run_tests.py` equivalent once it exists, rather than leaving
   the unified runner undocumented for this purpose.

## 4. GAP 3 Mechanism: One new workflow step, zero classifier code changes, one new test

**Confirmed mechanism** (fully derived from source reading, §1.6):

1. Add a third step to `.github/workflows/unstable-watch.yml`, positioned alongside `watch_code`
   and `watch_oracle` (after line 58, before or after `watch_oracle` — order does not matter to
   the classifier), mirroring `watch_code`'s exact shape:
   ```yaml
   - name: Run development-marked tests (code/ tree)
     id: watch_development
     continue-on-error: true
     run: |
       cd code
       set +e
       PYTHONPATH=src pytest tests/ src/model_checker -m development -v \
         --junitxml=/tmp/watch-development.xml
       code=$?
       echo "exit_code=$code" >> "$GITHUB_OUTPUT"
       if [ "$code" -eq 0 ] || [ "$code" -eq 5 ]; then
         exit 0
       fi
       exit "$code"
   ```
   (Exit code 5 tolerance mirrors `watch_code`/`watch_oracle` exactly — "no tests collected" would
   only occur if the bimodal blanket were ever removed without a replacement, i.e. the theory
   graduated out of development, which is the deletion trigger recorded in 8.14's "Exit path.")
   The `-m development` selection over `tests/ src/model_checker` (not just the bimodal subtree)
   matches how the theory-wide blanket is applied and is consistent with the other two steps'
   selection scope over their respective trees; a narrower `src/model_checker/theory_lib/bimodal/tests/`
   selection would also work and is arguably clearer intent — this is a small, low-stakes choice
   for the planner, not a design fork.
2. **No changes needed to `.github/scripts/unstable_watch_classify.py`**: `main()` (lines 641-645)
   already calls `run()` with no explicit `dev_junit_path` argument, so it resolves to
   `DEFAULT_DEV_JUNIT_PATH = "/tmp/watch-development.xml"` (line 55) automatically — the exact
   path the new step above writes to. The entire DEV_STATUS classification path (§1.6) is already
   implemented and unit-tested; it has simply never had real input to classify.
3. **Test extension needed** (per the task's citation of
   `test_unstable_deselection_wiring.py:156-173`, clarified in §1.6): add a new test — either a
   new method on `TestGatingInvocationsDeselectQuarantineMarkers` in that same file, or a small
   adjacent test — asserting the new step's shape: it selects `-m development` (a targeted regex
   distinct from the existing `-m unstable`-scoped one), writes `--junitxml=/tmp/watch-development.xml`,
   and is `continue-on-error: true`. Do **not** touch the existing `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable`
   assertion of "exactly 2" `-m unstable` matches — that assertion is scoped to the `unstable`
   marker specifically and is unaffected by an `-m development` step (confirmed by the regex,
   §1.6).
4. This closes the loop the task's MOTIVATION section names directly: "This is the mechanism that
   lets bimodal regressions stay VISIBLE while non-gating, which is precisely what makes a
   non-gating theory safe rather than merely quiet" — after this step lands, a bimodal regression
   shows up in `unstable-watch.yml`'s nightly `## Development Watch` step-summary section
   (already implemented, confirmed by `TestDevelopmentWatchSummary`, §1.6) with a real pass rate,
   with zero risk of failing the job (confirmed non-gating by construction, §1.6).

## 5. Full Corrected List of Correctness-Debt Fixes (exact file:line anchors)

All verified directly against the tree; no line number below is assumed from the task
description without independent confirmation.

1. **`.github/workflows/README.md` lines 22-23** — "`general-tests`: a `ubuntu-latest` x Python
   `['3.10', '3.11', '3.12']` matrix that installs the PyPI `z3-solver` toolchain and runs
   `code/tests/` plus the full `code/src/model_checker` suite (bimodal included), filtered by
   `-m "not packaging"`, at `-n 6`." — **Confirmed false on all three counted claims**: the real
   filter (`.github/workflows/tests.yml:187`) is `-m "not packaging and not performance and not
   unstable and not xdist_serial and not development"` (five `not` clauses, not one), and the
   worker count is `-n 4` (`tests.yml:187`), not `-n 6`. Fix: rewrite to state the real five-clause
   expression and `-n 4`.
2. **`.github/workflows/README.md` line 26** — "runs `nix flake check`, exercising `flake.nix`'s
   `checks.default` output, which itself now covers the same broadened scope (`src/model_checker
   tests -m "not packaging"`)" — same understatement of the filter (confirmed `flake.nix:179`
   carries the same five-clause expression as `tests.yml`). Fix alongside item 1.
3. **`.github/workflows/README.md` lines 54-58** — the "Why `-n 6` and never xdist's auto
   worker-count mode" bullet states "`-n 6` is used literally, in both `tests.yml` and
   `flake.nix`'s `checks.default`." **Confirmed false**: both now use `-n 4` (`tests.yml:187`,
   `flake.nix:179`) — this was changed on measured evidence (see `tests.yml`'s own extensive
   comment at lines 51-59 and 115-132) and this README bullet was never updated. Fix: `-n 6` ->
   `-n 4` in this bullet.
4. **`.github/workflows/README.md` lines 60-62** — "`checks.default` in `flake.nix` is no longer
   bimodal-scoped: it now runs `src/model_checker tests -m "not packaging" -n 6 -q`" — **confirmed
   false on both the filter (missing four `not` clauses) and the worker count** (`flake.nix:179`
   is `-n 4`, and also carries `--timeout=300 --timeout-method=thread`, absent from this
   description). Fix alongside items 1-3; consider consolidating all four README passages into one
   accurate restatement of the real expression, since they currently repeat the same two errors
   (filter, worker count) four times.
5. **`.github/workflows/tests.yml` lines 102-113** — the "general-tests" job's comment block
   states: "this job deliberately does NOT exclude bimodal even though `nix flake check` ... also
   covers it" (line 109-110 verbatim: "this job deliberately does NOT exclude bimodal even though
   `nix flake check`..."). **Confirmed contradicted by the job's own filter** at line 187, which
   carries `and not development` — bimodal IS excluded from gating today (though the bimodal
   *code* still runs and reports, since `development` quarantines from gating, not from
   collection; the comment's claim is specifically about gating exclusion and is now wrong on that
   specific claim). Fix: reword to state that bimodal's tests still execute and report (not
   skipped/deselected from collection) but are gating-excluded via the `development` marker,
   consistent with 8.14's "quarantines... without hiding or skipping it" framing — do not simply
   delete the "does not exclude" claim, since the underlying point (bimodal is not filtered out of
   *collection*, cross-toolchain coverage is real) is still true and worth keeping, just
   mis-stated.
6. **Seven vs. six invocations** — full list of every "six" occurrence requiring correction,
   confirmed exact:
   - `code/docs/core/TESTING_GUIDE.md:972`
   - `code/docs/core/TESTING_GUIDE.md:1388`
   - `code/docs/core/TESTING_GUIDE.md:1391`
   - `code/docs/core/TESTING_GUIDE.md:1487`
   - `code/src/model_checker/theory_lib/bimodal/tests/conftest.py:25`
   - `code/src/model_checker/theory_lib/bimodal/tests/README.md:10`
   - `code/tests/ci/test_development_marker_application.py:13`
   Fix: "six" -> "seven" in all seven locations, and add the executable count assertion described
   in §1.2 (e.g. extend `test_unstable_deselection_wiring.py` with a test that sums
   `len(_invocations_for(f))` filtered to those carrying an `-m` expression, or a simpler literal
   `assert 1 + 1 + 1 + 1 + 1 + 2 == 7`-style accounting keyed to the same four `_SCANNED_FILES` —
   the exact shape is an implementation-phase decision, but it must be a real assertion, not a
   docstring, given this is precisely how the "six" error propagated silently across seven files).
7. **The stale Phase 6 exit criterion** — see §1.7 in full. Verified already correctly reconciled
   at the canonical source of truth (`TESTING_GUIDE.md`'s "Currently marked" paragraph, per task
   153's own precedent of not rewriting another task's plan). Recommend NOT editing task 173's
   plan file from task 177 (repeats the exact cross-task edit 153 declined); instead record the
   pointer note for task 173's own eventual resumption (§1.7, last bullet) in this task's own
   summary/report, not by modifying `specs/173_.../plans/01_development-marker.md`.
8. **`oracle/run-oracle-suite.sh` runs in no workflow** — confirmed intended (§1.3); recommend
   adding one sentence to `TESTING_GUIDE.md` section 8.14's "Where the deselection is wired"
   paragraph (immediately after "Six [-> Seven] invocations in total") clarifying that two of the
   seven never execute in CI and exist solely for the manual `nix develop` gating-reproduction
   path, so a future reader does not need to re-derive this the way this report had to.

## 6. Cross-Reference: Verification Criteria from the Task

- **(a) "a change touching only `code/src/model_checker/theory_lib/bimodal/**` cannot turn any
  required CI check red"** — TRUE today for `tests.yml` and `flake.nix` (both filter `not
  development`, confirmed §1.2) and for `differential-tests.yml`'s first step (inert filter,
  confirmed §1.4) — but **FALSE for `differential-tests.yml`'s second step** (§1.4), which is
  recommended to **stay** true-red-on-regression per §2's decision (soundness gates
  deliberately). Given the §2 recommendation, criterion (a) as literally stated should be
  understood as scoped to *completeness* checks (the ones 8.14 already blankets), with the
  soundness-check exception explicitly carved out and tested (§2's new assertion) rather than
  silently true. The planner should phrase the eventual plan's success criteria to match this
  scoped reading rather than the task's unscoped literal wording, since the unscoped wording is
  what this report's GAP 1 analysis argues against satisfying.
- **(b) "bimodal remains runnable and its failures remain visible to a developer working on it"**
  — TRUE today via `-m development` / bare `pytest` (§1.5) at the raw-pytest level; NOT yet true
  via the unified `run_tests.py` entry point (§1.5, §3) — this is exactly GAP 2.
- **(c) "whatever soundness guarantee is decided in GAP 1 is enforced by a test, not merely
  documented"** — NOT yet true (§1.4: no test asserts absence of `continue-on-error` or presence
  of `TestCIGate` in the gate step) — addressed by §2's proposed new assertion.

## 7. Files Read In Full (for provenance)

`.github/workflows/differential-tests.yml`, `.github/workflows/tests.yml`,
`.github/workflows/unstable-watch.yml`, `.github/workflows/README.md`, `code/pyproject.toml`
(markers/addopts region), `code/src/model_checker/theory_lib/bimodal/tests/conftest.py`,
`code/src/model_checker/theory_lib/bimodal/tests/README.md`, `oracle/conftest.py`,
`code/run_tests.py` (argparse, TestConfig, command-building sections), `oracle/run-oracle-suite.sh`,
`flake.nix` (pytest invocation region), `code/tests/ci/test_unstable_deselection_wiring.py`,
`code/tests/ci/test_development_marker_application.py`, `code/tests/ci/test_workflow_parity.py`
(header/extraction region), `.github/scripts/unstable_watch_classify.py`,
`code/tests/ci/test_unstable_watch_classifier.py` (Phase 3 / DEV_STATUS region),
`code/docs/core/TESTING_GUIDE.md` section 8.14 (in full) plus lines 960-980,
`specs/173_add_development_marker_for_in_progress_theories/plans/01_development-marker.md`
(Phase 6), `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/plans/01_seriality-interpolation-axioms.md`
(lines 595-625), `specs/TODO.md` (task 177, 173, 158 entries), `specs/173_.../.return-meta.json`.
