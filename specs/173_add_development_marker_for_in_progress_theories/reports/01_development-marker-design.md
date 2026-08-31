# Research: `development` pytest marker for in-progress theories

## Scope

This report answers the six numbered decisions the task poses (semantics, what stays gating,
deselection wiring, observability, exit path, documentation), grounded in the CURRENT state of
this task's eight `file_scope` files plus the files task 175 and task 172 actually touched (read
fresh, not from memory). It does not apply the marker to any bimodal test — no theory_lib
source file is in `file_scope`, so this task is CI-infrastructure-only: registering the marker,
wiring its deselection, documenting it, and deciding (with reasons recorded) how it gets
observed. It also does not re-litigate the `unstable`/`xdist_serial` markers' own criteria or
reopen the worker-crash (item D) or gating-floor investigations.

Files read: `.github/workflows/tests.yml`, `.github/workflows/differential-tests.yml`,
`flake.nix`, `code/pyproject.toml`, `oracle/run-oracle-suite.sh`,
`code/docs/core/TESTING_GUIDE.md` (sections 8.6, 8.8, 8.9, 8.12, 8.13),
`code/tests/ci/test_unstable_deselection_wiring.py`, `code/tests/ci/test_unstable_watch_classifier.py`
(current, 687 lines), `.github/scripts/unstable_watch_classify.py` (current, 533 lines, not in
`file_scope`), `.github/workflows/unstable-watch.yml` (current, not in `file_scope`),
`.github/workflows/release.yml`'s `test-and-release`/`build` job comments (not in `file_scope`),
`oracle/conftest.py`'s marker-mirroring `pytest_configure`, and
`code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`'s `UNSTABLE_EXAMPLES`
pattern. Predecessor summaries for tasks 158, 172, 175 read in full (all three landed in this
session; their outputs are ground truth here, not their descriptions).

## 0. THE FINDING THAT MUST SHAPE THE PLAN: a file_scope gap on item (4)

**`.github/scripts/unstable_watch_classify.py` and `.github/workflows/unstable-watch.yml` are
NOT in this task's `file_scope`, but item (4)'s stated preferred mechanism — "extending
unstable-watch.yml (whose classifier lives in `.github/scripts/unstable_watch_classify.py`...)
— extend the module, never the workflow YAML" — requires editing exactly the module that is
missing.**

Concretely:

- `code/tests/ci/test_unstable_watch_classifier.py` (in `file_scope`) loads
  `.github/scripts/unstable_watch_classify.py` **by absolute path**
  (`CLASSIFIER_SCRIPT = REPO_ROOT / ".github" / "scripts" / "unstable_watch_classify.py"`,
  line ~35). Its own module docstring frames it explicitly as "Unit tests for
  `.github/scripts/unstable_watch_classify.py`". There is no way to add meaningful new test
  coverage for a `development`-observability code path in this file without the subject module
  itself being editable.
- `classify()`'s current design is built entirely around the `unstable` marker's TIMING-vs-NEW
  dichotomy (a documented duration/message signature that MUST still be present, vs. anything
  else). A `development`-marked test's expected failure has no such signature in general — it is
  "genuinely not done yet", which could be any assertion failure, any exception, any message. Any
  extension has to introduce a materially different classification concept (see §4 below), which
  is a `classify()`/`run()` change, not a test-only change.
- `unstable-watch.yml`'s two `pytest ... -m unstable` invocations would need to become
  `-m "unstable or development"` (or a third, parallel step) for anything to reach the classifier
  in the first place — a workflow-YAML edit, also outside `file_scope`.

This is a real design tension, not a paperwork nit: `test_unstable_watch_classifier.py` is
declared in `file_scope` precisely because the task expects observability work to land somewhere
in this area, but the two files that would actually carry that logic are absent. Two precedents
in this same session bear on how to resolve it:

- Task 158 (`file_scope`: mostly `__main__.py`/`project.py`/`release.yml`) widened into
  `code/tests/cli/test_flag_matrix.py` and `test_parse_file_flags.py` — files outside its
  declared scope — because they were "a necessary corollary of the in-scope source edit" (its
  summary's Plan Deviation #4). The same reasoning applies here in the opposite direction: a test
  file inside `file_scope` (`test_unstable_watch_classifier.py`) has its necessary corollary
  (the module it tests) sitting just outside.
- Task 175 landed `TESTING_GUIDE.md`'s "classifier lives in an importable module... Adding a
  third `unstable` marking means extending that module... not editing workflow YAML" language
  specifically to steer a *future* extender toward the module-not-YAML pattern — anticipating
  exactly this kind of follow-on work, and implicitly assuming the extender would have that
  module in scope.

**Recommendation for the plan: widen `file_scope` to add
`.github/scripts/unstable_watch_classify.py`, following the task-158 corollary precedent, rather
than leaving item (4) undesigned or forcing an artificial workaround.** `.github/workflows/
unstable-watch.yml` itself can very likely stay untouched — see §4's recommended design, which
reuses the classifier's existing dual code+oracle JUnit inputs and needs at most a `-m`
expression change, which if truly required should be flagged for a narrow, explicit widening
too (a single line, `-m unstable` → `-m "unstable or development"`, on both `watch_code`/
`watch_oracle` steps) rather than left unresolved. If the task's owner prefers a stricter reading
of `file_scope` as a hard boundary, the alternative is to design (record the decision, per item
4) but NOT implement the classifier extension here, and use `/spawn` to open a narrowly-scoped
follow-up task owning exactly `.github/scripts/unstable_watch_classify.py` +
`.github/workflows/unstable-watch.yml` + `code/tests/ci/test_unstable_watch_classifier.py` (which
would then need to move out of *this* task's `file_scope` to avoid the same two-tasks-same-file
collision the ordering note in this task's own description warns about). Either resolution is
legitimate; leaving it undecided is not — do not let item (4) default to "extend the classifier"
in the plan text while the plan's phase list quietly never touches the file that requires.

## 1. Marker semantics — what `development` means, and application granularity

**Definition (for `code/pyproject.toml`'s `markers` list, mirroring the existing `unstable`/
`xdist_serial` entries' one-line style):**

> `development: Tests belonging to a theory still under active construction (see
> code/docs/core/TESTING_GUIDE.md section 8.X), whose current failure is expected and tracked
> rather than a regression. Deselected from release-gating runs with -m "not development"; the
> whole marked set is observed on its own schedule so it stays visible and fixable rather than
> silently hidden. Distinct from unstable (a single, investigated, non-semantic instability in an
> otherwise-complete theory) and from xdist_serial (a routine contention classification, not a
> quarantine).`

**Granularity: per-test, not per-module or per-theory-pytestmark.** The task's own framing poses
this as "the hard question" and warns that a theory-level blanket application "is also the
version most capable of hiding a real regression" — decide with the failure mode in view. Three
reasons per-test wins here, all traceable to file_scope's own contents:

1. **`test_unstable_deselection_wiring.py`'s existing contract is inherently test-mark-based.**
   It scans for `-m` expressions containing `not unstable`; a `pytestmark = pytest.mark.development`
   at the top of a whole test module is equally filterable by `-m "not development"` — granularity
   doesn't change the wiring mechanics. But it does change what "not development" *means*: a
   module-level blanket silently deselects every test in that module forever, including ones that
   already pass today and would pass tomorrow after an unrelated change elsewhere breaks them.
   Per-test marking (mirroring `UNSTABLE_EXAMPLES = {"BM_CM_1"}`'s
   `marks=[pytest.mark.unstable] if name in UNSTABLE_EXAMPLES else []` pattern already established
   in `test_bimodal.py`, even though that file is outside this task's `file_scope`) keeps every
   currently-passing bimodal test in the gating suite, and only pulls out the specific tests that
   are actually known-incomplete right now.
2. **Item (2)'s "must not hide a regression" requirement is easier to keep true per-test.** A
   theory-level marker has no way to express "this specific test started failing for a NEW reason
   unrelated to the theory's known incompleteness" — every failure in the theory is equally
   invisible. A per-test marker keeps every *other* bimodal test (the overwhelming majority —
   today, only `BM_CM_1` carries `unstable` and four `test_soundness_regression.py` tests carry
   `xdist_serial`; nothing is currently known-failing) fully gating, so a regression anywhere else
   in bimodal still turns CI red exactly as it does today.
3. **Precedent inside this exact codebase already rejected the theory-level shape for a sibling
   concern.** Task 174's description (a currently `not_started`, dependent-on-this-task sibling)
   explicitly states: "Do NOT mark the crashed test `unstable`... The crash is NOT test-scoped...
   so a test-level marker cannot contain it." That is the *opposite* failure mode from this one —
   there the crash truly is cross-test and a test-level marker would be dishonest — but it
   establishes the codebase's working principle: **match the marker's grain to the failure's own
   grain.** A theory "under development" is, in the concrete case at hand, a set of *specific*
   known-incomplete behaviors, not an undifferentiated blob — so the marker should be applied at
   that same grain.

A theory-level convenience marker is explicitly NOT recommended. If a future contributor wants a
lighter-weight way to bulk-apply it to many known-failing tests at once (as `UNSTABLE_EXAMPLES`
does via a set-membership list), that is a per-test *application ergonomics* choice inside the
theory's own test file (out of `file_scope`), not a change to what the marker semantically means
or how it is deselected.

## 2. What must stay gating regardless — the executable boundary

**Soundness/differential-oracle failures stay gating, enforced structurally rather than by
convention, via the same mechanism `oracle/conftest.py` already uses for scope separation:**

`oracle/conftest.py`'s own docstring states its `pytest_configure` mirrors `differential`, `slow`,
and `unstable` from `code/pyproject.toml` "so the two declarations do not drift", and instructs
future editors to "keep this list and `code/pyproject.toml`'s markers list in sync". **This task
should deliberately NOT add `development` to that oracle mirror list** — the one place in this
codebase where "keep two files in sync" is an established, named convention, this marker is the
intentional exception, and that exception must be recorded as a comment at both sites (in
`oracle/conftest.py`, out of `file_scope`, flag for the plan to note even if not edited here; and
in `code/pyproject.toml`'s own marker entry or an adjacent comment, which IS in `file_scope`).
Consequences:

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — home to `TestCIGate`,
  `TestGatingConclusiveScan`, and every differential-comparison/soundness assertion — has no
  `development` marker registered at all. Applying it there would either be silently swallowed
  (pytest does not error on an unregistered mark unless `--strict-markers` is set, and neither
  `code/pyproject.toml`'s `addopts` nor any oracle-side ini sets it) or would need the mirror
  entry added deliberately, which this design explicitly withholds. **No oracle-tree test can
  ever legitimately claim `development` under this design** — the category exists only for
  `code/`-tree theory implementation tests, not for the differential soundness harness that
  checks a theory's semantics against reference oracles regardless of how "done" the theory is.
- `oracle/run-oracle-suite.sh` should still carry `and not development` in both passes' `-m`
  expressions defensively (the same "costs nothing, closes a future gap" pattern
  `release.yml`'s `build` job already uses for `unstable`: "a defensive no-op today... makes this
  real pytest invocation... structurally incapable of gating on a quarantined test... even though
  nothing here currently needs the exclusion"). Since the marker is unregistered in `oracle/`,
  this really is a no-op filter today, but it is one line of defense-in-depth against a future
  contributor mistakenly registering and using it there, and it keeps `test_unstable_deselection_
  wiring.py`'s per-file contract shape uniform across all four scanned drivers (see §3).
- Within `code/`, the boundary is enforceable per-test the same way `unstable`/`xdist_serial`
  already are: nothing stops a future author from mis-marking a genuinely-soundness-relevant test
  `development`, but that is true of every marker in this taxonomy today (`unstable`'s own entry
  criteria are enforced by review discipline and TESTING_GUIDE.md's four-point checklist, not by
  code). Recommend documenting, in the new TESTING_GUIDE.md subsection, an explicit "must not be
  used for" list mirroring 8.9's entry-criteria discipline: differential/soundness-oracle tests,
  and any test whose current pass/fail state encodes a semantic claim about the theory's
  correctness rather than its completeness.

## 3. Deselection wiring — extending the existing contract, not writing a parallel one

Both drivers already carry the pattern to copy. Current `-m` expressions (verified against the
files as they stand right now, all four already landed task-172/175/158 edits):

| Driver | Pass | Current `-m` expression |
|---|---|---|
| `tests.yml` | parallel | `not packaging and not performance and not unstable and not xdist_serial` |
| `tests.yml` | serial | `xdist_serial and not packaging and not unstable` |
| `flake.nix` `checks.default` | parallel | `not packaging and not performance and not unstable and not xdist_serial` |
| `flake.nix` `checks.default` | serial | `xdist_serial and not packaging and not unstable` |
| `differential-tests.yml` | first invocation | `not slow and not differential and not unstable` |
| `differential-tests.yml` | second invocation | node-id-selecting, no `-m` at all (unaffected) |
| `oracle/run-oracle-suite.sh` | pass 1 | `not xdist_serial and not slow and not unstable` |
| `oracle/run-oracle-suite.sh` | pass 2 | `xdist_serial and not slow and not unstable` |

**Add `and not development` to every `-m`-bearing invocation in this table** (six invocations
across four files — `differential-tests.yml`'s second invocation stays untouched, exactly as it
already does for `unstable`, since it is node-id-selecting and structurally cannot collect a
`development`-marked test either).

`code/tests/ci/test_unstable_deselection_wiring.py` (in `file_scope`) is the executable contract
already covering exactly this shape for `unstable`. It should be **extended in place, not
duplicated**, per the task's own instruction — its current design already generalizes cleanly:

- `TestGatingInvocationsDeselectUnstable` (the class name itself is now slightly stale once a
  second marker is covered — consider whether to rename the class, e.g. to
  `TestGatingInvocationsDeselectQuarantineMarkers`, or add a sibling class; either is fine, but
  pick one and keep `test_scanned_invocation_counts_match_known_shape`'s per-file invocation
  counts unchanged since parsing shape hasn't changed, only the assertion content).
  `test_every_marker_expression_excludes_unstable` asserts `"not unstable" in marker_expr` per
  invocation — the natural extension adds a second assertion, `"not development" in marker_expr`,
  over the same already-extracted `invocations` list, rather than a second parsing pass.
- `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable` documents why
  `unstable-watch.yml` is excluded from the scanned-file list and confirms it selects (not
  deselects) `unstable`. If `unstable-watch.yml` gains a `development` selection too (§4,
  contingent on the file_scope resolution in §0), this test's docstring and assertion should gain
  a parallel check — but note this test's file (`unstable-watch.yml`) is itself outside `file_scope`
  today, so this specific extension is gated on §0's resolution, not automatic.
- **`release.yml`'s documented no-op comment** ("Any pytest suite added to this job in the future
  MUST carry `not unstable`...", `.github/workflows/release.yml:159-161`, and the `build` job's
  defensive `and not unstable` at line 237) is named explicitly in the task description as needing
  "the same treatment". `release.yml` is **not** in this task's `file_scope`. Recommend: (a) the
  plan should still update that comment's wording to also name `development` (a documentation-only
  edit, low risk, and the task description explicitly asked for it) even though the file sits
  outside `file_scope` — following the same corollary-widening precedent as §0, or (b) explicitly
  record in the plan that this specific one-line comment/filter update is deferred, with a reason.
  Do not silently skip it; the task description called it out by name.

**`code/pyproject.toml`'s own `markers` list** gets the new one-line `development: ...` entry
(§1's proposed text), inserted after `xdist_serial` (last-registered) or after `unstable`
(thematically adjacent) — either ordering is fine, no test in `file_scope` asserts marker-list
ordering.

## 4. Observability — the recommended design (contingent on §0's file_scope resolution)

Assuming `file_scope` is widened per §0's recommendation to include
`.github/scripts/unstable_watch_classify.py` (and, minimally, a one-line `-m` change in
`unstable-watch.yml`):

**Do not reuse `classify()`'s TIMING/NEW machinery as-is.** That function's entire design encodes
"this specific documented signature = expected instability; anything else = investigate" — a
model that fits `unstable`'s single-known-failure-mode-per-test semantics but not `development`'s
"this theory has an open-ended, evolving set of known-incomplete behaviors" semantics. A
`development`-marked test's failure text will vary as the theory's implementation changes across
commits; pinning it to a specific signature string (the way `MAX_TIME_BY_NODEID_FRAGMENT` and
`GATING_FLOOR_SIGNATURE` do for `unstable`) would require updating the classifier on every commit
that changes a development test's failure mode — a maintenance burden `unstable`'s stable,
investigated signatures don't have.

**Recommended shape: a `DEV_STATUS` classification, orthogonal to TIMING/NEW, added as a third
branch in `classify()`'s caller (`run()`), not `classify()` itself:**

- A `development`-marked node id's outcome (from JUnit `parse_junit`) is recorded verbatim
  (`passed`/`failed`/`error`) with **no attempt to distinguish "expected" failure text from
  "unexpected"** — by definition, any current failure on a `development`-marked test is expected
  (that is what the marker asserts), and any exception/error is *also* worth surfacing (a
  collection-breaking `ImportError`, say) but should never be conflated with a semantic
  regression the way a `NEW` classification implies for `unstable`.
- **Never contributes to `any_new` / the classify step's exit code.** This is the load-bearing
  design constraint from item (2): a `development`-marked test's watch run must never turn the
  (already non-gating) `unstable-watch.yml` job red, mirroring exactly how a `TIMING` failure
  today leaves that job green. The interesting signal for `development` tests is not
  pass-vs-fail-today, it is **trend**: is a previously-failing test now passing (progress worth
  noting toward eventual promotion) — the inverse of `unstable`'s "is a previously-failing test
  still failing the same documented way" question.
- **Per-test streak/trend tracking should track the OPPOSITE direction from `unstable`'s.**
  `compute_per_test_promotion_streak` counts consecutive *clean* runs toward a 20-run promotion
  threshold. For `development`, the useful signal is closer to "how many of the last N runs did
  this specific test PASS" (a rising number is progress; report it, do not gate on it, and do not
  reuse the 20-run/`READY TO PROMOTE` framing verbatim — that framing specifically means "ready to
  remove the marker because the instability resolved itself", which is a different claim than
  "this theory's test now passes"). A simpler `{nodeid: (passes_in_last_N, total_in_last_N)}`
  summary table, reusing `fetch_past_classifications`'s existing `gh run download` +
  per-run-JSONL-artifact machinery (it already generalizes to any tracked node id set, not just
  the two currently in `MAX_TIME_BY_NODEID_FRAGMENT`/`GATING_FLOOR_NODEID_FRAGMENT`), is
  sufficient and avoids overloading `READY TO PROMOTE`'s existing, narrower meaning.
- `unstable-watch.yml`'s two watch steps would need `-m "unstable or development"` (both `code/`
  and `oracle/` steps — though per §2, the oracle step will simply never collect anything under
  `development` since the marker isn't registered there, so its own `-m` change there is either a
  genuine no-op or can be skipped; recommend changing both anyway for textual parity with the
  `code/` step, consistent with `test_unstable_deselection_wiring.py`'s existing "defensive
  symmetry across both passes" convention).

**Alternative considered and not recommended: a separate job/workflow.** A second, brand-new
scheduled workflow file duplicating `unstable-watch.yml`'s checkout/setup/run/upload structure
just to select `-m development` instead of `-m unstable` would (a) require an entirely new
workflow YAML file (also outside `file_scope`, an even larger widening than extending the
existing one), (b) duplicate the non-gating-contract comment block and permissions boilerplate
`unstable-watch.yml` already carries, and (c) fragment the "what's currently marked and why"
picture across two workflow files instead of one. Extending the existing workflow's `-m`
expression and the existing classifier module is the smaller, more consistent change.

**Alternative considered and not recommended: a periodic report with no CI job at all** (e.g. a
`/todo`-style script a human runs on demand). This fails the task's own stated requirement
("quarantined tests remain learnable-from and fixable later... A marker with no watch mechanism
fails the stated requirement") — an on-demand-only report is not "observed", it's "observable if
someone remembers to look", which is precisely the failure mode `unstable-watch.yml`'s nightly
cadence exists to prevent for the sibling marker.

**If `file_scope` is NOT widened** (the stricter reading from §0): the plan should still record
this section's design as the *intended* eventual mechanism, but implement only marker
registration + deselection wiring + documentation here, and open a follow-up task (via `/spawn`,
naming exactly `.github/scripts/unstable_watch_classify.py`,
`.github/workflows/unstable-watch.yml`, and `code/tests/ci/test_unstable_watch_classifier.py` as
its `file_scope`) to implement it. Do not implement a half-measure inside the wrong files just to
avoid the widening-vs-follow-up decision.

## 5. Exit path — retiring the marker for a theory

Mirror 8.9's "standing rule" structure, adapted for a marker whose unit of exit is a *test* (when
it's fixed) composing toward a *theory-level* milestone (when the theory is no longer
"in development" as a whole), rather than 8.9's single per-test 20-run/verified-fix criterion:

- **Per-test exit**: a `development`-marked test's marker is removed exactly when the underlying
  behavior is implemented/fixed and the test passes — mechanical, immediate, no waiting window
  (unlike `unstable`, there is no "prove it wasn't a fluke" requirement, since the marker was
  never claiming instability in the first place, only incompleteness). Removal is a normal part of
  ongoing bimodal development work, not a dedicated promotion ceremony.
- **Theory-level exit** ("bimodal is no longer in development"): recommend this be a **concrete,
  externally-checkable condition** — zero remaining tests in the theory's test tree carry
  `@pytest.mark.development` — rather than a subjective human call. This is directly analogous to
  8.9's mechanical per-test promotion but composes naturally: the theory-level claim is true
  exactly when the per-test claims are all resolved. Recommend a lightweight executable check
  (e.g., a `--collect-only -m development` count in a maintenance script, or a comment-only
  convention documented in TESTING_GUIDE.md pointing at `grep -rn "pytest.mark.development"`) that
  a task like the eventual "bimodal is production-ready" milestone can cite as its own exit
  evidence — but do not over-build this; a documented grep-based check is proportionate for a
  marker used by a single theory today.
- **8.9's "standing rule" analogue**: recommend the same escalation discipline — a test still
  carrying `development` after some review cadence (8.9 uses "two review cycles, roughly two
  months" for `unstable`; a theory genuinely under active construction likely warrants a longer or
  differently-shaped cadence, e.g. tied to the theory's own milestone/roadmap rather than a fixed
  calendar window, since "still incomplete after two months" is not itself surprising for a
  from-scratch theory the way "still flaky after two months" is for `unstable`) — or an explicit
  recorded reason why the standing rule does not apply verbatim to `development`. Record whichever
  choice is made; do not silently omit the analogue.
- **Who decides**: recommend the same implicit answer 8.9 uses for `unstable` — whoever owns the
  test removes the marker once the fix lands (mechanical, evidence-based), and the monthly-review
  backstop (or its `development`-appropriate analogue) is a human check that a stalled marking
  gets escalated rather than forgotten.

## 6. Documentation — TESTING_GUIDE.md

**New subsection, section 8.14** (after 8.13, the last-numbered subsection currently in the file;
confirmed by `grep -n "^### 8\."` — 8.9 through 8.13 are the existing run, no 8.14 exists yet).
Recommended contents, mirroring 8.9's/8.12's own structure for internal consistency:

- **What the marker means** (§1's definition).
- **Entry criteria** — lighter than 8.9's four-point list (this is not a quarantine for an
  investigated defect, it's a completeness tracker), but still not a rubber stamp: recommend
  requiring (a) the theory is genuinely incomplete (not a workaround for a fixable bug elsewhere),
  and (b) a one-line comment at the marking site naming what's missing, so a reader doesn't have
  to reverse-engineer intent from a bare decorator.
- **What it must not hide** (§2) — the explicit "must not be used for" list, and the deliberate
  non-mirroring into `oracle/conftest.py`.
- **Where the deselection is wired** (§3) — extend 8.9's own "Where the deselection is wired"
  paragraph's file list (it already names all four `file_scope` drivers plus `release.yml`) to
  also state the `development` marker's wiring, or add a parallel paragraph under the new 8.14 —
  either placement is acceptable, but do not leave 8.9's paragraph implying only `unstable` when
  a reader would reasonably expect it to be current for every quarantine-style marker.
- **Observability** (§4) — however §0 resolves, document the actual mechanism (or the recorded
  decision to defer it to a follow-up task, naming that task).
- **Exit path** (§5).
- **Marker-choice guidance** — the task explicitly asks for "how a reader chooses between
  `development`, `unstable`, `xdist_serial`, and `performance`". Recommend a decision-table
  mirroring 8.12's existing `performance` vs. `xdist_serial` table:

  | Marker | Meaning | Use when |
  |---|---|---|
  | `development` | Theory-under-construction, known-incomplete behavior | The behavior genuinely isn't implemented/correct yet, and the theory is still being built |
  | `unstable` | Investigated, non-semantic instability in an otherwise-complete theory | A specific documented failure mechanism, demonstrably non-semantic, survived a genuine fix attempt |
  | `xdist_serial` | Routine contention classification for a real wall-clock assertion | The test is correct and complete; only `-n`-pool contention threatens its budget |
  | `performance` | Budget too tight for any shared CI runner | Sub-10ms-class assertion, no amount of isolation helps |

- **Currently marked** — an explicit statement that, as of this task, **no test carries
  `development`** (nothing in `file_scope` includes a theory_lib source file, so this task adds
  the category without applying it), analogous to 8.9's "Currently marked" list but honestly
  empty. This avoids a future reader assuming some test is already covered when none is.

## Cross-references confirmed accurate (no re-derivation needed)

- The task's "CORRECT A LIKELY PREMISE" claim — `release.yml`'s `test-and-release` job runs no
  pytest at all, the only release-path pytest is `build`'s `packaging`-marked invocation — is
  independently reconfirmed by direct inspection of `release.yml:155-237` (not merely trusted from
  the task description): `test-and-release` builds/installs/imports/`--help`/version-checks only,
  no `pytest` token anywhere in that job's `run:` block; `build`'s only pytest line is
  `python -m pytest tests/packaging/ -v -m "packaging and not unstable"`.
- The task's second "CORRECT ONE MORE PREMISE" claim — `unstable-watch.yml`'s triggers are
  `schedule`/`workflow_dispatch` only, so extending it does nothing for master/PR signal — is
  reconfirmed directly against the current file's `on:` block (`schedule: cron '0 5 * * *'`,
  `workflow_dispatch:`, no `push`/`pull_request`/`tags`). This means the *actual* CI-signal payoff
  of this whole task is entirely in §3's deselection wiring (keeping `tests.yml`/
  `differential-tests.yml`/`flake.nix`/`run-oracle-suite.sh` green once a theory carries
  known-incomplete tests) — §4's observability work is purely the "don't forget" half, exactly as
  the task's own item (4) framing states, not a second source of gating signal.

## Recommended plan-phase shape (for the planner, not prescriptive)

1. `code/pyproject.toml`: register `development` marker.
2. Four drivers' `-m` expressions (`tests.yml` ×2, `differential-tests.yml` ×1,
   `flake.nix` ×2, `oracle/run-oracle-suite.sh` ×2): add `and not development`.
3. `test_unstable_deselection_wiring.py`: extend the existing parametrized assertions to also
   require `not development`; extend/rename the documentation-grade `unstable-watch.yml` exclusion
   test if §4's file_scope widening is accepted.
4. `TESTING_GUIDE.md`: new section 8.14 per §6 above; a narrow-scoped update to 8.9's own
   "Where the deselection is wired" paragraph if that's the chosen placement — coordinate with
   task 176's advisory (also touching `TESTING_GUIDE.md`; keep this task's edits section-scoped to
   avoid collision, per the dispatch's own advisory).
5. (Contingent on §0's resolution) `.github/scripts/unstable_watch_classify.py` +
   `code/tests/ci/test_unstable_watch_classifier.py`: §4's `DEV_STATUS` extension, OR a `/spawn`
   follow-up task if the stricter file_scope reading is chosen instead.
6. `release.yml`'s no-op comment: one-line wording update naming `development` alongside
   `unstable` (§3's release.yml note), or an explicit deferral recorded in the plan.
