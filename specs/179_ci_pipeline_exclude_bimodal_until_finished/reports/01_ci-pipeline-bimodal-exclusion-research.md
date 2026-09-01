# Research: CI pipeline speed/green while bimodal is excluded

## 0. Verification of prior state ("already done")

Confirmed unchanged and holding, via direct inspection and execution (no full oracle-suite run,
per TESTING_GUIDE.md 8.8):

- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` still applies a path-scoped
  `development` blanket to all 313 bimodal in-package items via `pytest_collection_modifyitems`.
- `oracle/conftest.py` still applies a path-scoped `development` blanket to the oracle tree,
  exempting exactly `_SOUNDNESS_CORE_CLASSES = (TestCIGate, TestFormulaEnumerator,
  TestDifferentialInfrastructure, TestKnownFormulaBaseline, TestDifferentialComparison,
  TestDifferentialReport)`.
- `code/pyproject.toml`'s `development` marker text and `TESTING_GUIDE.md` sections 8.8/8.14
  match the implementation.
- `PYTHONPATH=code/src pytest code/tests/ci/ -q` → **136 passed** (29.4s), including all 12
  `test_oracle_development_marker_application.py` tests and the full
  `test_unstable_deselection_wiring.py` suite.
- Local commits `98c7c65a` (task creation) and `65f9de0e` ("update testing") already exist on
  `master` but are **unpushed** — `git status` reports `ahead 115` of `origin/master`. No live CI
  run reflects this repo's current state; all "before" GitHub Actions numbers below are the most
  recent *pushed* runs (pre-oracle-blanket, task 172's run). There is no "after" CI number yet —
  that requires an actual push, which is outside a research task's scope.

## 1. (a) Redundancy in differential-tests.yml — confirmed and quantified

`--collect-only` on both of `differential-tests.yml`'s pytest steps, diffed as sorted node-id
lists, is **byte-identical**: both select the same 49 node ids (verified with `diff`, zero
output). Step 1 (`-m "not slow and not differential and not unstable and not development"`) and
step 2 (`::TestCIGate ::TestFormulaEnumerator ::TestDifferentialInfrastructure
::TestKnownFormulaBaseline ::TestDifferentialComparison ::TestDifferentialReport`) now collapse
onto exactly the same soundness core.

**Historical CI evidence for the redundancy's cost** (run `32995122906`, job "Cross-Oracle
Differential Tests", the most recent pushed run, predating the `development`-marker addition to
step 1's `-m` expression, so it shows the *old*, non-redundant selection for comparison):

| Step | Selection (at that commit) | Wall clock |
|---|---|---|
| "Run differential tests" | 62 tests (`not slow/differential/unstable`, no `development` filter yet) | 4m56s |
| "Run CI gate tests explicitly" | 49 tests (node-id, the soundness core) | 3m14s |
| **Job total** | | **8m22s** (+ ~12s setup) |

Locally re-collecting the *old* expression (`not slow and not differential and not unstable`,
no `development`) against the current tree gives 62/72 collected — confirming the pre-`65f9de0e`
step-1 population really was 62, a proper superset of the 49-item core (13 extra items were the
non-core oracle tests, since removed from step 1's population once `and not development` was
added).

Post-`65f9de0e` (current, unpushed HEAD), step 1's `-m` expression now selects the identical 49
as step 2. Since both steps solve the same Z3 formulas via the same `TestCIGate` /
`TestDifferentialReport` etc. machinery, step 1's wall clock should now track step 2's (~3m14s)
rather than the old 62-item figure (~4m56s) — i.e. the job now pays roughly **2× the soundness
core's solve cost** (~6-7 min of pytest work) for **1× the coverage**. (I could not get a fresh
timed local run to confirm this precisely: a local `pytest ::TestCIGate ... ::TestDifferentialReport`
run timed out at the 2-minute Bash tool ceiling on this development machine — consistent with
TESTING_GUIDE.md 8.6's documented contention sensitivity of Z3 solves on a loaded machine, not a
regression. The CI-run evidence above is the reliable number; a fresh post-push CI run will give
the exact "after" figure.)

**Recommended collapse.** Delete step 1 ("Run differential tests…") entirely; keep step 2 ("Run
CI gate tests explicitly") exactly as-is. This is the minimal collapse that does not touch the
protected step: `TestOracleSoundnessGateStaysUnconditionallyGating`'s three assertions (no
`continue-on-error`, `::TestCIGate` node id present, `paths:` trigger unnarrowed on both `push`
and `pull_request`) all target the *second* step's block and are untouched by removing the first.
`--collect-only` above is the evidence that nothing is lost: the surviving step already
independently proves it selects the same 49 node ids the broad `-m` expression does.

**This collapse has real, non-optional follow-on edits** (do not do the workflow edit alone):

- `code/tests/ci/test_unstable_deselection_wiring.py`:
  - `EXPECTED_GATING_MARKER_INVOCATIONS = 7` → `6` (differential-tests.yml drops from 1 `-m`
    invocation to 0; total across all four scanned drivers goes 7→6).
  - `test_scanned_invocation_counts_match_known_shape`'s
    `assert len(_invocations_for(DIFFERENTIAL_TESTS_YML)) == 2` → `== 1`.
  - `test_differential_tests_yml_gate_step_has_no_marker_expression` should still pass unmodified
    (asserts exactly one node-id-selecting invocation with no `TestGatingConclusiveScan`), but
    re-verify after the edit.
  - The `_SEVEN_COUNT_ANCHORS` list's `must_contain`/`must_not_contain` pairs invert (they exist
    specifically to catch a "six" staying stale after a "seven" correction — this collapse is
    the mirror-image edit, "seven" becoming stale after a real invocation is removed, which is a
    legitimate reduction, not the drift the anchors were built to catch. Update the anchor
    *values* to expect "six" again).
- Exactly 7 documentation/docstring locations currently say "seven" as this specific count and
  must change together (all enforced by the anchors above): `code/docs/core/TESTING_GUIDE.md`
  (4 occurrences: "wired through the same seven invocations", "Seven invocations in total.",
  "across all seven.", "the seven gating `-m` expressions,"),
  `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` ("All seven release-gating
  pytest invocations already carry"), `code/src/model_checker/theory_lib/bimodal/tests/README.md`
  ("all seven release-gating pytest invocations…"), and
  `code/tests/ci/test_development_marker_application.py` ("all seven gating invocations already
  carry").
- `code/docs/core/TESTING_GUIDE.md` section 8.14's "Where the deselection is wired" paragraph
  should gain one sentence recording that `differential-tests.yml`'s broad `-m` step was removed
  as a proven redundant duplicate of the node-id gate step, with the `--collect-only` diff as the
  justification, so a future reader does not read "six" and assume `development` deselection
  wiring regressed.

None of this requires touching `GATING_RECHECK_SOLVE_TIMEOUT_MS`, `MIN_CONCLUSIVE_GATING_FORMULAS`,
or any assertion strength — it is pure invocation-count bookkeeping following a genuine
invocation removal.

## 2. (b) Open decision: keep the 49-test oracle soundness gate — already substantively resolved

`code/docs/core/TESTING_GUIDE.md` section 8.14 **already contains** the reconciliation this task
asks for, and it predates task 179's own commits (confirmed via `git show 65f9de0e -- ...
TESTING_GUIDE.md`: the paragraph is untouched by that diff, so it existed before this task
started). Key passages, already in the file:

> "Why a bimodal-only edit can still legitimately gate on `differential-tests.yml`... The
> `development` marker quarantines only *completeness* claims about the `code/`-tree
> implementation... `TestCIGate::test_oracle_baseline_agreement` asserts something categorically
> different: a *soundness* claim... A theory being incomplete is a reason to stop gating on
> *completeness*; it is not a reason to stop checking whether the theory is *wrong*."

And under "What this accepts, stated plainly" → "Soundness stays gating" bullet, plus the
`_SOUNDNESS_CORE_CLASSES` exemption mechanism and its three-part guard test
(`TestSoundnessCoreStaysGating`, `TestOracleTreeClaimsDevelopment`,
`TestOracleSoundnessGateStaysUnconditionallyGating`).

**Recommendation: keep the gate.** The rationale already on record is sound and the task's own
constraints reinforce it — dropping the 49-test gate would require deleting
`TestOracleSoundnessGateStaysUnconditionallyGating`, which the task brief itself names as the
thing "which exists precisely to prevent that happening by accident." No new information
surfaced in this research changes that calculus.

**One explicit gap to close, not a re-decision:** the task brief asks that the decision
"reconcile [the exclusion intent] against the soundness rationale" — the existing prose makes the
reconciliation *implicitly* (by scoping `development` narrowly to completeness) but never states
outright, in one sentence, "the repo owner's directive to exclude bimodal until finished is
honored for completeness testing and deliberately not extended to this one soundness check, and
here is why." Recommend the implementation phase add exactly that one linking sentence near the
top of the "Why a bimodal-only edit can still legitimately gate" paragraph so the reconciliation
is self-evident to a reader who has not independently derived it, without changing anything about
the mechanism itself.

**Documentation staleness bug found (unrelated to the decision above, but in the same section):**
8.14's "The producing workflow step does not exist yet" paragraph is **factually stale**.
`.github/workflows/unstable-watch.yml` already has a `watch_development` step (`id:
watch_development`, `-m development`, writes `/tmp/watch-development.xml`, `continue-on-error:
true`, tolerates exit 0/5) — added in commit `59a72993` ("task 177 phase 3: wire the -m
development producing step in unstable-watch.yml"), which predates task 179 entirely. The guard
test `test_unstable_deselection_wiring.py::TestGatingInvocationsDeselectQuarantineMarkers::
test_watch_development_step_selects_development_and_writes_junit` already asserts this step's
shape and **currently passes**. The stale prose ("has no step today that runs `-m development`…
until a future workflow change adds a third watch step") should be corrected to describe the step
as implemented, in the same TESTING_GUIDE.md edit pass as item (a)'s "seven"→"six" correction.

## 3. (c) Where gating CI time actually goes (measured, not guessed)

Historical `gh run view --json jobs` data for the most recent successful pushed run of each
workflow (task 172's push, run ids `32995122897` "Tests" and `32995122906` "Differential Oracle
Tests" — the two workflows fired on the same commit and started within seconds of each other):

**`tests.yml`** (matrix legs run concurrently; job wall clock, not CPU time):

| Job | Wall clock | Notes |
|---|---|---|
| General Suite / Python 3.10 | 3m56s | parallel + serial pytest pass |
| General Suite / Python 3.11 | 3m46s | parallel + serial pytest pass |
| General Suite / Python 3.12 | 3m45s ("Run general test suite" step: 3m25s) | parallel + serial pytest pass |
| **nix flake check** | **6m12s** (checkPhase itself: 5m14s, after ~50s of Nix store fetch/build setup) | **long pole — determines total workflow wall clock** |
| Workflow total | **6m16s** | bounded by flake-check, not the Python matrix |

`nix flake check`'s `checkPhase` runs the *same two pytest passes* as one `tests.yml` Python leg
(parallel `-n 4` pass + serial `xdist_serial` pass, byte-for-byte per `flake.nix`'s own comment
and enforced by `code/tests/ci/test_workflow_parity.py`), yet takes ~5m14s vs. ~3m25s for the
equivalent step on a Python-matrix leg — roughly 50% slower for nominally the same test
population and marker expression. Root cause is not established by this research (candidates:
nixpkgs' Z3 build vs. PyPI `z3-solver` wheel performance characteristics, sandboxed-build CPU
allocation, or cold-cache effects not fully absorbed by `magic-nix-cache-action`); flagged as a
follow-up investigation, not something to fix by widening any budget.

Given a 20-minute `timeout-minutes` on `general-tests` and 30 minutes on `flake-check`, both have
large headroom today (~3.5-4× and ~5× respectively) — no evidence of the matrix or flake-check
being close to their own timeout backstops.

**`differential-tests.yml`**: single job, no matrix. Current bottleneck is the redundancy
documented in section 1 above (paying for the 49-test soundness core's Z3 solves twice). Removing
step 1 is the direct, measured lever here — worth roughly halving the pytest portion of this
job's ~8m22s (from ~8m10s of the two redundant passes down to ~1 pass, ~3-4 min), which is by far
the largest win available in this task relative to effort, since it requires no new test-selection
logic, only removing a proven-duplicate step.

## 4. (d) unstable-watch.yml — confirmed non-gating, stays that way

Read in full. Triggers are `schedule: cron '0 5 * * *'` and `workflow_dispatch` only — no `push`,
no `pull_request`, no `tags`. The file's own header comment states the "NON-GATING CONTRACT"
explicitly ("must NEVER gate anything... must never appear in another workflow's `needs:`, and
must never be added to branch protection required-checks"). Its three watch steps
(`watch_code`, `watch_oracle`, `watch_development`) are all `continue-on-error: true`. Guard test
`test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable` confirms both
`unstable`-selecting invocations use `-m unstable` (not `not unstable`), and it is deliberately
excluded from `test_unstable_deselection_wiring.py`'s `_SCANNED_FILES` scan list. Nothing in
scope here needs to change; no action item for this workflow beyond continuing to leave it alone.

## 5. Summary of recommended next-phase (planning/implementation) work items

1. **(a)** Delete `differential-tests.yml`'s "Run differential tests (non-slow, no
   BimodalHarness)" step; keep "Run CI gate tests explicitly" unmodified. Update
   `EXPECTED_GATING_MARKER_INVOCATIONS` 7→6 and the invocation-count assertion for
   `DIFFERENTIAL_TESTS_YML` (2→1) in `test_unstable_deselection_wiring.py`; flip all 7 "seven"
   documentation/docstring anchors back to "six" (exact locations listed in section 1); add one
   sentence to TESTING_GUIDE.md 8.14 recording why the count dropped.
2. **(b)** No mechanism change — keep the 49-test soundness gate. Add one linking sentence to
   TESTING_GUIDE.md 8.14 explicitly reconciling "exclude bimodal until finished" against the
   soundness carve-out (see section 2). Separately, correct the stale "producing workflow step
   does not exist yet" paragraph in the same section — the step already exists and its guard test
   already passes.
3. **(c)** No code change indicated by this research beyond (a)'s redundancy removal — record the
   measured baseline table (section 3) in the task's summary/plan so a post-implementation push
   can be compared against it. Flag the flake-check-vs-matrix-leg speed gap as an out-of-scope
   follow-up if the repo owner wants it investigated further.
4. **(d)** No action — confirmed already correct.
5. **Verification plan for implementation**: `--collect-only` diffs (as done here) plus
   `PYTHONPATH=code/src pytest code/tests/ci/ -q` (136 tests) for every edit; a real "after"
   wall-clock number requires an actual push once these commits reach `origin/master` — note this
   explicitly in the plan/summary rather than fabricating a number, since local commits are
   currently 115 ahead of `origin/master` and unpushed.

## Files referenced

- `.github/workflows/tests.yml`, `.github/workflows/differential-tests.yml`,
  `.github/workflows/unstable-watch.yml`, `flake.nix`
- `oracle/conftest.py`, `code/src/model_checker/theory_lib/bimodal/tests/conftest.py`
- `code/pyproject.toml` (marker registration)
- `code/docs/core/TESTING_GUIDE.md` sections 8.6, 8.8, 8.9, 8.14
- `code/tests/ci/test_unstable_deselection_wiring.py`,
  `code/tests/ci/test_oracle_development_marker_application.py`,
  `code/tests/ci/test_development_marker_application.py`
- `code/src/model_checker/theory_lib/bimodal/tests/README.md`
