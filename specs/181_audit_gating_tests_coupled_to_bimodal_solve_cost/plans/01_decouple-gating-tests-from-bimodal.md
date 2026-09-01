# Implementation Plan: Decouple Release-Gating Tests from Bimodal Solve Cost

- **Task**: 181 - Audit and fix gating tests outside the bimodal test tree that still depend on bimodal solve cost
- **Status**: [IMPLEMENTING]
- **Effort**: 8.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/reports/01_gating-tests-coupled-to-bimodal.md`
- **Artifacts**: plans/01_decouple-gating-tests-from-bimodal.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The audit report enumerated every release-gating test outside `theory_lib/bimodal/tests/` that
constructs or solves a bimodal example, and recorded a disposition for each: switch the fixture to
logos where the assertion is not bimodal-specific, apply `@pytest.mark.development` at per-test /
per-parametrize granularity where the *subject* is genuinely bimodal but the claim is one of
completeness rather than soundness, and keep exactly one test
(`test_full_pipeline.py::test_theory_library_execution`) on bimodal because its `"World Histories"`
assertion cannot be reproduced under any other theory. This plan executes those dispositions,
closes the unaudited gating-driver gap that would otherwise make the `development` markings inert
(three workflows, four pytest invocations), extends the executable wiring contract to cover them,
and adds a new executable guard plus a before/after wall-clock record proving the decoupling
actually happened rather than asserting it qualitatively.

Definition of done: every release-gating selection's wall clock is independent of bimodal solve
cost except for one deliberately-retained, budgeted test; the non-bimodal suite is green and still
fully gating (no collection-count collapse); and both facts are enforced by tests, not by prose.

### Research Integration

The plan is built on the report's dispositions and does not re-derive them. Findings carried
forward verbatim:

- **Finding 1** — `packaging.yml`, `release.yml` (two jobs), and `pypi-smoke.yml` all run
  `code/tests/packaging/` with no `and not development` clause, and none of the three is in
  `test_unstable_deselection_wiring.py`'s `_SCANNED_FILES`. `test_generate_then_execute[bimodal]`
  was empirically confirmed still running past 200s on current HEAD against its own 180s
  subprocess timeout — it is now expected to fail via `subprocess.TimeoutExpired`, not merely to
  run slowly.
- **Finding 2** — `code/tests/utils/helpers.py::create_test_model()` hardcodes bimodal while
  advertising a `theory_name` parameter it never reads; roughly 20 gating call sites across three
  `tests/integration/` files inherit that, measured at 58 passed in 36.25s single-worker.
- **Finding 3** — coupling in `builder/tests/unit/test_example.py` is file-wide, with
  `test_iteration_via_iterate_api` measured at **31.78s against its own explicit 30s budget** — a
  currently-passing near-miss of exactly the failure already seen once in this file.
- **Finding 4** — `tests/e2e/test_batch_output_real.py` and
  `test_full_pipeline.py::test_print_impossible_flag_includes_impossible_states` repeat the
  already-fixed `tests/cli/conftest.py` CLI-plumbing pattern; `test_theory_library_execution` is
  the one genuine exception and stays on bimodal.
- **Finding 5** — `tests/cli/test_flag_matrix.py::_MAXIMIZE_EXAMPLE` is a second inline fixture the
  earlier `conftest.py` and `_CVC5_COMPATIBLE_EXAMPLE` fixes did not reach.

Two implementation-time couplings the report did not need to name, discovered while reading the
files this plan touches, and which the phase ordering below exists to handle:

1. `code/tests/ci/test_development_marker_application.py::TestDevelopmentMarkerIsContainedToBimodal`
   asserts that **no** item outside the bimodal tree carries `development`, both per-root (roots
   include `tests`) and in the mixed-root `tests src/model_checker` collection. Applying the two
   markings the report recommends will turn that contract red. It must be widened to a named,
   enumerated allowlist in the same phase as the markings — never deleted or loosened to a
   tautology.
2. `test_unstable_deselection_wiring.py`'s `_MARKER_EXPR_RE` matches only the **double-quoted**
   `-m "..."` form. `packaging.yml`'s current `-m packaging` is unquoted, so it would be silently
   classified as a node-id-selecting invocation and the new coverage would be vacuous. The
   invocation must be re-written in quoted form, and the per-file "this driver is known to use
   `-m`" guard extended to the new files so a future unquoting is caught rather than tolerated.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; no ROADMAP.md consultation was performed.

## Goals & Non-Goals

**Goals**:
- Make `create_test_model()` honor its `theory_name` parameter and default to logos, decoupling
  ~20 gating call sites in one change.
- Switch every non-bimodal-specific gating fixture identified by the audit from bimodal to logos,
  preserving each test's assertions byte-for-byte in substance.
- Apply `@pytest.mark.development` at per-test / per-parametrize granularity to the two tests whose
  subject is genuinely bimodal but whose claim is completeness, per TESTING_GUIDE 8.14's default
  granularity.
- Give all four packaging-suite gating invocations (across `packaging.yml`, `release.yml` ×2,
  `pypi-smoke.yml`) an `and not unstable and not development` selector, in the quoted form the
  wiring contract can actually see.
- Extend `test_unstable_deselection_wiring.py` to scan those three workflows, and widen
  `test_development_marker_application.py`'s containment contract to an enumerated allowlist
  without weakening its leak detection.
- Add a new executable contract proving no *new* bimodal-coupled test can enter a gating selection
  unclassified.
- Record before/after wall clocks for the actual gating selections.

**Non-Goals**:
- Changing bimodal's semantics, axioms, or frame-class constraints in any way.
- Widening any solve budget, `max_time`, or subprocess timeout as a remedy.
- Weakening, skipping, deleting, or `xfail`-ing any assertion to reach green.
- Touching `oracle/` (already carries the authorized `development` blanket, out of scope per the
  report's stated method).
- Fixing the dead-code helpers the report noted for hygiene (`tests/conftest.py::test_module_content`,
  `helpers.py::capture_model_output`/`run_example`) — zero callers, zero wall-clock cost, explicitly
  out of this task's cost scope.
- Re-deriving a pre-axiom baseline by reverting prior commits.

### Hard Constraints (binding on every phase)

These are restated inline here because a phase-local reading of this plan must not be able to miss
them:

1. **No budget widening as a remedy.** `TESTING_GUIDE.md` section 8.6 forbids it, and this code's
   own history is the local disproof: `test_build_example_bimodal_theory_countermodel` was widened
   once (10s → 30s) and failed anyway; `test_iteration_via_iterate_api` now measures 31.78s against
   its own 30s budget. If an implementer finds themselves typing a larger `max_time`, a larger
   `timeout=`, or a larger pytest-timeout value, the phase is being done wrong. The one permitted
   interaction with a budget is *retaining an existing one unchanged* (notably
   `test_theory_library_execution`'s `max_time=10`).
2. **No assertion weakening.** A logos substitution keeps the identical assertions against a cheap
   theory. A `development` marking keeps the test collectable and runnable under `-m development`.
   Neither disposition may delete an assertion, relax a comparison, add a `skip`, or convert a
   failure into an `xfail`.
3. **No bimodal semantics changes.** The frame axioms are correct and are not in question. Nothing
   in this plan edits `theory_lib/bimodal/semantic*`, `operators.py`, or any constraint definition.
4. **Every new or edited gating pytest invocation carries `and not development`** (and
   `and not unstable`), in the double-quoted `-m "..."` form, and is covered by
   `test_unstable_deselection_wiring.py`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A logos substitution silently changes a test's meaning (e.g. a countermodel that existed under bimodal does not under logos, or vice versa) | H | M | Each swap phase runs the affected file and reads the assertion text before editing; any test whose outcome flips is escalated as a blocker rather than "fixed" by relaxing the assertion. The `tests/cli/conftest.py` precedent shows the swap is outcome-preserving for this class of plumbing assertion. |
| `development` markings land before the packaging selectors are fixed, so the marked tests still run (and now fail) in `packaging.yml`/`release.yml`/`pypi-smoke.yml` | H | M | Strict phase ordering: Phase 6 `Depends on: 3, 5`. The selector fix (Phase 5) must be green before any marking is applied. |
| `packaging.yml`'s unquoted `-m packaging` makes the extended wiring contract vacuous | H | M | Phase 5 rewrites it in quoted form and extends the `checked_any_marker_expr` guard to the new files, so a future unquoting fails loudly instead of passing silently. |
| Widening `test_development_marker_application.py`'s containment contract degenerates into a tautology that no longer catches a leaking hook | H | M | The allowlist is an explicit, enumerated node-id/file set; the mixed-root leak assertion and the `>1000` collected-count floor are both retained unchanged. Phase 6 verification includes re-confirming the leak assertion is still genuinely RED against a deliberately-leaking hook (dry-run mutation, reverted immediately). |
| `EXPECTED_GATING_MARKER_INVOCATIONS` and the seven "six invocations" prose anchors drift out of sync in the same edit | M | M | Phase 5 derives the new count empirically from the extractor itself before editing any prose, and the constant's own test (`test_total_gating_marker_expression_count_matches_constant`) plus the anchor test are the phase's success criteria. |
| The `watch_development` step in `unstable-watch.yml` now collects `test_generate_then_execute[bimodal]`, spending 180s+ and reporting a timeout failure | L | H | Expected and acceptable — the watch is `continue-on-error: true` and non-gating; keeping the failure *observed* rather than hidden is precisely the marker's purpose. Recorded in the TESTING_GUIDE 8.14 "Currently marked" entry in Phase 6 so it is not later mistaken for a regression. |
| Baseline wall clocks measured on a loaded machine make the before/after table meaningless | M | M | Phase 1 records machine state (load, worker count, single-worker vs `-n 4`) alongside every figure, and Phase 8 re-measures under the identical invocation shape. The table reports paired invocations, never a cross-shape comparison. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4, 5 | 1 |
| 3 | 6 | 3, 5 |
| 4 | 7 | 2, 3, 4, 6 |
| 5 | 8 | 2, 3, 4, 5, 6, 7 |

Phases within the same wave can execute in parallel. Phases 2, 3, 4, and 5 touch disjoint file
sets (helpers/base; `builder/tests/unit/test_example.py`; the four CLI/e2e/packaging fixture files;
the three workflows plus the CI wiring contract and its prose anchors) and may be dispatched
concurrently.

---

### Phase 1: Record before-state wall-clock baselines [COMPLETED]

**Goal**: Capture, on current HEAD before any code change, the wall clock of every selection whose
improvement this task claims — so Phase 8's "after" figures compare against a real measurement
rather than the report's partial single-file numbers.

**Tasks**:
- [ ] Create `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/baselines/` and record
      machine state first: `uptime`, CPU count, whether anything else is running.
- [ ] Measure and record, each with its exact invocation string and `-n` setting:
  - [ ] Full gating parallel pass: `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial and not development" -n 4 -q --timeout=300 --timeout-method=thread`
  - [ ] Gating serial pass: same shape with `-m "xdist_serial and not packaging and not unstable and not development"`
  - [ ] `pytest tests/integration/test_performance.py tests/integration/test_error_handling.py tests/integration/test_timeout_resources.py -m "not development"` (report figure: 58 passed in 36.25s)
  - [ ] `pytest src/model_checker/builder/tests/unit/test_example.py -m "not development" --durations=20` (report figure: 17 passed in 33.96s, slowest 31.78s)
  - [ ] `pytest tests/cli/test_flag_matrix.py tests/e2e/test_batch_output_real.py src/model_checker/builder/tests/e2e/test_full_pipeline.py -m "not development" --durations=20`
  - [ ] Packaging suite as `packaging.yml` currently selects it: `pytest tests/packaging/ -v -m packaging --durations=20`. Record the observed outcome of `test_generate_then_execute[bimodal]` verbatim — per the report this is now expected to hit `subprocess.TimeoutExpired` at 180s, and the *before* state must record whether it did.
- [ ] Write all figures, invocations, and observed outcomes to
      `baselines/before-wall-clocks.md`.

**Timing**: 0.75 hours (mostly wall-clock waiting; the packaging leg alone is multi-minute)

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: The report's figures (36.25s for the three integration files, 33.96s for
`test_example.py`, 31.78s for `test_iteration_via_iterate_api`, >200s for
`test_generate_then_execute[bimodal]`) are hypotheses carried from a research-time measurement on a
possibly different machine state. Confirm each by re-running the invocation above and recording the
observed number; where a figure diverges materially from the report, record the divergence rather
than the report's number, and note it in `before-wall-clocks.md`.

**Files to modify**:
- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/baselines/before-wall-clocks.md` - new; the before-state record

**Verification**:
- `before-wall-clocks.md` exists and contains, for every bullet above, the literal invocation, the
  observed wall clock, and pass/fail counts.
- No source file under `code/` was modified in this phase (`git status --short code/` is clean).

---

### Phase 2: Make `create_test_model()` honor `theory_name`, defaulting to logos [COMPLETED]

**Deviation record** (per this phase's own Scope Hypothesis obligation): the report's "none of the
~20 call sites needs bimodal" hypothesis needed correction. `logos.DEFAULT_EXAMPLE_SETTINGS` is
itself expensive (`N=16, contingent=True, non_empty=True, non_null=True, disjoint=True`) — nothing
like bimodal's cheap `N=2, contingent=False` defaults — so any call site with an explicit N>=10
(under logos's eager 2^N state enumeration) or with no explicit N at all (silently inheriting
logos's heavy N=16 default) reproduces the exact same class of memory/time blowup this phase set
out to remove, just from the opposite theory. Empirically found (measured directly: N=5 -> 0.33s,
N=8 -> 1.21s, N=10 -> 22.1s under logos with default flags; one uncontrolled run reached 13.6GB
RSS and had to be killed) and fixed by pinning `theory_name='bimodal'` explicitly, with an
in-place comment, at five call sites whose settings were calibrated against bimodal's
representation rather than making any semantic or budget change:
- `test_performance.py::TestExecutionPerformance::test_complex_model_performance` (N=16)
- `test_performance.py::TestMemoryPerformance::test_memory_usage_complex` (N=10)
- `test_error_handling.py::TestErrorRecovery::test_graceful_degradation` (one sub-case has no
  explicit N, inheriting logos's heavy default)
- `test_error_handling.py::TestFrameworkErrorHandling::test_z3_timeout_handling` (N=10)
- `test_timeout_resources.py::TestPerformanceDegradation::test_performance_with_many_constraints`
  (N=10)
- `test_timeout_resources.py::TestResourceRecovery::test_memory_released_after_error` (N=10, x10
  loop iterations)

`tests/utils/base.py::BaseModelTest.create_model()` was extended with an optional `theory_name`
parameter (default `'logos'`, forwarded to `create_test_model()`) to make the pin possible at two
of the five call sites that go through it — a minimal, additive signature change, not a default
change for any other caller.

All 58 tests in the three-file selection pass (`tests/integration/test_performance.py` +
`test_error_handling.py` + `test_timeout_resources.py -m "not development"`): **31.60s**, vs.
Phase 1's baseline of 32.36s. This is real but not "material" in isolation — recorded honestly
rather than overstated. Two independent factors bound the achievable improvement for this specific
three-file aggregate, neither touched by this phase's stated scope: (a) the five pinned-bimodal
call sites above retain genuine bimodal solve cost (~10.4s combined, dominated by
`test_complex_model_performance`'s 6.59s, matching its pre-existing bimodal cost) because their
settings do not transfer to logos's representation without an outcome flip; (b) three CLI-
subprocess tests unrelated to `create_test_model()`
(`test_special_characters_in_names` 5.64s, `test_file_handles_closed` 4.20s,
`test_partial_results_on_error` 2.47s -- ~12.3s combined) were already the slowest tests in the
selection under bimodal too (report's own figures: 5.60s/4.28s/2.46s) — their cost is Python
subprocess-startup overhead, not bimodal Z3 solve cost, and they use inline
`theory_lib import bimodal` content strings independent of this helper. These three files are
candidates for Phase 7's own bimodal-reference scan, not this phase's stated file list.

**Goal**: Fix the shared helper so its ~20 gating call sites stop silently solving bimodal, without
touching any call site.

**Tasks**:
- [ ] In `code/tests/utils/helpers.py::create_test_model()`, replace the unconditional
      `from model_checker.theory_lib import bimodal; theory = bimodal.get_theory()` with a
      resolution that actually reads the `theory_name` parameter (via `model_checker.api.get_theory`
      or `model_checker.theory_lib`), and change the default from `'bimodal'` to `'logos'` so the
      signature matches the docstring's existing (currently false) claim.
- [ ] Update the docstring so it describes the real behavior, and add a short comment recording
      *why* logos is the default — cost decoupling from a theory under active construction,
      citing TESTING_GUIDE 8.14 the way `tests/cli/conftest.py`'s precedent comment does.
- [ ] Confirm `tests/utils/base.py::BaseModelTest.create_model()` needs no change beyond inheriting
      the new default (it forwards only `settings`); if it hardcodes anything, fix it the same way.
- [ ] Audit each of the ~20 call sites in `tests/integration/test_performance.py`,
      `test_error_handling.py`, and `test_timeout_resources.py` for an assertion that actually
      requires bimodal semantics. Per the report's initial read, none does. Any call site that
      genuinely does must be given an explicit `theory_name='bimodal'` rather than left to inherit
      the new default — do not change its assertion either way.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: "roughly 20 gating call sites across three files, none of which needs
bimodal" is a hypothesis. Confirm at implementation time with
`grep -rn "create_test_model\|create_model(" code/tests code/src` — record the actual call-site
count and the actual file list, and read every assertion in each caller before concluding no site
needs bimodal. If the real count or file set differs from the report's, record the difference in
the phase's commit message.

**Files to modify**:
- `code/tests/utils/helpers.py` - `create_test_model()` resolves `theory_name`; default `'logos'`; docstring corrected
- `code/tests/utils/base.py` - `BaseModelTest.create_model()` confirmed/adjusted to inherit the new default
- `code/tests/integration/test_performance.py`, `test_error_handling.py`, `test_timeout_resources.py` - only if a specific call site is found to genuinely require bimodal (explicit `theory_name='bimodal'`); otherwise untouched

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/integration/test_performance.py tests/integration/test_error_handling.py tests/integration/test_timeout_resources.py -m "not development" --durations=20` passes with the same test count as Phase 1's baseline (58, or whatever Phase 1 actually recorded) — no test lost, none newly skipped.
- Wall clock for that selection is recorded and is materially below the Phase 1 baseline.
- `grep -n "import bimodal" code/tests/utils/helpers.py` returns nothing (or only a comment).
- `cd code && PYTHONPATH=src pytest tests/utils -q` passes, if that directory collects any tests.

---

### Phase 3: Switch `builder/tests/unit/test_example.py`'s non-bimodal-specific solves to logos [NOT STARTED]

**Goal**: Remove the file's incidental bimodal exposure for the six tests whose subject is generic
BuildExample/iterate-API plumbing, including the 31.78s near-miss.

**Tasks**:
- [ ] Switch `TestBuildExampleBasic`'s inline module content (the five tests:
      `test_build_example_initialization`, `test_build_example_get_result`,
      `test_build_example_print_model`, `test_build_example_with_no_model`,
      `test_build_example_comparison_mode`) from `theory_lib.bimodal` to `theory_lib.logos`.
- [ ] Switch `TestBuildExampleIntegration::test_iteration_via_iterate_api` to logos, including its
      `from model_checker.theory_lib.bimodal.iterate import iterate_example` import, which must
      become the logos iterate entry point.
- [ ] Delete the now-obsolete `max_time: 30` justification comments that exist solely to explain
      bimodal's cost, replacing them with a comment recording the swap and its reason (mirroring
      `tests/cli/conftest.py`'s precedent comment). **Do not raise any budget**; if the logos solve
      no longer needs an explicit `max_time` at all, removing the override is acceptable but
      lowering-or-removing only — never raising.
- [ ] Leave `test_build_example_bimodal_theory_countermodel` entirely untouched in this phase — it
      is Phase 6's subject, and its existing timeout-vs-unsat discriminator must be preserved.
- [ ] Leave the mocked classes (`TestTimeoutSurfacing`, `TestThreeWayCheckResult`,
      `TestBuildExampleErrorHandling`) untouched — they perform no real solve.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: "five `TestBuildExampleBasic` tests plus `test_iteration_via_iterate_api`, and
ten mocked tests needing no change" is a hypothesis from the report's per-test timing table. Confirm
by running the file with `--durations=20` before editing and checking that exactly the tests with
non-zero durations are the ones being changed (minus
`test_build_example_bimodal_theory_countermodel`, deliberately deferred to Phase 6).

**Files to modify**:
- `code/src/model_checker/builder/tests/unit/test_example.py` - inline module content for `TestBuildExampleBasic` and `test_iteration_via_iterate_api` switched to logos; cost-justification comments replaced

**Verification**:
- `cd code && PYTHONPATH=src pytest src/model_checker/builder/tests/unit/test_example.py -m "not development" --durations=20` passes with the same collected count as Phase 1's baseline (17).
- The slowest duration in that run is materially below 31.78s, and no test in the file now runs
  within 20% of its own declared budget.
- `grep -c "bimodal" code/src/model_checker/builder/tests/unit/test_example.py` has decreased, and every
  remaining occurrence is inside `test_build_example_bimodal_theory_countermodel` or a docstring/comment.
- No `max_time`, `timeout`, or budget value in the file was increased (`git diff` reviewed
  specifically for numeric increases).

---

### Phase 4: Switch the remaining CLI / e2e / packaging plumbing fixtures to logos [NOT STARTED]

**Goal**: Close out the four inline fixtures the earlier `tests/cli/conftest.py` fix did not reach,
while explicitly preserving the one genuinely-bimodal gating test.

**Tasks**:
- [ ] `code/tests/packaging/test_cli_console_script.py`: switch `_TINY_EXAMPLE_CONTENT` from
      bimodal to logos (affects `test_real_example_run_through_console_script` and
      `test_console_script_runs_without_pythonpath`; both assert only generic console-script
      behavior).
- [ ] `code/tests/e2e/test_batch_output_real.py`: switch `_BATCH_EXAMPLE_CONTENT` to logos. Rename
      the two test functions only if their names embed "bimodal" in a way that would now be
      misleading, and if renaming, keep the assertions identical.
- [ ] `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py`: switch
      `test_print_impossible_flag_includes_impossible_states`'s inline module content to logos.
- [ ] `code/tests/cli/test_flag_matrix.py`: switch `_MAXIMIZE_EXAMPLE` to logos, following the
      pattern `_CVC5_COMPATIBLE_EXAMPLE` in the same file already uses, and carry over its
      explanatory comment style.
- [ ] **Explicitly do not touch** `test_full_pipeline.py::test_theory_library_execution`: it stays
      on bimodal with its existing `max_time=10`, because its `"World Histories"` assertion is
      bimodal's own model-rendering label and is not reproducible under another theory. Add a short
      comment above it recording that this retention is deliberate and audited, so a future sweep
      does not "finish the job" by swapping it.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: The enumerated file list above (four files, five test functions changed, one
deliberately retained) is a hypothesis. Confirm at implementation time by re-running the report's
own discovery command over these directories —
`grep -rn "theory_lib import bimodal\|theory_lib\.bimodal" code/tests/packaging code/tests/e2e code/tests/cli code/src/model_checker/builder/tests/e2e` —
and reconciling the hits against the list; any hit not in the list must be classified (real solve vs.
construct-only) before the phase closes.

**Files to modify**:
- `code/tests/packaging/test_cli_console_script.py` - `_TINY_EXAMPLE_CONTENT` → logos
- `code/tests/e2e/test_batch_output_real.py` - `_BATCH_EXAMPLE_CONTENT` → logos
- `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` - `test_print_impossible_flag_includes_impossible_states` fixture → logos; deliberate-retention comment added above `test_theory_library_execution`
- `code/tests/cli/test_flag_matrix.py` - `_MAXIMIZE_EXAMPLE` → logos

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/cli/test_flag_matrix.py tests/e2e/test_batch_output_real.py src/model_checker/builder/tests/e2e/test_full_pipeline.py -m "not development" --durations=20` passes with an unchanged collected count and a materially lower wall clock than Phase 1's baseline.
- `cd code && PYTHONPATH=src pytest tests/packaging/test_cli_console_script.py -v -m packaging` passes (this leg requires the `installed_venv` session fixture; if the sandbox cannot build it, record the skip reason explicitly rather than declaring the phase verified).
- `grep -n "World Histories" code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` still matches, and `test_theory_library_execution` still resolves bimodal with `max_time: 10` unchanged.
- No budget value increased anywhere in the diff.

---

### Phase 5: Bring the three packaging workflows under the gating-selector contract [NOT STARTED]

**Goal**: Give all four packaging-suite gating invocations an `and not unstable and not development`
selector in the quoted form the wiring contract can see, and extend that contract to scan them — so
Phase 6's markings are actually honored by every gating driver.

**Tasks**:
- [ ] `.github/workflows/packaging.yml`: change
      `python -m pytest tests/packaging/ -v -m packaging` to
      `python -m pytest tests/packaging/ -v -m "packaging and not unstable and not development"`.
      The quoting is load-bearing — `_MARKER_EXPR_RE` only matches `-m "..."`, so an unquoted
      expression would be classified as node-id-selecting and the new coverage would be vacuous.
- [ ] `.github/workflows/release.yml`: append `and not development` to **both** packaging-suite
      invocations (the `test-and-release` job's, and the PyPI-published-artifact verification
      job's), yielding `-m "packaging and not unstable and not development"`.
- [ ] `.github/workflows/pypi-smoke.yml`: same change to its single packaging-suite invocation.
- [ ] `code/tests/ci/test_unstable_deselection_wiring.py`:
  - [ ] Add `PACKAGING_YML`, `RELEASE_YML`, `PYPI_SMOKE_YML` path constants and append them to
        `_SCANNED_FILES` and to the `test_every_marker_expression_excludes_unstable_and_development`
        parametrize list.
  - [ ] Extend the `checked_any_marker_expr` guard's known-`-m`-bearing tuple to include the three
        new files, so a future unquoting or clause removal fails loudly instead of passing silently.
  - [ ] Extend `test_scanned_invocation_counts_match_known_shape` with the per-file expected
        invocation counts for the three new files, derived empirically (see Scope Hypothesis).
  - [ ] Update `EXPECTED_GATING_MARKER_INVOCATIONS` from 6 to the empirically derived new value, and
        rewrite the constant's long explanatory comment to record this change and its direction, in
        the same spirit as the existing seven→six narrative (which must not be deleted — the
        history is what stops the constant being "corrected" back).
  - [ ] Extend the module docstring: it currently says "Four drivers are in scope" and enumerates
        them; update to the new count and list.
- [ ] Update all seven `_INVOCATION_COUNT_ANCHORS` prose sites to the new count, keeping the
      `(must_contain, must_not_contain)` pairs coherent: `code/docs/core/TESTING_GUIDE.md` (four
      distinct phrasings), `code/src/model_checker/theory_lib/bimodal/tests/conftest.py`,
      `code/src/model_checker/theory_lib/bimodal/tests/README.md`, and
      `code/tests/ci/test_development_marker_application.py`'s docstring. Update the anchor tuples
      in `test_unstable_deselection_wiring.py` itself to match.
- [ ] Update `TESTING_GUIDE.md` section 8.9's "Where the deselection is wired" narrative and section
      8.14's corresponding claim to name the three newly in-scope drivers.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: The new invocation count is hypothesized at **10** (existing 6, plus
`packaging.yml` 1, `release.yml` 2, `pypi-smoke.yml` 1). This is a hypothesis about what
`_extract_pytest_invocations` actually sees, not a hand count of grep hits — the extractor filters
comment lines and `pip install` lines and joins backslash continuations, so its view may differ.
Confirm by running the extractor directly against each new file (e.g. a throwaway
`python -c` importing `_invocations_for`) and reading the returned list before writing any number
into the constant, the per-file count assertions, or the seven prose anchors. If the derived value
is not 10, use the derived value everywhere and record the discrepancy in the commit message.

`Commit Mode: atomic-batch` is declared here because the four workflow edits, the constant, the
per-file counts, and the seven prose anchors are checked by tests that only pass once *all* of them
land — intermediate per-file states are expected red and must not be committed individually.

**Files to modify**:
- `.github/workflows/packaging.yml` - packaging invocation quoted and given `and not unstable and not development`
- `.github/workflows/release.yml` - both packaging invocations given `and not development`
- `.github/workflows/pypi-smoke.yml` - packaging invocation given `and not development`
- `code/tests/ci/test_unstable_deselection_wiring.py` - three new scanned files, extended parametrize/guards/per-file counts, updated `EXPECTED_GATING_MARKER_INVOCATIONS` and anchor tuples, updated docstring
- `code/docs/core/TESTING_GUIDE.md` - four count anchors updated; 8.9 and 8.14 driver lists updated
- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` - count anchor updated
- `code/src/model_checker/theory_lib/bimodal/tests/README.md` - count anchor updated
- `code/tests/ci/test_development_marker_application.py` - docstring count anchor updated (containment logic itself is Phase 6's subject)

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/ci/test_unstable_deselection_wiring.py -v` passes in full,
  including `test_total_gating_marker_expression_count_matches_constant`,
  `test_scanned_invocation_counts_match_known_shape`, and every
  `test_invocation_count_anchor_is_current` parametrize case.
- `grep -n 'pytest tests/packaging/' .github/workflows/packaging.yml .github/workflows/release.yml .github/workflows/pypi-smoke.yml`
  shows all four invocations carrying a double-quoted `-m "packaging and not unstable and not development"`.
- `cd code && PYTHONPATH=src pytest tests/ci/ -v` passes (the whole CI-contract directory, to catch
  any sibling contract that also asserted the old count).
- `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable` still passes —
  `unstable-watch.yml` was not accidentally pulled into `_SCANNED_FILES`.

---

### Phase 6: Apply per-test `development` markings and widen the containment contract [NOT STARTED]

**Goal**: Quarantine the two completeness-claim tests from gating runs at per-test/per-parametrize
granularity, and amend the containment contract to permit exactly those two — without weakening its
ability to catch a leaking blanket.

**Tasks**:
- [ ] `code/tests/packaging/test_generate_then_execute.py`: replace the bare
      `@pytest.mark.parametrize("theory_name", registry.get_registered())` with a
      `pytest.param(name, marks=[pytest.mark.development] if name == "bimodal" else [])`
      comprehension, mirroring the `UNSTABLE_EXAMPLES` set-membership idiom TESTING_GUIDE 8.14 names
      as the established pattern. Prefer a module-level `_DEVELOPMENT_THEORIES = {"bimodal"}` set
      over an inline string comparison, so the reason has somewhere to be documented.
- [ ] Replace the now-stale `timeout=180` justification comment (which cites the pre-axiom ~100s
      figure) with an accurate one recording the measured >200s post-axiom behavior and why the
      remedy is the marker, not a larger timeout. **Leave `timeout=180` itself unchanged** — raising
      it is exactly the forbidden remedy.
- [ ] `code/src/model_checker/builder/tests/unit/test_example.py`: apply
      `@pytest.mark.development` to `test_build_example_bimodal_theory_countermodel` with a comment
      citing TESTING_GUIDE 8.14 and this task's audit. Preserve its existing timeout-vs-unsat
      discriminator and its `max_time: 30` exactly as they are.
- [ ] `code/tests/ci/test_development_marker_application.py`: widen
      `TestDevelopmentMarkerIsContainedToBimodal` from "bimodal tree only" to "bimodal tree plus an
      explicit, enumerated allowlist":
  - [ ] Add a module-level `_AUTHORIZED_NON_BIMODAL_DEVELOPMENT` constant listing the two node ids
        (with a comment recording, per test, *why* it is authorized and that it is a completeness
        claim rather than a soundness claim per 8.14's stated boundary).
  - [ ] Amend `test_no_development_marked_tests_outside_bimodal` and
        `test_no_leakage_when_bimodal_is_collected_alongside_the_rest_of_the_tree` to subtract the
        allowlist rather than to assert an empty set.
  - [ ] Add a new assertion that the allowlist is **exactly** matched — every entry is actually
        collected as `development`-marked, so a stale allowlist entry (e.g. after a rename) fails
        loudly instead of silently widening the exemption.
  - [ ] Leave `test_gating_expression_still_collects_the_non_bimodal_suite`'s `>1000` floor and its
        `bimodal_survivors == []` assertion untouched.
- [ ] `code/docs/core/TESTING_GUIDE.md` section 8.14: add the two markings to the "Currently marked"
      record, noting that they are per-test/per-parametrize (not a new blanket), citing the audit,
      and recording the expected consequence that `unstable-watch.yml`'s `watch_development` step
      will now collect and report the `test_generate_then_execute[bimodal]` timeout — which is the
      marker working as designed, not a regression.

**Timing**: 1.5 hours

**Depends on**: 3, 5

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: "exactly two tests outside the bimodal tree acquire `development`" is a
hypothesis. Confirm empirically after the markings land by running
`cd code && PYTHONPATH=src pytest -o addopts=--import-mode=importlib --collect-only -q -m development tests src/model_checker`
and diffing the collected node ids against
`src/model_checker/theory_lib/bimodal/tests` — the residue must be exactly the two allowlisted ids,
with their exact node-id spelling (including the `[bimodal]` parametrize suffix) taken from that
output rather than hand-written into the allowlist.

`Commit Mode: atomic-batch` is declared because the two markings and the contract widening are
mutually dependent — landing either half alone leaves `test_development_marker_application.py` red.

**Files to modify**:
- `code/tests/packaging/test_generate_then_execute.py` - per-parametrize `development` marking; corrected timeout justification comment (value unchanged)
- `code/src/model_checker/builder/tests/unit/test_example.py` - `@pytest.mark.development` on `test_build_example_bimodal_theory_countermodel`
- `code/tests/ci/test_development_marker_application.py` - allowlist constant; amended containment assertions; new exact-match assertion
- `code/docs/core/TESTING_GUIDE.md` - 8.14 "Currently marked" record extended

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/ci/test_development_marker_application.py -v` passes in
  full, including the mixed-root leak assertion and the `>1000` collected-count floor.
- `cd code && PYTHONPATH=src pytest -o addopts=--import-mode=importlib --collect-only -q -m "not development" tests/packaging/` shows `test_generate_then_execute[bimodal]` absent while every other theory's parametrize case is present.
- `cd code && PYTHONPATH=src pytest -o addopts=--import-mode=importlib --collect-only -q -m "not development" src/model_checker/builder/tests/unit/test_example.py` shows `test_build_example_bimodal_theory_countermodel` absent and the other 16 present.
- `cd code && PYTHONPATH=src pytest -m development src/model_checker/builder/tests/unit/test_example.py -v` still *collects and runs* the marked test — it is quarantined, not deleted or skipped.
- Leak-detection sanity check: temporarily remove the path filter from bimodal's
  `pytest_collection_modifyitems` hook, confirm
  `test_no_leakage_when_bimodal_is_collected_alongside_the_rest_of_the_tree` goes RED, then revert
  immediately. The widened contract must still catch a leaking blanket; record the observed RED in
  the commit message.
- `cd code && PYTHONPATH=src pytest tests/ci/ -v` passes as a whole.

---

### Phase 7: Add an executable no-bimodal-in-gating contract [NOT STARTED]

**Goal**: Convert this audit from a one-time sweep into a standing guard, so a *new* bimodal-coupled
test cannot silently enter a gating selection.

**Tasks**:
- [ ] Add `code/tests/ci/test_gating_selection_bimodal_decoupling.py`, following the established
      style of the sibling CI contracts (subprocess `--collect-only`, regex/grep source scanning,
      explicit module docstring explaining the mechanism and its known blind spots).
- [ ] The contract: for every file containing at least one test collected by a gating selection —
      both the main gating expression over `tests src/model_checker` and the packaging expression
      over `tests/packaging/` — and lying outside `theory_lib/bimodal/tests/`, if the file
      references bimodal as an example fixture (`theory_lib import bimodal`,
      `theory_lib.bimodal import`), it must appear in exactly one of two enumerated, commented
      constants:
  - [ ] `_SOLVE_FREE_BIMODAL_REFERENCES` — files the audit classified as construct-only, mocked, or
        string/registry-only (no `BuildExample`/`ModelDefaults` construction, therefore no Z3 solve).
        Seed from the report's "Items checked and ruled out" section, with a one-line reason per
        entry.
  - [ ] `_DELIBERATE_BIMODAL_GATING` — the single authorized real-solve retention,
        `builder/tests/e2e/test_full_pipeline.py::test_theory_library_execution`, with its reason
        (the `"World Histories"` assertion) and its existing `max_time=10`.
- [ ] Add an anti-vacuity assertion: the gating collection must be non-empty and the scanned file
      set non-empty, so a broken collection cannot make the contract pass by scanning nothing —
      the same failure mode `test_development_marker_application.py`'s docstring already warns about.
- [ ] Add an exact-match assertion on both constants: every listed file must still exist and still
      reference bimodal, so a stale entry (after a swap or a rename) fails loudly rather than
      silently widening the exemption.
- [ ] Document in the module docstring the contract's honest blind spot: it is a *static source*
      check at file granularity, not a runtime solve-cost measurement, so it catches a newly
      introduced bimodal fixture but cannot catch a bimodal solve reached through an indirection it
      does not textually see. Name the Phase 8 wall-clock record as the complementary evidence.

**Timing**: 1 hour

**Depends on**: 2, 3, 4, 6

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: The seed contents of `_SOLVE_FREE_BIMODAL_REFERENCES` are hypothesized from
the report's "Items checked and ruled out" list (`test_build_module_theories.py`,
`test_component_integration.py`, `test_serialize.py`, `test_comparison.py`, `test_package_marker.py`,
`test_project_version.py`, `test_package_imports.py`, `test_generated_projects.py`,
`test_project_edge_cases.py`, `test_loader.py`, `test_meta_data.py`, `test_theory_conformance.py`,
`theory_lib/tests/unit/test_error_handling.py`, `utils/tests/unit/test_parsing.py`,
`jupyter/tests/unit/test_adapters.py`, `output/tests/unit/test_markdown_formatter.py`,
`test_registry.py`, `test_layering.py`, plus the `tests/ci/*` meta-tests). This list is a hypothesis
about what the scan will actually surface after Phases 2-4 land. Derive the real list by running the
new contract's own scan first and letting it fail with the full set of unclassified files, then
classify each hit by reading it (real solve vs. construct-only) before adding it to a constant —
never bulk-paste the report's list into the allowlist without confirming each entry still matches.

**Files to modify**:
- `code/tests/ci/test_gating_selection_bimodal_decoupling.py` - new executable contract
- `code/docs/core/TESTING_GUIDE.md` - short cross-reference to the new contract from section 8.14 (or 8.6, wherever the sibling contracts are already indexed)

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/ci/test_gating_selection_bimodal_decoupling.py -v` passes.
- Genuine-RED demonstration: temporarily reintroduce a bimodal fixture into one of the files fixed
  in Phase 4, confirm the new contract goes RED naming that file, then revert. Record the observed
  RED in the commit message — a contract that has never been seen red is not evidence.
- Anti-vacuity: the contract's own non-empty assertions are exercised (deliberately point the
  collection at an empty root and confirm it fails rather than passes).
- `cd code && PYTHONPATH=src pytest tests/ci/ -v` passes as a whole.

---

### Phase 8: Record after-state wall clocks and verify the full gating suite [NOT STARTED]

**Goal**: Produce the paired before/after wall-clock record the task requires, and prove the
non-bimodal suite is still green and still fully gating.

**Tasks**:
- [ ] Re-run every invocation from Phase 1, under the identical shape (`-n` setting, marker
      expression, machine state recorded), and capture the after figures. For the packaging leg, use
      the *new* selector (`-m "packaging and not unstable and not development"`) alongside the old
      one, so the table shows both the selector change and the cost change.
- [ ] Write `baselines/after-wall-clocks.md` and a paired
      `baselines/before-after-comparison.md` with one row per selection: invocation, before, after,
      delta, and pass/fail counts before and after.
- [ ] Assert the no-regression property numerically, not qualitatively: collected counts for each
      gating selection are unchanged except for the two deliberately deselected tests, and the main
      gating expression still collects >1000 items (the floor `test_development_marker_application.py`
      already enforces).
- [ ] Run the full gating parallel pass and the serial pass to completion and confirm green.
- [ ] Run `cd code && PYTHONPATH=src pytest tests/ci/ -v` one final time as the contract-suite gate.
- [ ] Record explicitly, in the comparison file, that `test_theory_library_execution` remains the one
      gating test whose wall clock still depends on bimodal solve cost, with its retained
      `max_time=10` bound — so the claim in the summary is "one budgeted exception", not "zero",
      and is accurate.
- [ ] If any figure fails to improve materially, do **not** widen a budget or relax an assertion:
      record the finding, and escalate it as a blocker for a follow-up task.

**Timing**: 1 hour

**Depends on**: 2, 3, 4, 5, 6, 7

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: The expected improvements (the three integration files well below 36.25s, the
builder unit file well below 33.96s with no test near its budget, the packaging suite no longer
running `test_generate_then_execute[bimodal]` at all) are hypotheses. Confirm each by measurement and
record the observed number; a smaller-than-expected improvement is a finding to record, not a
number to adjust.

**Files to modify**:
- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/baselines/after-wall-clocks.md` - new
- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/baselines/before-after-comparison.md` - new; the paired table

**Verification**:
- Full gating parallel pass green: `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial and not development" -n 4 -q --timeout=300 --timeout-method=thread`
- Gating serial pass green: same with `-m "xdist_serial and not packaging and not unstable and not development"`
- Packaging suite green under the new selector: `cd code && PYTHONPATH=src pytest tests/packaging/ -v -m "packaging and not unstable and not development"`, and `test_generate_then_execute[bimodal]` is not collected.
- `cd code && PYTHONPATH=src pytest tests/ci/ -v` green.
- `before-after-comparison.md` exists with a numeric row per selection and no qualitative-only claims.

---

## Testing & Validation

- [ ] `cd code && PYTHONPATH=src pytest tests/ci/ -v` — all CI-wiring contracts green, including the
      extended `test_unstable_deselection_wiring.py`, the widened
      `test_development_marker_application.py`, and the new
      `test_gating_selection_bimodal_decoupling.py`.
- [ ] Full gating parallel pass and serial pass both green, with collected counts unchanged except
      for the two deliberately deselected tests.
- [ ] Packaging suite green under `-m "packaging and not unstable and not development"` in all four
      workflow invocations' shape.
- [ ] `nix flake check`'s `checks.default` (or the equivalent local `flake.nix` invocation) still
      passes, since `flake.nix` is one of the scanned gating drivers.
- [ ] Every logos-swapped test retains its original assertions — verified by reading the diff for
      assertion-text changes, not merely by a green run.
- [ ] No budget value (`max_time`, `timeout=`, `--timeout=`) was increased anywhere in the task's
      total diff: `git diff` reviewed specifically for numeric increases before final commit.
- [ ] Both new/amended contracts were observed RED at least once against a deliberate mutation, then
      reverted (Phases 6 and 7).

## Artifacts & Outputs

- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/plans/01_decouple-gating-tests-from-bimodal.md` (this plan)
- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/baselines/before-wall-clocks.md`
- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/baselines/after-wall-clocks.md`
- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/baselines/before-after-comparison.md`
- `code/tests/ci/test_gating_selection_bimodal_decoupling.py` (new executable contract)
- Modified: `code/tests/utils/helpers.py`, `code/tests/utils/base.py`,
  `code/src/model_checker/builder/tests/unit/test_example.py`,
  `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py`,
  `code/tests/packaging/test_cli_console_script.py`,
  `code/tests/packaging/test_generate_then_execute.py`,
  `code/tests/e2e/test_batch_output_real.py`, `code/tests/cli/test_flag_matrix.py`,
  `code/tests/ci/test_unstable_deselection_wiring.py`,
  `code/tests/ci/test_development_marker_application.py`,
  `.github/workflows/packaging.yml`, `.github/workflows/release.yml`,
  `.github/workflows/pypi-smoke.yml`, `code/docs/core/TESTING_GUIDE.md`,
  `code/src/model_checker/theory_lib/bimodal/tests/conftest.py`,
  `code/src/model_checker/theory_lib/bimodal/tests/README.md`

## Rollback/Contingency

Every phase commits independently (Phases 5 and 6 as declared atomic batches), so rollback is a
`git revert` of the offending phase commit. The riskiest revert boundaries:

- **Phase 5 alone must not be reverted while Phase 6 stands** — that would leave the two
  `development`-marked tests collected by unfixed packaging drivers, i.e. a red release gate. Revert
  6 first, then 5.
- **Phase 6 alone must not be reverted while Phase 5 stands** — harmless (the selectors simply
  deselect nothing new), so this direction is safe.
- If a logos substitution turns out to change a test's outcome, revert only that file's swap and
  escalate the specific test as a blocker; do not compensate by relaxing the assertion or raising a
  budget.
- If the wall-clock improvement in Phase 8 is materially smaller than expected, the correct
  contingency is a follow-up investigation task, not a budget change — TESTING_GUIDE 8.6 and this
  task's own history rule out widening as a convergent remedy.
