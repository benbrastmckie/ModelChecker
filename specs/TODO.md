---
next_project_number: 137
---

# TODO

## Task Order

*Updated 2026-08-05. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 133,134,135,136 | -- | architecture, testing |
| 2 | 127 | 133 | testing |
| 3 | 126 | 127 | architecture |

**Grouped by Topic** (indented = depends on parent):

### Architecture

134 [NOT STARTED] — Reconcile the declared N bound with the enforced one, and decide 
126 [BLOCKED] — Systematically refactor the repo into: 1) the core codebase conta

### Testing

133 [PLANNED] — Fix the pre-existing self-consistency failure in the oracle full-
  └─ 127 [BLOCKED] — Complete the oracle differential-suite regression baseline that t
135 [NOT STARTED] — Fix the non-deterministic segmentation fault when models are buil
136 [NOT STARTED] — Make the wall-clock performance assertions robust so they can rej

## Tasks

### 136. Ground wallclock performance budgets
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None

**Description**: Make the wall-clock performance assertions robust so they can rejoin the default test run. Several timing tests have budgets tighter than this codebase's real Z3 solve-time variance, so their pass/fail state changes between identical runs on the same commit -- directly demonstrated: two consecutive full sweeps at the same commit on the same machine produced different failure sets, with test_scaling_with_n[2-1.0] failing in one and passing in the other while test_simple_model_performance failed in both. Observed magnitudes: builder/tests/integration/test_performance.py::test_small_model_generation_completes_quickly and ::test_multiple_examples_process_efficiently both assert <500ms and both measure about 1.09s, roughly 2.2x over budget even at low load, so these two look like authoring defects rather than pure flakiness -- the budget may never have matched the real cost. Affected files, all currently carrying a module-level pytest.mark.slow and therefore quarantined out of the default run by the -m "not slow" clause in code/pyproject.toml addopts: tests/integration/test_performance.py, tests/integration/test_timeout_resources.py, and src/model_checker/builder/tests/integration/test_performance.py. Work: for each timing assertion decide which of three things it is -- (a) a real performance regression guard, which needs a budget derived from measured p95/p99 across repeat samples plus enough headroom for the roughly 20x Z3 solve-time variance documented in code/docs/core/TESTING_GUIDE.md section 8.6; (b) a correctness test wearing a stopwatch, which should assert the behaviour and drop the timing clause entirely; or (c) an obsolete assertion whose budget was never grounded in measurement, which should be deleted. Prefer (b) and (c): a wall-clock assertion on a shared development machine is a weak regression signal at best. Where a genuine performance guard is wanted, consider asserting relative scaling between two N values rather than absolute seconds, since a ratio is far more load-stable than a stopwatch. Definition of done: every one of these tests either passes reliably across at least five repeat full-suite samples or has been removed, the pytest.mark.slow markers are dropped from these files, and the coordination noted in task 135 is satisfied so the addopts filter clause can be deleted outright. Do not settle for widening budgets until they stop failing -- an unmeasured larger number is the same defect with a bigger constant. MEASURED OVER-HIDING (act on this first, it is cheap and independent of the budget work): the slow marker is applied as a module-level pytestmark across three whole files, so it quarantines 43 tests when only 5 justify quarantine. Measured with -m slow and the two crashers deselected: 3 failed, 38 passed, in 73 seconds total. So 38 of 43 quarantined tests pass and are hidden for no reason, at a cost of just over a minute; examples include test_file_handles_closed, test_keyboard_interrupt_cleanup, and test_memory_released_after_error, none of which assert on wall-clock time or use threads. Replace the module-level pytestmark in tests/integration/test_performance.py, tests/integration/test_timeout_resources.py, and src/model_checker/builder/tests/integration/test_performance.py with per-test @pytest.mark.slow on only: test_simple_model_performance, test_small_model_generation_completes_quickly, test_multiple_examples_process_efficiently (the 3 measured failures), test_scaling_with_n[2-1.0] (intermittent -- failed one full sweep and passed the next at the same commit), plus the two concurrency crashers which stay marked until task 135 lands. Keep models/tests/unit/test_semantic.py::test_max_n_itself_is_constructible marked: it legitimately allocates about 3.5GB over about 11s and exists to keep MAX_N honest. Verify the narrowing with repeat default sweeps rather than one, since the borderline timing tests are exactly the ones that flap. The three named failures assert <500ms against a measured ~1.09s, roughly 2.2x over even at low load, so treat them as authoring defects to re-ground rather than as flakes to widen.

---

### 135. Fix concurrent model building segfault
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None

**Description**: Fix the non-deterministic segmentation fault when models are built concurrently from multiple threads. Two tests reproduce it and both abort the whole pytest process (exit 139, Fatal Python error: Segmentation fault, Extension modules: cvc5.cvc5_python_base): tests/integration/test_performance.py::TestConcurrentPerformance::test_sequential_vs_concurrent (3 threads) and tests/integration/test_timeout_resources.py::TestResourceLimits::test_concurrent_model_building (5 threads). Both call create_test_model({N: 3}) from threading.Thread targets and crash during thread join. The crash is intermittent, not deterministic: the performance one reproduced on run 3 of 3 identical isolated invocations (runs 1 and 2 exited 0), so any single green run proves nothing and repeat sampling is required to validate a fix. This is independent of the N-bound work: N=3 is far below MAX_N so the new guard is a no-op on this path. Because a segfault kills the interpreter rather than failing a test, these two tests are the reason a full-suite sweep still cannot complete even after the N=64 memory hang was fixed -- a sweep aborts at whichever concurrency test it reaches first, producing no failure summary at all. Two mechanisms to investigate. First, the solver backend is resolved lazily per call through _get_backend_module() (solver/expressions.py, solver/backend.py:55, z3_shim.py:45) with a module-level _cached_module/_backend_module, so concurrent first-touch can race on that import and cache assignment; note cvc5.cvc5_python_base appears as the faulting extension even though solver defaults to z3, so establish why the cvc5 pythonic module is loaded at all on the default path before assuming the backend choice is irrelevant. Second, SemanticDefaults.__init__ calls self._reset_global_state() (models/semantic.py:83) whose documented job is to reset global state to avoid cross-example interference; resetting process-global solver state from several threads at once is inherently racy and theory subclasses override it to reset their own caches too. Decide the intended contract: either make concurrent model construction genuinely thread-safe (guard the backend cache and global-state reset with a lock, or make the state per-instance rather than global), or declare model construction single-threaded-only, document that, and replace these two tests with ones that assert the documented contract instead of exercising an unsupported pattern. Do not simply mark the tests skip or slow without recording that decision -- the crash risk stays in the product either way, and both files are already pytest.mark.slow, a marker nothing currently filters on. ADDITIONAL SCOPE (filter removal): the -m "not slow" filter is now wired into code/pyproject.toml addopts as an explicit, documented quarantine -- see the comment block above addopts. It is temporary. This task owns removing it: once the segfault is genuinely fixed (not skipped, not marked), delete the -m "not slow" clause from addopts entirely rather than relaxing it, drop the pytest.mark.slow markers from the two concurrency tests, and confirm an unfiltered full run is green across repeat samples -- the crash is intermittent at roughly 1 in 3, so a single green unfiltered run is not evidence. Note the filter currently hides these crashes rather than fixing them, which is exactly the state this task exists to end. Removing the filter also depends on the wall-clock budget work (task 136), since the same filter is quarantining those; coordinate so the clause is deleted only when BOTH are done, and record in the final summary that an unfiltered run was verified green and repeatable. CRASH SITE (observed): a second reproduction, this time SIGABRT (exit 134, Fatal Python error: Aborted) rather than SIGSEGV (exit 139), shows the faulting stack is two threads simultaneously inside model_checker/theory_lib/bimodal/semantic/core.py:580 build_frame_constraints, reached from core.py:88 __init__ -- i.e. concurrent BimodalSemantics construction, not concurrent solving. That the same test aborts under two different fatal signals across runs is consistent with memory corruption from unsynchronised access rather than a clean assertion inside the native library. Start the investigation at build_frame_constraints and at whatever process-global Z3/cvc5 context SemanticDefaults._reset_global_state touches during __init__, rather than at the solver check() path. Note also that the quarantined -m slow set cannot currently be measured as a whole: the run aborts at test_sequential_vs_concurrent partway through, so any characterisation of the slow set requires deselecting the two concurrency tests first.

---

### 134. Reconcile n bound contract and state space
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: architecture
- **Dependencies**: None

**Description**: Reconcile the declared N bound with the enforced one, and decide whether the 2^N state space must stay eager. A fail-fast guard now rejects N outside [1, MAX_N] in models/semantic.py (MAX_N=20) before all_states is materialized, because the prior unbounded path did not fail on a large N -- it allocated 2^N BitVecVals until the machine died (measured: 24GB RSS in ~60s at N=64, on a 30GB host, inside an uninterruptible Z3 C call that no Python-level pytest timeout can stop). That guard fixed the immediate hang but left the codebase asserting two different contracts. The declared contract says N in [1,64]: code/tests/utils/assertions.py:123 assert_settings_valid enforces 1<=N<=64 as a pure dict check that constructs nothing, so tests/integration/test_error_handling.py::TestEdgeCases::test_valid_n_boundary_values[32], [63], and [64] still pass while asserting a range that cannot actually be built; test_invalid_n_boundary_values treats 65 as the first invalid value; and code/src/model_checker/settings/tests/conftest.py:29 carries a {N: 65} # N too large fixture premised on the same 64 ceiling. tests/integration/test_system_boundaries.py:204/215/216 likewise exercise N=64 and N=32 through the dict-only validator. Separately, the settings layer (settings/settings.py) has _validate_setting_range available but applies no bound to N at all, so the only real enforcement is the new models-layer guard -- meaning direct API and create_test_model callers are covered but the settings pipeline still advertises no limit. Work: (1) pick one authoritative N ceiling and propagate it to assertions.py, the settings validation pipeline, the boundary-test parameters, the settings conftest fixture, and any docs stating a 64 limit, so a single source defines it; (2) decide the deeper design question of whether all_states must remain an eagerly materialized list of 2^N BitVecVals -- consumers across imposition/semantic/model.py, logos/iterate.py and models/semantic.py:191 iterate it directly, so laziness alone would not raise the feasible ceiling much and the exponential may be inherent, but that should be established rather than assumed; (3) if the ceiling stays at 20, remove or re-scope logos DEFAULT_EXAMPLE_SETTINGS N=16 headroom concerns and confirm no shipped theory default sits near the limit. Note the shape of this defect matches the oracle find_countermodel issue: a resource limit reported as a silent wrong answer rather than an error.

---

### 133. Fix oracle self consistency disagreements
- **Status**: [PLANNED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None
- **Research**: [133_fix_oracle_self_consistency_disagreements/reports/02_find-countermodel-contract.md]
- **Plan**: [133_fix_oracle_self_consistency_disagreements/plans/02_find-countermodel-contract.md]

**Description**: Fix the pre-existing self-consistency failure in the oracle full-scan report. oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFullScanReport::test_complexity_5_scan_self_consistent fails with AssertionError: Self-comparison produced N disagreements at complexity<=5 (assert N == 0) at test_cross_oracle_differential.py:1381. A self-comparison producing any disagreement means the oracle does not agree with itself on the same input, which is a correctness defect independent of any refactor. This failure is confirmed pre-existing: it reproduces at pre-refactor commit 6cfb7f48. It is NOT a resource or contention artifact -- it fails deterministically in a serial isolated run (which takes about 31 minutes). One open question to resolve as part of this work: the run at 6cfb7f48 reported 1 disagreement while the run at HEAD reported 3. With a single sample from each commit on a suite already known to be timing-sensitive, it is unresolved whether the disagreement count is stable, load-dependent, or genuinely worse post-refactor. Take repeat samples at both commits before drawing a conclusion. A prior disposition document incorrectly classified this test as a contention flake that passes in isolation; that classification is false and should be corrected wherever it is recorded.

---

### 132. Make oracle suite xdist safe
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None
- **Research**: [132_make_oracle_suite_xdist_safe/reports/01_oracle-xdist-safety.md]
- **Plan**: [132_make_oracle_suite_xdist_safe/plans/01_oracle-xdist-safety.md]
- **Summary**: [132_make_oracle_suite_xdist_safe/summaries/01_oracle-xdist-safety-summary.md]

**Description**: Make the oracle differential suite safe to run under pytest-xdist, or mark the unsafe parts serial-only. A full run under -n 6 produced seven failures where a serial run of the same tests produces two: the five extra failures were parallel-execution artifacts that all pass when re-run together serially in under three minutes. The affected tests are test_boundary_regression.py::TestExampleRegression::test_regression_all_active_examples[BM_CM_1-example_case7], test_soundness_regression.py::TestStateIsolationRegression::test_100_calls_mixed_temporal_depths, test_soundness_regression.py::TestStateIsolationRegression::test_sat_unsat_interleaving_stability, test_soundness_regression.py::TestOracleMFormulaBoundarySafe::test_oracle_m_formula_depth1_boundary_safe, and test_oracle_interface.py::TestEnrichedRoundTrip::test_enriched_vs_primitive_sat_agreement[some_past]. Because these tests assert on state isolation and call-sequence stability, distributing them across workers breaks the property under test. Add xdist_group markers (or an equivalent serialization mechanism) so the suite can be run in parallel without manufacturing false failures, and register the currently-unknown custom marks (differential, slow) which emit PytestUnknownMarkWarning on every run. Until this lands, any regression baseline for this suite must be generated serially, which takes roughly 90 minutes versus 45 under -n 6.

---

### 131. Fix oracle ternary sat regression
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None
- **Research**: [131_fix_oracle_ternary_sat_regression/reports/01_oracle-ternary-sat-regression.md]
- **Plan**: [131_fix_oracle_ternary_sat_regression/plans/01_fix-oracle-ternary-timeout.md]
- **Summary**: [131_fix_oracle_ternary_sat_regression/summaries/01_fix-oracle-ternary-timeout-summary.md]

**Description**: Fix the refactor-introduced regression in the oracle differential suite. oracle/bimodal_logic/tests/test_oracle_interface.py::TestTernarySerializationAll::test_all_sat_task_relation_ternary PASSES at pre-refactor commit 6cfb7f48 and FAILS on the current branch with AssertionError: Expected SAT for next_A (assert None is not None) at test_oracle_interface.py:1050 -- find_countermodel returns no model for a next_A formula that is expected to be satisfiable. The bisect endpoints are already established (green at 6cfb7f48, red at HEAD), so the work is to locate the responsible change in the core/theory_lib refactor and repair it. Note that a max_time overrun in this codebase surfaces as a wrong-answer result rather than an error, and Z3 solve times vary roughly 20x run-to-run on this machine (see code/docs/core/TESTING_GUIDE.md section 8.6), so rule out a timeout budget before concluding the semantics are wrong -- but the fact that the same test passes at the baseline commit under the same conditions points at a genuine behavioral change rather than timing. This regression is the sole remaining blocker on completing the core/theory_lib refactor.

---

### 130. Stabilize order dependent builder test
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None
- **Research**: [130_stabilize_order_dependent_builder_test/reports/01_order-dependent-test-diagnosis.md]
- **Plan**: [130_stabilize_order_dependent_builder_test/plans/01_deterministic-bimodal-builder-test.md]
- **Summary**: [130_stabilize_order_dependent_builder_test/summaries/01_deterministic-bimodal-builder-test-summary.md]

**Description**: Make builder/tests/unit/test_example.py::TestBuildExampleIntegration::test_logos_extensional_theory deterministic and correctly named. The test is order-dependent: at the pre-refactor baseline it fails when run in isolation and at file scope but passes within the full builder suite, and its outcome inverts depending on which modules are already imported, so it reports differently under different invocations. It is also misnamed: despite being called test_logos_extensional_theory, its body imports get_theory from theory_lib.bimodal and calls get_theory(['extensional']), exercising bimodal rather than logos. Establish what the test is actually meant to assert, rename it accordingly, and remove the hidden dependence on import or solver state so the outcome is identical in isolation, at file scope, and in a full-suite run. Its assertion on result['model_found'] depends on a Z3 solving outcome, so verify whether the countermodel expectation itself is sound for the theory the body actually loads.

---

### 129. Triage preexisting test failure backlog
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: Task 128, Task 130
- **Research**: [129_triage_preexisting_test_failure_backlog/reports/01_known-failures-baseline.md]
- **Plan**: [129_triage_preexisting_test_failure_backlog/plans/01_verify-fixes-baseline-doc.md]

**Description**: Triage and document the pre-existing test failure backlog so future refactors can diff cleanly against a known-good baseline. A full sweep (PYTHONPATH=code/src pytest code/src/model_checker/ code/tests/) currently reports 27 failures against 2148 passing, all of which reproduce at the pre-refactor baseline commit 6cfb7f48 and are therefore unrelated to the core/theory_lib refactor. They fall into two groups. The larger group is environment-sensitive: roughly 16 timing and resource tests across tests/integration/test_performance.py, tests/integration/test_timeout_resources.py, and builder/tests/integration/test_performance.py, whose pass/fail state flips with machine load (a repeat sweep varied between 27 and 30 failures). These should either be marked resource-dependent, given explicit tolerances, or moved behind an opt-in marker so that a default run is deterministic. The smaller group is genuine defects worth fixing: a ModuleNotFoundError for a missing tests.fixtures.example_data module, an AttributeError from mock-spec misuse ('assert_and_track' is not a valid assertion), and ValueError expectation drift in error-handling tests ('Empty token list' and 'The expression [] is incomplete'). Deliver a categorized known-failures baseline document plus fixes for the genuine defects.

---

### 128. Fix witness error theory attribute
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None
- **Research**: [128_fix_witness_error_theory_attribute/reports/01_witness-error-theory-contract.md]
- **Plan**: [128_fix_witness_error_theory_attribute/plans/01_fix-witness-theory-tests.md]
- **Summary**: [128_fix_witness_error_theory_attribute/summaries/01_fix-witness-theory-tests-summary.md]

**Description**: Resolve the contradiction between the witness error classes and their tests. theory_lib/tests/unit/test_error_handling.py asserts that WitnessRegistryError(...).theory equals 'exclusion' and WitnessConstraintError(...).theory equals 'exclusion', but both classes inherit WitnessError -> TheoryError without setting any theory default, so .theory is None and both tests fail. These failures predate the core/theory_lib refactor: theory_lib/errors.py carries no commit from it. Decide the correct contract and implement it: either the witness error hierarchy should bind a theory identifier (noting that the refactor deliberately eliminated hardcoded theory-name literals from the core and upper layers, so a hardcoded 'exclusion' default would need justification, most likely via a constructor argument supplied at the raise sites), or the tests encode a stale expectation and should assert the actual contract. Whichever way it resolves, the two failing tests must end up passing and the reasoning recorded.

---

### 127. Close oracle suite regression baseline
- **Status**: [BLOCKED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: Task 131, Task 132, Task 133
- **Research**: [127_close_oracle_suite_regression_baseline/reports/01_oracle-baseline-environment.md]
- **Plan**: [127_close_oracle_suite_regression_baseline/plans/01_close-oracle-regression-baseline.md]
- **Summary**: [127_close_oracle_suite_regression_baseline/summaries/01_close-oracle-regression-baseline-summary.md]

**Description**: Complete the oracle differential-suite regression baseline that the core/theory_lib refactor could not finish. The 550-test suite in oracle/bimodal_logic/tests/ has never completed a full run in the development sandbox: pytest-xdist is unavailable (package index unreachable), forcing a fully serial run of roughly 90 minutes, and serial attempts were killed by resource contention from concurrent sessions at about 91% through. Collection count (550) and the 5 xfail(strict=True) marker line locations are already pinned and verified clean. Install or vendor pytest-xdist, or run on dedicated/isolated resources, then commit baselines/oracle-run.txt and baselines/junit-oracle.xml, flip the refactor plan's Phase 2 heading from [PARTIAL] to [COMPLETED], and re-run code/scripts/verify-refactor.sh without --skip-oracle so Step 6 exercises the full suite. Completing this is the sole remaining blocker to marking the core/theory_lib refactor task COMPLETED.

---

### 126. Refactor repo core infrastructure theory lib
- **Status**: [BLOCKED]
- **Task Type**: general
- **Topic**: architecture
- **Dependencies**: Task 127
- **Research**: [126_refactor_repo_core_infrastructure_theory_lib/reports/01_team-research.md]
- **Plan**: [126_refactor_repo_core_infrastructure_theory_lib/plans/01_core-theory-lib-refactor.md]
- **Summary**: [126_refactor_repo_core_infrastructure_theory_lib/summaries/05_phases-22-26-summary.md]

**Description**: Systematically refactor the repo into: 1) the core codebase containing all appropriate utilities and resources (the model-checker infrastructure); 2) the theory_lib consisting of the bimodal, exclusion, imposition, and logos theories; and 3) remove the spatial subtheory from the logos theory. If it makes more sense, move theory_lib/ into src/, making any other natural restructuring as needed. Systematically review the modules throughout the codebase to design a full refactor improving organization, code quality, and uniformity, with a standardized set of modules for each theory/subtheory as appropriate, making systematic changes however improves the final state of the repo.

---

### 125. Release engineering and pypi rehearsal
- **Effort**: 2.5 hours
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: packaging
- **Dependencies**: Task 123, Task 124
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [125_release_engineering_and_pypi_rehearsal/plans/01_release-engineering-pypi-rehearsal.md]
- **Summary**: [125_release_engineering_and_pypi_rehearsal/summaries/01_release-engineering-summary.md]

**Description**: Covers plan phase 13 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Release Engineering and Rehearsal'). Requires the Nix-verified build (flake task) as the ground-truth build target for parity checks, and the refreshed docs/CHANGELOG (documentation task) for the release checklist narrative. No agent publishes to PyPI or pushes to git in this task -- per .claude/rules/pr-prohibition.md, publish and push are strictly user-only actions. Goal: fix .github/workflows/release.yml (`cd Code` -> `cd code` in both jobs); reconcile .github/RELEASE_SETUP.md with the single actual workflow; migrate the publish job to PyPI Trusted Publishing (OIDC) via pypa/gh-action-pypi-publish@release/v1 in a separate, environment-gated (pypi) job with permissions: id-token: write, dropping the long-lived PYPI_API_TOKEN; add `twine check --strict`; add a TestPyPI rehearsal step and perform a local rehearsal (`python -m build`, `check-wheel-contents`, and a wheel-content/hash parity diff vs `pip download --no-deps model-checker==1.2.12`, run NixOS-safe inside `nix develop`); confirm the built artifact is named model_checker-<version>, not bimodal_logic; confirm the final version number (set provisionally in the package-identity task) and prepare a step-by-step publish checklist ending in the user-only actions -- user pushes the branch/tag and either invokes /merge or triggers the release workflow. Explicitly mark publish + push as user-gated in the checklist; the agent performs neither. Verification: release.yml casing fixed; OIDC Trusted Publishing configured; `python -m build` produces a model_checker-<version> wheel/sdist excluding the oracle directory; `check-wheel-contents` clean; wheel-content parity diff vs 1.2.12 reviewed and documented; `twine check --strict dist/*` passes; TestPyPI rehearsal succeeds; publish checklist handed to the user with publish/push explicitly marked user-only.

---

### 124. Documentation refresh for the restored framework
- **Effort**: 2 hours
- **Status**: [COMPLETED]
- **Task Type**: markdown
- **Topic**: packaging
- **Dependencies**: Task 122
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [124_documentation_refresh_for_the_restored_framework/plans/01_docs-refresh.md]
- **Summary**: [124_documentation_refresh_for_the_restored_framework/summaries/01_docs-refresh-summary.md]

**Description**: Covers plan phase 12 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Documentation Refresh'). Requires the full green test gate (prior wave) to be established so docs describe the definitive, working state rather than in-progress restoration. Goal: fix root README.md's `pip install model-checker[jupyter]` quick-start and the dead link to jupyter/README.md; ensure the four-theory framing (logos, bimodal, exclusion, imposition) matches the actual registered AVAILABLE_THEORIES set; fix code/README.md's `cd ModelChecker/Code` casing to `cd code` and update its component table to reflect restored builder/iterate and the relocated oracle directory; reconcile CLAUDE.md's canonical test command and architecture description with reality; add an honest code/CHANGELOG.md entry for this release (identity restore, theory set, first-order removal, oracle relocation); check docs/usage/SEMANTICS.md for stale first-order references and code/scripts/README.md for the dead link to the deleted docs/theory/QUANTIFIER_SOLVERS.md, fixing both; cross-check that code/MANIFEST.in (edited by the package-identity task) resolves against real paths -- read-only verification here, do not re-edit MANIFEST.in itself; as a non-blocking follow-up, seed specs/ROADMAP.md with the durable identity decision. Verification: no dead links in README.md/code/README.md/code/scripts/README.md; CLAUDE.md's test command matches the actual canonical command; CHANGELOG.md has an honest entry; no stale first-order or bimodal-logic references remain in user-facing docs.

---

### 123. Rewrite the nix flake for multisystem build and te
- **Effort**: 2.5 hours
- **Status**: [COMPLETED]
- **Task Type**: nix
- **Topic**: packaging
- **Dependencies**: Task 122
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [123_rewrite_the_nix_flake_for_multisystem_build_and_te/plans/01_nix-flake-multisystem-rewrite.md]
- **Summary**: [123_rewrite_the_nix_flake_for_multisystem_build_and_te/summaries/01_nix-flake-multisystem-rewrite-summary.md]

**Description**: Covers plan phase 11 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Nix Flake Rewrite'). Requires the full test suite already green (prior task) so the flake's checks.default target validates a known-good state rather than surfacing unrelated failures, and the finalized package identity (pyproject.toml from the package-identity task) as the packages.default build target. Goal: rewrite root flake.nix to be multi-system (flake-utils or an explicit system list, replacing the hardcoded x86_64-linux); add packages.default via nixpkgs-native `buildPythonPackage { pyproject = true; }` against python3Packages.z3 (NOT the PyPI z3-solver wheel), with networkx included; add checks.default running the canonical pytest suite so `nix flake check` is a real gate; provide a devShell that subsumes what code/shell.nix offered (z3, setuptools, pip, networkx, pytest), making the ../BimodalHarness path strictly optional (no failure/warning path required for a standalone checkout); commit flake.lock; delete code/shell.nix (no backwards-compat layer); verify `nix build` and `nix flake check` succeed locally. This task exists specifically because pip install is impractical on NixOS -- the flake is the primary NixOS-native install/test path. Verification: `nix build` succeeds and produces a working model-checker package; `nix flake check` runs and passes the pytest suite; devShell provides a working development environment without requiring ../BimodalHarness; code/shell.nix removed.

---

### 122. Rootcause crossoracle differential and establish t
- **Effort**: 4 hours
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 118, Task 121
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [122_rootcause_crossoracle_differential_and_establish_t/plans/01_rootcause-differential-green-gate.md]
- **Summary**: [122_rootcause_crossoracle_differential_and_establish_t/summaries/01_rootcause-differential-green-gate-summary.md]

**Description**: Covers plan phases 9-10 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Root-Cause Cross-Oracle Differential Failures' and 'Full Green Test Gate'). Requires the oracle already relocated (bootstrap task) and the test suite widened/collectible (package identity + test infra task). Goal (differential): with the oracle differential harness moved to oracle/bimodal_logic/, confirm the in-package theory_lib/bimodal suite passes without BimodalHarness present; for the relocated test_cross_oracle_differential.py, run it in its new oracle context and root-cause the 2-4 consistent failures noted in research (regression vs. environment/xfail behavior), fixing or correctly marking and documenting them; record the definitive bimodal pass/fail tally against the Phase 1 baseline captured by the bootstrap task. Goal (green gate): run the full model_checker suite to completion (all theories + top-level tests) using pytest-xdist, achieving green or documented/justified skips/xfails only; run the relocated oracle suite separately to green; smoke-test the CLI end-to-end (`python -m model_checker --help`, a representative example run, and --maximize/--save paths if quick); record final pass counts and runtimes as the release baseline in the task directory. Verification: in-package bimodal suite green without BimodalHarness; differential failures root-caused and documented; full suite green (or documented skips/xfails) via pytest-xdist; oracle suite green; CLI smoke tests pass; release baseline recorded.

---

### 121. Restore package identity and repair test infrastru
- **Effort**: 3.5 hours
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 118, Task 119, Task 120
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [121_restore_package_identity_and_repair_test_infrastru/plans/01_restore-package-identity-test-infra.md]
- **Summary**: [121_restore_package_identity_and_repair_test_infrastru/summaries/01_restore-package-identity-test-infra-summary.md]

**Description**: Covers plan phases 7-8 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Restore Package Identity (pyproject.toml, MANIFEST.in)' and 'Repair Test Infrastructure'). Requires the oracle relocation and all theory registrations (logos, exclusion, imposition) to be complete so package-data include/exclude and testpaths can be finalized. Goal (identity): in code/pyproject.toml set [project] name = "model-checker"; choose next version (recommend 1.3.0 given the restored theory set and first-order removal since PyPI 1.2.12, final number confirmed in the release task); restore description/keywords/classifiers to the framework identity; restore dependencies to match PyPI 1.2.12 intent (z3-solver>=4.8.0, networkx>=2.0, jupyter/all optional-dependency extras: ipywidgets, matplotlib, networkx, jupyter, ipython); keep only the `model-checker = "model_checker.__main__:run"` console script, removing the bimodal-logic script and the [project.entry-points."bimodal_harness.oracle_providers"] table (already moved to oracle/ by the bootstrap task); ensure [tool.setuptools.packages.find] and package-data include model_checker (with restored jupyter/ notebooks) and exclude the relocated oracle directory; reconcile version single-sourcing in model_checker/__init__.py's get_model_checker_version(); update code/MANIFEST.in to keep theory_lib/{logos,bimodal,exclusion,imposition} and jupyter/ includes, removing references to paths that no longer exist. Goal (test infra): widen [tool.pytest.ini_options] testpaths beyond bimodal-only to cover code/tests/ and all registered theories (or remove the pin so `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker` works per CLAUDE.md); fix or delete stale top-level tests referencing formerly-deleted modules (tests/e2e/test_simple_output_verify.py, tests/integration/test_model_building_sync.py, tests/integration/test_system_imports.py, tests/utils/helpers.py) -- repair against restored builder/output modules where meaningful, delete where obsolete; add pytest-xdist (dev dependency + -n auto usage documented) to parallelize the slow bimodal suite; confirm `PYTHONPATH=code/src pytest code/tests/ --collect-only -q` reports zero collection errors. Verification: pyproject.toml declares model-checker identity with restored deps/entry-point; MANIFEST.in resolves against real paths; zero pytest collection errors across code/tests/ and code/src/model_checker.

---

### 120. Restore and port the exclusion and imposition theo
- **Effort**: 6 hours
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 119
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [120_restore_and_port_the_exclusion_and_imposition_theo/plans/02_port-exclusion-imposition.md]

**Description**: Covers plan phases 5-6 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Restore and Port the exclusion Theory' and 'Restore and Port the imposition Theory'). This is the highest-risk work in the plan: both theories restore from a PRE-solver-migration commit (abb3bf7d^), predating z3_shim, model_checker.solver, and the modular models.semantic/models.proposition/models.structure package structure, and must be ported to the current API. Use the already-current-API bimodal and logos theories (from the prior task) as the concrete reference pattern for the port. Goal (exclusion): `git checkout abb3bf7d^ -- code/src/model_checker/theory_lib/exclusion`; port imports/APIs from pre-migration to current: model_checker.z3_shim, model_checker.solver (is_true/is_false), models.semantic.SemanticDefaults, models.proposition.PropositionDefaults, models.structure.ModelDefaults, syntactic.atoms.get_atom_sort, and bimodal witness modules; register exclusion in AVAILABLE_THEORIES; get theory_lib/exclusion/tests/ to collect and pass; commit per green sub-step. Goal (imposition): `git checkout abb3bf7d^ -- code/src/model_checker/theory_lib/imposition`; apply the same import/API porting recipe established for exclusion; register imposition in AVAILABLE_THEORIES; get theory_lib/imposition/tests/ to collect and pass; commit per green sub-step. If porting exceeds budget, the plan's documented fallback is to ship with logos+bimodal registered and follow up on exclusion/imposition separately -- but the goal is full restoration; treat the fallback as a last resort. Verification: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/exclusion -q` and `.../imposition -q` both green; both registered in AVAILABLE_THEORIES; no import errors against current z3_shim/solver/models.* API.

---

### 119. Restore core infrastructure and reconcile the logo
- **Effort**: 4.5 hours
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 118
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [119_restore_core_infrastructure_and_reconcile_the_logo/plans/01_restore-core-infra-logos.md]
- **Summary**: [119_restore_core_infrastructure_and_reconcile_the_logo/summaries/01_restore-core-infra-logos-summary.md]

**Description**: Covers plan phases 3-4 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Restore Core Infrastructure (builder, iterate, jupyter, output)' and 'Reconcile and Register the logos Theory'). Requires task branch and confirmed restore-point SHAs from the bootstrap task. Goal: restore deleted general-purpose infrastructure via `git checkout 013a486c^ -- code/src/model_checker/builder`, `git checkout c21b3709^ -- code/src/model_checker/iterate code/src/model_checker/jupyter`, and `git checkout 71ef79a1^ -- code/src/model_checker/output/manager.py code/src/model_checker/output/progress`; reconcile imports via smoke tests for model_checker.builder, model_checker.iterate, model_checker.output.manager, fixing any references broken since the (post-solver-migration) restore point; verify `PYTHONPATH=code/src python -m model_checker --help` and `python code/dev_cli.py --help` both run without ModuleNotFoundError; commit per green sub-step. Then reconcile theory_lib/logos/: confirm its `from .iterate import ...`/`model_checker.iterate` imports now resolve (iterate just restored), fix any residual import paths; verify the first-order subtheory removal (commit e9734a27) is intact with no dangling references; register logos (and its retained subtheories) in theory_lib's AVAILABLE_THEORIES; get theory_lib/logos/tests/ to collect and pass via `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos -q`. Verification: builder/iterate/jupyter/output.manager import cleanly; CLI --help commands work; logos registered in AVAILABLE_THEORIES; logos test suite green.

---

### 118. Bootstrap branch baseline capture and oracle reloc
- **Effort**: 3 hours
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: None
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [118_bootstrap_branch_baseline_capture_and_oracle_reloc/plans/01_branch-baseline-oracle-relocation.md]
- **Summary**: [118_bootstrap_branch_baseline_capture_and_oracle_reloc/summaries/01_branch-baseline-oracle-relocation-summary.md]

**Description**: Covers plan phases 1-2 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Branch, Inventory, and Baseline Capture' and 'Separate the Bimodal-Oracle/Harness Layer'). Goal: create a task branch (e.g. task-117-restore-model-checker) off master (do not push); record a pre-change baseline (run the live bimodal suite once for pass/fail + timing, snapshot the currently-failing `PYTHONPATH=code/src pytest code/tests/ --collect-only -q` and `python -m model_checker --help` output, both saved under the task directory); inventory the restore-point SHAs from the plan's git-restore table and confirm each restore source path exists via `git ls-tree <sha>^ -- <path>` (013a486c^ for builder/, c21b3709^ for iterate/jupyter, 71ef79a1^ for output/manager.py+progress/, abb3bf7d^ for exclusion/imposition). Then relocate the bimodal-oracle/harness layer: move code/src/bimodal_logic/ (cli.py, provider.py, serialization.py, translation.py, __init__.py, tests/) to a new top-level oracle/bimodal_logic/ directory at repo root; delete the stale code/src/bimodal_logic.egg-info/; move the cross-oracle differential harness/tests that depend on BimodalHarness (theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py and any oracle-only helpers) alongside the oracle; give the oracle its own minimal dev setup (own pyproject.toml or a README documenting PYTHONPATH-based standalone development and the bimodal_harness.oracle_providers entry point); confirm nothing under code/src/model_checker/ imports bimodal_logic (fix-forward any residual references); verify the oracle's own tests still collect from its new location. Verification: branch exists; baseline artifacts saved under the task directory; oracle/bimodal_logic/ exists with its own tests collecting; code/src/model_checker/ has zero references to bimodal_logic. This is the foundational task all others build on.

---

### 117. Review cli pypi parity nix flake release
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 118, Task 119, Task 120, Task 121, Task 122, Task 123, Task 124, Task 125
- **Research**:
  - [117_review_cli_pypi_parity_nix_flake_release/reports/01_team-research.md]
  - [117_review_cli_pypi_parity_nix_flake_release/reports/03_team-research.md]
- **Plan**: [117_review_cli_pypi_parity_nix_flake_release/plans/03_stabilize-and-release-closeout.md]
- **Summary**: [117_review_cli_pypi_parity_nix_flake_release/summaries/03_stabilize-and-release-closeout-summary.md]

**Description**: Review and stabilize the repo after recent revisions: verify the CLI works, audit discrepancies with the model-checker package on PyPI, build a Nix flake for testing on NixOS (pip install is impractical there), complete full testing, and prepare a top-quality release to push to PyPI

---

### 116. Draft email modelchecker architecture
- **Status**: [COMPLETED]
- **Task Type**: markdown
- **Topic**: documentation
- **Dependencies**: None

**Description**: Draft a brief email for a Python expert explaining how the ModelChecker supports modular extensions: each model structure is built over shared general infrastructure and supports a range of operators supplied semantic clauses using that model structure's resources. Explain the basic architecture and the pipeline by which logical claims are processed into SMTlib, solved, then passed back to print a model, where key methods are provided by each operator. Culminate with code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py as a worked example. Draw on docs/ and distributed README.md files as appropriate.
