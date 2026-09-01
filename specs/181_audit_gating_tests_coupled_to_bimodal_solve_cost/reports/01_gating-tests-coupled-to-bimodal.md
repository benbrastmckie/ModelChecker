# Audit: Gating Tests Coupled to Bimodal Solve Cost

## Scope and method

Enumerated every test that (a) runs in a release-gating selection, (b) lives outside
`code/src/model_checker/theory_lib/bimodal/tests`, and (c) constructs or solves a bimodal
example. Entry points used: `grep -rl` for `theory_lib import bimodal` / `theory_lib.bimodal` /
`"Bimodal"` across `code/`, followed by per-file reads to classify each hit as (i) a real Z3
solve (via `BuildExample.__init__`/`get_result()`, `ModelDefaults.__init__`, or a CLI subprocess
that runs an example), (ii) a construct-only hit (`BuildModule`/`BuildProject`/`get_theory()`
with no solve triggered), or (iii) a string/comment mention with no runtime cost. `oracle/` was
excluded throughout: its own bimodal-only tree already carries the authorized `development`
blanket (TESTING_GUIDE.md 8.14), and it is not "outside the bimodal tree" in the sense this task
means — it is a second, deliberately bimodal-only differential harness, not an incidental user of
bimodal as a fixture.

Five release-gating drivers were identified and inventoried (one more than the four the existing
`test_unstable_deselection_wiring.py` contract scans — see Finding 1 below):

| Driver | Selection | Scans `not development`? |
|---|---|---|
| `.github/workflows/tests.yml` (2 invocations) | `pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial and not development"` (+ serial pass) | Yes |
| `flake.nix` `checks.default` (2 invocations) | same shape | Yes |
| `.github/workflows/differential-tests.yml` | node-id selects `TestCIGate` (soundness only) | N/A by design |
| `oracle/run-oracle-suite.sh` (2 invocations) | `-m "not xdist_serial and not slow and not unstable and not development"` | Yes |
| **`.github/workflows/packaging.yml`** | `pytest tests/packaging/ -v -m packaging` | **No — not scanned, no `development` filter at all** |

## Finding 1 (highest priority): `packaging.yml` is an unaudited fifth gating driver, and it pays full, unshielded bimodal solve cost

`.github/workflows/packaging.yml` (`on: push` to every branch, `on: pull_request`) runs
`cd code && python -m pytest tests/packaging/ -v -m packaging` — this is a real, currently-gating
CI job. It is **not** one of the four files `code/tests/ci/test_unstable_deselection_wiring.py`
scans (`_SCANNED_FILES = [TESTS_YML, FLAKE_NIX, DIFFERENTIAL_TESTS_YML, RUN_ORACLE_SUITE_SH]`),
and its `-m` expression carries no `and not development` clause at all — so even if a
`development` marker were later applied inside `code/tests/packaging/`, this driver would still
collect it.

Two more workflows run the identical `code/tests/packaging/` suite and share the same gap:
`.github/workflows/release.yml`'s `test-and-release` job and its PyPI-published-artifact
verification job, and `.github/workflows/pypi-smoke.yml`, each run
`python -m pytest tests/packaging/ -v -m "packaging and not unstable"` — one step further than
`packaging.yml` (it does exclude `unstable`) but still with no `and not development` clause. Any
fix to this gap (adding `packaging.yml` to `_SCANNED_FILES` and giving its invocation `and not
development`) should cover all three of these workflows' packaging-suite invocations, not just
`packaging.yml`'s, since all three would collect the same `development`-marked
`test_generate_then_execute[bimodal]` case recommended below.

Two concrete tests inside it construct/solve bimodal, unguarded:

1. **`code/tests/packaging/test_generate_then_execute.py::test_generate_then_execute[bimodal]`**
   (`pytestmark = [pytest.mark.packaging, pytest.mark.slow]`). Parametrized over
   `registry.get_registered()`, so one parametrize case runs `BuildProject('bimodal').generate()`
   then executes the generated project's full default `examples.py` through the real installed
   console script, subprocess `timeout=180`. Its own docstring already records: "bimodal's full
   default generated examples.py is genuinely slow -- confirmed directly at ~100s ... it runs
   every example in the theory's default set." That ~100s figure predates the Skolemized
   Seriality/Interpolation axioms (this file's git history places it before task 153); with the
   axioms' ~10x per-solve cost increase measured elsewhere in this task, this parametrize case is
   now the single most expensive bimodal-coupled gating test found in this audit, and is now the
   parametrize case closest to blowing its own 180s subprocess timeout.

   **Empirically reproduced directly** (this audit, idle sandbox, current HEAD): confirmed the
   generated project's `examples.py` is genuinely the theory's full 53-entry `unit_tests` set
   (`countermodel_examples` + `theorem_examples` from `theory_lib/bimodal/examples.py`), not a
   small curated default — the generated file is 1482 lines with 58 `max_time` occurrences,
   essentially 1:1 with its 53 examples. Running it through `dev_cli.py` directly (bypassing only
   the `installed_venv` wrapper, to avoid a from-scratch venv build) was still producing normal,
   in-progress example output past **200 seconds** wall clock when terminated — i.e. it did not
   complete within the packaging test's own 180s subprocess timeout, on an idle machine, against
   this repository's current (post-axiom) `HEAD`. Individual example solves observed in the
   partial output were fast (0.04-0.08s each), consistent with a handful of harder formulas — not
   a uniform slowdown — absorbing most of the roughly 10x cost increase. This upgrades the
   paragraph above from "closest to blowing its budget" to "already blows its budget": absent a
   fix, `test_generate_then_execute[bimodal]` should now be expected to fail via
   `subprocess.TimeoutExpired` in `packaging.yml`, `release.yml` (both jobs), and
   `pypi-smoke.yml`, not merely run slower.
2. **`code/tests/packaging/test_cli_console_script.py::test_real_example_run_through_console_script`**
   and **`::test_console_script_runs_without_pythonpath`** (same `pytestmark`). Both write
   `_TINY_EXAMPLE_CONTENT` — `bimodal.get_theory()`, N=2, no explicit `max_time` (inherits
   bimodal's 1s default) — and run it through the installed console script. Both assert only
   generic console-script behavior (exit code, absence of `Traceback`, output containing
   `"EXAMPLE"`/expected content) — nothing bimodal-specific. This is the exact CLI-plumbing
   pattern `code/tests/cli/conftest.py` was already fixed for (see "Precedent" below); this file
   was missed because it lives in a different directory covered by a different CI workflow.

**Recommendation**: (a) bring `packaging.yml` into `test_unstable_deselection_wiring.py`'s
scanned-file list and give its invocation an `and not development` clause (`-m "packaging and not
development"`); (b) switch `test_cli_console_script.py`'s `_TINY_EXAMPLE_CONTENT` from bimodal to
logos — identical remedy to the `tests/cli/conftest.py` precedent, same non-bimodal-specific
assertions; (c) for `test_generate_then_execute[bimodal]`, see the "genuinely bimodal subject"
decision below — this is the clearest instance of that question in the whole audit, because
unlike the builder test named in the task description, this one's *entire point* is to prove each
specific registered theory's generated project actually runs, so substituting another theory
would not preserve its coverage.

## Finding 2 (second priority): `create_test_model()` — a shared test helper — hardcodes bimodal, silently ignoring its own `theory_name` parameter, and feeds ~20+ gating call sites across three files

`code/tests/utils/helpers.py::create_test_model()` accepts a `theory_name: str = 'bimodal'`
parameter whose docstring claims "defaults to 'logos'" but whose body never reads the parameter
at all — it unconditionally does `from model_checker.theory_lib import bimodal; theory =
bimodal.get_theory()`. Every caller in the repository calls it positionally with only `settings`
(confirmed by grep: no call site anywhere passes `theory_name`), so **every test that goes
through this helper is silently testing bimodal, unconditionally**, regardless of what the test's
own name or docstring implies. `tests/utils/base.py::BaseModelTest.create_model()` wraps the same
function and is likewise bimodal-only.

The function constructs a real `ModelDefaults` directly (not via `BuildExample`), and
`ModelDefaults.__init__` (`code/src/model_checker/models/structure.py:52`) eagerly calls
`self.solve(...)` — so every `create_test_model()`/`create_model()` call is a real Z3 solve, not
a lazy construction.

Callers, all in `code/tests/integration/` (a directory gated by both `tests.yml`'s and
`flake.nix`'s two invocations — no `packaging`/`performance`/`unstable`/`xdist_serial`/
`development` marker applies to any of these, so all run in the main parallel pass):

- `test_performance.py` (`TestExecutionPerformance`, `TestMemoryPerformance`,
  `TestConcurrentPerformance`, `TestCachingPerformance`, `TestBatchPerformance`,
  `TestWorstCasePerformance`) — subject is generic execution/memory/concurrency performance,
  nothing bimodal-specific. Its own docstring already documents the coupling for wall-clock
  budgets ("every `create_test_model` call here measured `min(real_solve_time, max_time) +
  overhead` and pinned at ~1.03s no matter what N was") and removed the resulting flaky budget
  assertions — but did not address the underlying theory choice.
- `test_error_handling.py` (`TestEdgeCases`, `TestErrorRecovery`, `TestFrameworkErrorHandling`) —
  subject is generic error handling (invalid N, malformed formulas, Unicode, graceful
  degradation), nothing bimodal-specific.
- `test_timeout_resources.py` (`TestTimeoutHandling`, `TestResourceLimits`,
  `TestPerformanceDegradation`, `TestResourceRecovery`, `TestInterruptHandling`) — subject is
  generic timeout/resource-limit behavior, nothing bimodal-specific. Carries the same kind of
  "budgets removed, not measuring the code's cost" docstring as `test_performance.py`.

**Measured current cost** (post-axiom, this repository's HEAD, `pytest
tests/integration/test_performance.py tests/integration/test_error_handling.py
tests/integration/test_timeout_resources.py -m "not development"`): **58 passed in 36.25s**
wall clock (single-worker; these three files run inside the `-n 4` parallel pass in the real
gating driver, so their contribution to total gating wall-clock is smaller than 36s but their
per-worker cost is real). Slowest individual calls: 6.16s (`test_complex_model_performance`),
5.60s (`test_special_characters_in_names`), 4.28s (`test_file_handles_closed`), 2.46s
(`test_partial_results_on_error`), plus ~15 more calls each in the 1.0-1.4s band — i.e. essentially
every one of these ~20 real-solve call sites is now individually costing roughly a full second or
more, purely from bimodal's frame-axiom overhead, with zero bimodal-specific assertions anywhere
in the three files.

**Recommendation**: fix `create_test_model()` to actually honor its `theory_name` parameter
(resolving via `model_checker.theory_lib` or `model_checker.api.get_theory` rather than
hardcoding `bimodal`), default it to `'logos'` (matching the existing, currently-false
docstring), and audit the ~20 call sites in these three files for whether any specific one
needs bimodal's particular semantics (initial read: none do — every assertion inspects generic
`ModelDefaults` attributes, error types, or timing/memory behavior). This single fix converts the
largest concentration of non-bimodal-specific bimodal-coupled gating cost found in this audit,
without touching bimodal's semantics.

## Finding 3: `code/src/model_checker/builder/tests/unit/test_example.py` — broader than the one test named in the task description

The task description names one failing test in this file
(`TestBuildExampleIntegration::test_build_example_bimodal_theory_countermodel`). Reading the
whole file shows the coupling is file-wide: **every class in it that performs a real solve uses
bimodal exclusively**, via one shared inline module-content string repeated with minor variants.
`BuildExample.__init__` (`builder/example.py:187-197`) eagerly calls
`self.model_structure.interpret(...)`, which is where the actual Z3 solve happens — so
construction alone (not just `get_result()`) is a real solve.

Measured current cost, this file alone (`pytest
src/model_checker/builder/tests/unit/test_example.py -m "not development"`): **17 passed in
33.96s**. Breakdown:

| Test | Wall time | Real solve? | Bimodal-specific subject? |
|---|---|---|---|
| `TestBuildExampleIntegration::test_iteration_via_iterate_api` | **31.78s** (explicit `max_time=30`) | Yes (2 solves: initial + iterate) | No — asserts the generic BuildExample/iterate-API contract ("asserts the contract, not the model count") |
| `TestBuildExampleIntegration::test_build_example_bimodal_theory_countermodel` | 5.72s (explicit `max_time=30`) | Yes | Borderline — asserts generic countermodel-found behavior, but is the one test in the file the task description already flags |
| `TestBuildExampleBasic::test_build_example_get_result` | 1.11s (no explicit `max_time`, inherits 1s) | Yes (via construction) | No — asserts result-dict shape/types only |
| `TestBuildExampleBasic::test_build_example_comparison_mode` | 0.54s | Yes | No — asserts comparison-mode wiring |
| `TestBuildExampleBasic::test_build_example_initialization` | 0.44s | Yes | No — asserts attribute wiring |
| `TestBuildExampleBasic::test_build_example_print_model` | 0.21s | Yes | No — asserts output non-empty |
| `TestBuildExampleBasic::test_build_example_with_no_model` | 0.09s | Yes (contradiction, fast UNSAT) | No — asserts `model_found is False` for `A ∧ ¬A` |
| `TestTimeoutSurfacing`, `TestThreeWayCheckResult`, `TestBuildExampleErrorHandling` (10 tests) | ~0.00s each | No — all use `BuildExample.__new__` + `Mock()`, never a real solve | N/A |

**The 31.78s figure is the single most important number in this finding.** It is a *currently
passing* test sitting almost exactly at its own explicit 30s budget — this is not a hypothetical
risk, it is a near-miss of exactly the class of failure that already put
`test_build_example_bimodal_theory_countermodel` into CI red on the 3.10 leg (widened once,
10s→30s, then failed anyway). `test_iteration_via_iterate_api`'s docstring already documents an
almost-identical prior near-miss ("this solve was observed taking 30.62s against this example's
own explicit max_time=30"). Both tests share the exact defect the task's HARD CONSTRAINT names:
widening the budget did not converge, and per TESTING_GUIDE.md 8.6, widening further is not the
fix.

**Recommendation, by sub-group**:
- `TestBuildExampleBasic` (5 tests, all non-bimodal-specific plumbing): switch to logos, same
  remedy as the `tests/cli/conftest.py` precedent. Eliminates ~2.4s and removes the file's
  incidental exposure to bimodal cost for tests that were never about bimodal.
- `test_iteration_via_iterate_api`: this is the file's clearest "genuinely bimodal subject vs.
  convenient fixture" case *in the negative direction* — its own docstring states it asserts the
  generic iterate-API contract, not bimodal semantics, and it is the one test in the file
  currently closest to a repeat CI failure. Switch to logos (logos's iterate path is exercised
  elsewhere in the theory's own test tree, so this is not a coverage loss for the *generic*
  contract this test targets).
- `test_build_example_bimodal_theory_countermodel`: this is the instance the task description
  asks to resolve deliberately — see the Decision section below.

## Finding 4: `code/tests/e2e/test_batch_output_real.py` and `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py::test_print_impossible_flag_includes_impossible_states` — same CLI-plumbing pattern as the fixed precedent, not covered by it

- `test_batch_output_real.py`'s two tests (`test_bimodal_batch_output_saves_one_model_entry_per_example`,
  `test_bimodal_batch_output_combines_markdown_with_separator`) run a two-example bimodal module
  (`N=2`, no explicit `max_time`) through `--save`/`--save markdown` and assert the batch-output
  *shape* (one `MODELS.json` entry per example, `---` separator in combined `EXAMPLES.md`) — this
  is functionally identical in kind to what `tests/cli/conftest.py`'s docstring already
  identifies as the class of test that should never have been pinned to bimodal ("gating
  CLI-plumbing assertions... nothing in them is bimodal-specific"). It was not touched by that
  fix because it lives in a different file with its own inline fixture content, not the shared
  `tiny_example_content`/`tiny_example_file` fixtures the fix targeted.
- `test_full_pipeline.py::test_print_impossible_flag_includes_impossible_states` runs two
  `dev_cli.py` subprocess invocations (baseline + `-i` flag) against a bimodal N=2 module with no
  explicit `max_time`, asserting only that `-i` changes output relative to baseline — generic
  flag-plumbing, not bimodal-specific.
- `test_full_pipeline.py::test_theory_library_execution` is a partial exception: it does assert
  `"World Histories"` appears in the output — bimodal's own distinct model-rendering label,
  genuinely bimodal-specific in that one assertion, even though the code path it exercises
  (`discover_theory_module`) is generic. Recommend leaving this one as bimodal (already carries
  an explicit `max_time=10`) rather than switching, since switching away from bimodal would
  remove the one assertion that actually needs it; if `discover_theory_module` coverage is wanted
  independent of bimodal, that would need a second, cheap-theory test rather than a substitution.

**Recommendation**: switch `test_batch_output_real.py`'s fixture content and
`test_print_impossible_flag_includes_impossible_states`'s fixture content to logos. Keep
`test_theory_library_execution` on bimodal with its existing `max_time=10`.

## Finding 5: `code/tests/cli/test_flag_matrix.py::_MAXIMIZE_EXAMPLE` — a second gap the `conftest.py` fix didn't reach

`test_flag_matrix.py` defines its own inline `_MAXIMIZE_EXAMPLE` (bimodal, two entries under the
same theory object, explicit `max_time=0.3`) for `test_maximize_dispatches_to_run_comparison`.
This is the same file whose `_CVC5_COMPATIBLE_EXAMPLE` was *already* switched to logos in a prior
pass (comment at line ~301: "Uses logos rather than bimodal: bimodal's frame constraints call
z3.MultiPattern... which cvc5.pythonic does not implement"), and whose main tiny-example fixture
comes from the already-fixed `conftest.py`. `_MAXIMIZE_EXAMPLE` is a separate, still-bimodal
string that fell outside both of those fixes. The test's own docstring states its assertion scope
plainly: "Asserts dispatch to `module.comparison.run_comparison()`... not comparison depth or
specific max-N results" — non-bimodal-specific by the test author's own description.

**Recommendation**: switch `_MAXIMIZE_EXAMPLE` to logos, same remedy, same file family as the
already-applied fixes — this closes out that file's remaining bimodal exposure entirely.

## Items checked and ruled out (construct-only, mocked, or already exempted)

- **`code/src/model_checker/builder/tests/integration/test_build_module_theories.py`**,
  **`test_component_integration.py`**: construct `BuildModule` only (never `BuildExample`) —
  `BuildModule.__init__` parses/loads but does not eagerly solve any example, confirmed by
  reading `builder/module.py`'s loading path and by these tests' own assertions (attribute
  presence only, no `get_result()`/`run_examples()` call). Negligible Z3 cost; not urgent, though
  the same "not bimodal-specific" argument for cleanliness applies if these files are touched for
  other reasons.
- **`test_serialize.py::test_serialize_real_bimodal_theory_preserves_structure`**: calls
  `bimodal.get_theory()` and serializes the theory *dict* (class references, module paths) —
  never constructs a `BuildExample`/`ModelDefaults`, no Z3 solve.
- **`test_comparison.py`**, **`test_package_marker.py`**, **`test_project_version.py`**,
  **`test_package_imports.py`**, **`test_generated_projects.py`**,
  **`test_project_edge_cases.py`**: use `BuildProject('bimodal')`, which writes template files
  (`.generate()`/`._create_package_marker()`) — no example is run, no Z3 solve.
- **`test_loader.py`**: calls `bimodal.get_theory()` (and three other theories') purely to inspect
  dict shape/module attribution; no solve.
- **`code/tests/conftest.py::test_module_content`** fixture and
  **`code/tests/utils/helpers.py::capture_model_output`/`run_example`**: define bimodal-based
  content/defaults but have **zero callers** anywhere in the test tree (`grep -rl` confirms no
  consumer) — dead code, no wall-clock cost. Worth deleting or fixing for hygiene but out of this
  audit's cost scope.
- **`theory_lib/tests/test_meta_data.py`**, **`test_theory_conformance.py`**,
  **`theory_lib/tests/unit/test_error_handling.py`**: string-literal/registry/signature checks
  (`module.get_theory()` inspected for shape, never executed against a formula) — no solve.
- **`utils/tests/unit/test_parsing.py::test_bimodal_formulas`**: pure tokenizer/parser test
  (`parse_expression`), operates on formula syntax only, no semantics layer touched at all.
- **`jupyter/tests/unit/test_adapters.py::TestBimodalTheoryAdapter`**,
  **`output/tests/unit/test_markdown_formatter.py`**: mocked models / string theory names only.
- **`test_registry.py::test_real_theories_are_registered_via_bootstrap`**,
  **`test_layering.py`**: string/registry-membership checks, no solve.
- **`code/tests/ci/*`** (`test_development_marker_application.py`,
  `test_example_budget_floor.py`, `test_oracle_development_marker_application.py`,
  `test_run_tests_markers.py`, `test_unstable_watch_classifier.py`,
  `test_worker_rss_sampler.py`, `test_unstable_deselection_wiring.py` itself): these are the
  meta-tests that audit the CI wiring/markers — none constructs or solves a bimodal example.
- **`test_flag_matrix.py`**'s `--load_theory bimodal` / `-l bimodal` / `test_docs_flag_matrix.py`'s
  `-load bimodal` cases: pass `'bimodal'` as a CLI *argument string* to `BuildProject.generate()`
  via `ask_generate()` (interactive project scaffolding) — file-copy only, no example is run, no
  Z3 solve. Bimodal here is being tested as a *load_theory target*, not as an example fixture; not
  in scope for a fixture swap (swapping it would just move the same non-cost issue elsewhere for
  no benefit, since the assertion is about the load_theory flag path itself, one instance of
  which should exercise a real registered theory name).

## Decision: does a test whose SUBJECT is genuinely bimodal belong in a gating selection while bimodal is in development?

The task asks this to be resolved deliberately for the builder test named in the description.
Having read the whole file (Finding 3) and found two more candidates raising the identical
question (Finding 1's `test_generate_then_execute[bimodal]`, and Finding 4's
`test_theory_library_execution`), the pattern across all three is the same and the same
resolution applies to all:

**None of the three actually has a bimodal-specific subject once "subject" is read as "the
behavior under test," as opposed to "the theory instance used to exercise it":**

- `test_build_example_bimodal_theory_countermodel` asserts `BuildExample` finds *a* countermodel
  for `A ⊬ B` — a claim true of essentially any non-degenerate theory, not a claim about
  bimodal's frame semantics. The task description's own framing agrees: "it asserts BuildExample
  integration, which is not bimodal-specific plumbing."
- `test_theory_library_execution` is the one genuine exception in this audit: its assertion
  (`"World Histories"` in output) is bimodal's own model-rendering label, not reproducible under
  any other theory. This one is correctly kept gating on bimodal.
- `test_generate_then_execute[bimodal]` is the interesting middle case: the *test function* is
  generic (packaging journey correctness), but the *parametrization* exists specifically to prove
  each theory's own packaging journey works — you cannot substitute logos for the bimodal
  parametrize case without silently dropping bimodal packaging coverage entirely.

Given TESTING_GUIDE.md 8.14's own stated boundary — `development` "must never be used for
differential or soundness-oracle tests, or for any test whose pass/fail state encodes a semantic
claim about the theory's correctness rather than its completeness" — none of these three is a
soundness claim. `test_generate_then_execute[bimodal]` and
`test_build_example_bimodal_theory_countermodel` are both, in substance, *completeness* claims
("bimodal's example set runs to completion," "bimodal finds a countermodel within budget") of
exactly the kind the `development` marker exists to quarantine — they are just not currently
reachable by either of the two existing `development` blankets, because neither
`code/tests/packaging/` nor `code/src/model_checker/builder/tests/` is inside
`theory_lib/bimodal/tests/` or `oracle/`.

**Recommendation**: apply `@pytest.mark.development` at per-test/per-parametrize granularity
(TESTING_GUIDE 8.14's default granularity — not a new blanket) to:
1. `test_generate_then_execute`'s bimodal parametrize case specifically (via
   `pytest.param(theory_name, marks=[pytest.mark.development] if theory_name == "bimodal" else
   [])`, mirroring the `UNSTABLE_EXAMPLES` set-membership pattern TESTING_GUIDE 8.14 names as the
   established idiom), and give `packaging.yml`'s invocation the accompanying `and not
   development` clause;
2. `test_build_example_bimodal_theory_countermodel` in `test_example.py`, moving it out of the
   "switch to logos" bucket it would otherwise fall into as a plumbing test, and instead marking
   it `development` in place — it stays runnable and visible (`-m development`), stops gating
   while bimodal's frame-axiom cost is unsettled, and its existing timeout-vs-unsat discriminator
   is preserved rather than discarded.

This keeps `test_theory_library_execution` as the one deliberately-bimodal, deliberately-gating
test in this whole audit, on the strength of its output-label assertion actually requiring
bimodal.

## Wall-clock evidence gathered (current HEAD, post-axiom; single-worker, not `-n 4`)

| Selection | Result |
|---|---|
| `builder/tests/integration/test_performance.py -m "not development"` | 6 passed in 3.60s (test session); slowest 1.57s / 1.10s |
| `builder/tests/unit/test_example.py -m "not development"` | 17 passed in 33.96s; slowest 31.78s (`test_iteration_via_iterate_api`, budget=30s) and 5.72s |
| `tests/integration/test_performance.py + test_error_handling.py + test_timeout_resources.py -m "not development"` | 58 passed in 36.25s; ~20 individual calls each ≥1s, all through the hardcoded-bimodal `create_test_model()` helper |

These are current, not historical-vs-current comparisons (the task's own "DO NOT RE-DERIVE"
instruction covers the one figure already measured — the tests/cli tiny-example 0.42s→4.2s
figure — and this audit did not attempt to independently reproduce a pre-axiom baseline for the
files above, since that would require reverting task 153's commits). What this audit *did*
measure is the current cost each of these files/tests carries, which is what informs the
disposition recommendations above. A rigorous before/after wall-clock table for the actual
release-gating selections (`tests.yml`'s two invocations, `flake.nix`'s two, and the newly-scoped
`packaging.yml` invocation) belongs to the implementation phase, taken immediately before and
after the fixture swaps and markings recommended here — this research pass intentionally stopped
short of running the full multi-minute gating selections twice to stay within a research-task
budget, and because "before" (this repository's current HEAD) is already captured by normal git
history for the implementation phase to diff against.

## Summary of recommended dispositions

| Test / file | Disposition |
|---|---|
| `code/tests/packaging/test_cli_console_script.py` (`_TINY_EXAMPLE_CONTENT`, 2 tests) | Switch to logos |
| `code/tests/packaging/test_generate_then_execute.py::test_generate_then_execute[bimodal]` | Mark `development` (per-parametrize); add `and not development` to `packaging.yml` |
| `code/tests/utils/helpers.py::create_test_model()` (+ `base.py::create_model()`) | Fix to honor `theory_name`; default to logos; ~20 call sites across `test_performance.py`/`test_error_handling.py`/`test_timeout_resources.py` inherit the fix automatically |
| `builder/tests/unit/test_example.py::TestBuildExampleBasic` (5 tests) | Switch to logos |
| `builder/tests/unit/test_example.py::test_iteration_via_iterate_api` | Switch to logos |
| `builder/tests/unit/test_example.py::test_build_example_bimodal_theory_countermodel` | Mark `development` (per-test) |
| `code/tests/e2e/test_batch_output_real.py` (2 tests) | Switch to logos |
| `builder/tests/e2e/test_full_pipeline.py::test_print_impossible_flag_includes_impossible_states` | Switch to logos |
| `builder/tests/e2e/test_full_pipeline.py::test_theory_library_execution` | Keep bimodal, keep existing `max_time=10` (genuinely bimodal-specific assertion) |
| `code/tests/cli/test_flag_matrix.py::_MAXIMIZE_EXAMPLE` | Switch to logos |
| Everything under "Items checked and ruled out" | No action (negligible/zero Z3 cost, or already exempted) |
| `test_unstable_deselection_wiring.py::_SCANNED_FILES` | Add `packaging.yml`, `release.yml` (both packaging-suite steps), and `pypi-smoke.yml`, giving each its `and not development` clause and bumping `EXPECTED_GATING_MARKER_INVOCATIONS` accordingly |

## Constraints honored

No solve budgets were proposed as a remedy anywhere above (every "keep" recommendation retains
an existing budget rather than widening one; every cost-driven recommendation is a fixture swap
or a `development` marking, not a bigger number). No assertion is weakened or deleted in any
recommendation — logos substitutions preserve the exact same assertions against a cheap theory,
and `development` marking preserves the assertion's visibility under `-m development` rather than
deleting or skipping it outright. Bimodal's semantics and frame-class constraints are untouched
throughout this research; nothing here proposes changing what the axioms assert, only which
gating tests pay for evaluating them.
