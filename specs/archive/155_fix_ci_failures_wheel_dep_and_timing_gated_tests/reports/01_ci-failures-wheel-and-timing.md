# Research: CI failures from first live workflow run (2026-08-12)

Runs investigated (by class, not by re-fetching logs -- the task description already carries the
observed failure signatures; this report verifies each claim against the current tree and pins
exact edit sites): 31609253772, 31609253774, 31609253618.

## Class 1 -- missing `wheel` (release-blocking, fix first)

Verified by reading both workflow files directly.

- `.github/workflows/packaging.yml:27` -- `run: pip install pytest build`. No `wheel`.
- `.github/workflows/packaging.yml:30` runs `python -m pytest tests/packaging/ -v -m packaging`,
  which invokes `python -m build --no-isolation` inside the packaging contract suite (see
  `code/tests/packaging/`). `--no-isolation` means the ambient env's packages are what `build`
  sees -- `wheel` must already be importable there. It is not, hence
  `ERROR Missing dependencies: wheel`.
- `.github/workflows/release.yml`: TWO separate `pip install` sites in TWO different jobs.
  - `test-and-release` job, line 51: `pip install build wheel setuptools` -- **already has
    `wheel`**. Not part of the bug.
  - `build` job, line 99: `pip install build twine` -- **missing `wheel`**. This job also calls
    `python -m build` (line ~101) and would fail identically to packaging.yml once a tag is
    pushed. `publish-testpypi` and `publish-pypi` both declare `needs: [... build ...]`
    (`needs: [test-and-release, build]` and `needs: [build, publish-testpypi]` respectively), so
    a `build`-job failure blocks the entire publish chain.

**Fix**: add `wheel` to exactly two install lines:
- `.github/workflows/packaging.yml:27` -> `pip install pytest build wheel`
- `.github/workflows/release.yml:99` -> `pip install build twine wheel`

Do not touch `release.yml:51` (`test-and-release` job) -- it already installs `wheel` and is not
implicated. This fix is deterministic dependency-resolution behavior, not flaky; the task's
verification instruction (re-run the workflows, don't reason about them) applies as-is.

## Class 2 -- wall-clock assertions under CI contention

### (a) Tests asserting SPEED -> mark `@pytest.mark.performance`, deselect in CI

The `performance` marker is already registered at `code/pyproject.toml:90`:
```
"performance: Tests that verify performance characteristics",
```
It is currently unused by any test in the tree (grep for `@pytest.mark.performance` returns
nothing) -- registered but never applied.

Two tests to mark:

1. `code/src/model_checker/builder/tests/test_refactoring_target_behavior.py:311-327`
   (`TestTargetLoaderBehavior.test_performance_improvement`, a `unittest.TestCase` method --
   pytest marks apply fine to TestCase methods). Currently undecorated. Asserts
   `init_time < 0.01` for 100 `ModuleLoader(...)` constructions; CI measured `0.011432s`.
   Add `@pytest.mark.performance` immediately above `def test_performance_improvement(self):`.
   `import pytest` is already present at the top of the file (line 18).

2. `code/tests/integration/test_performance.py:53-80`
   (`TestExecutionPerformance.test_complex_model_performance`), already decorated with
   `@pytest.mark.timeout(30)` at line 53. Stack `@pytest.mark.performance` alongside it (either
   order is fine; pytest applies both).
   - The test's own docstring (lines 55-61) explicitly frames its 20s/30s budgets as "hang
     guards, not performance budgets" with "3.3x headroom" that CI contention evidently ate
     (observed: `Failed: Timeout (>30.0s) from pytest-timeout`). The task text asks whether this
     belongs in (a) or (b) -- it is a **speed assertion dressed as a hang guard**: the assertion
     bodies are `elapsed < 20.0` / `elapsed < 30.0`, which is exactly the class-1(a) shape
     (a `< N seconds` wall-clock claim), not a `pytest-timeout` mechanism raise like the class-2(b)
     cases below. Recommend routing it to (a) with the other speed test rather than (b): raising
     its `@pytest.mark.timeout(30)` further would only re-hide the same problem the file's own
     top-of-file comment (lines 15-24) already diagnoses for its sibling tests in this class --
     these budgets don't measure the code's cost under a shared 2-core runner, full stop.

Selector to add in CI (both places, so the two gates agree):
- `.github/workflows/tests.yml:66` -- currently
  `pytest tests/ src/model_checker -m "not packaging" -n 6 -q` -> change to
  `pytest tests/ src/model_checker -m "not packaging and not performance" -n 6 -q`
- `flake.nix:147` (inside `checks.default`'s `checkPhase`) -- currently
  `pytest src/model_checker tests -m "not packaging" -n 6 -q` -> change to
  `pytest src/model_checker tests -m "not packaging and not performance" -n 6 -q`

Do NOT touch `.github/workflows/packaging.yml` (uses `-m packaging` positively, unrelated
selector) or `.github/workflows/differential-tests.yml` (uses `-m "not slow and not
differential"`, a disjoint marker set).

### (b) Tests that ran out of time doing real work -> raise the timeout budget, don't deselect

Both failures here are driven by an **application-level `max_time` / subprocess timeout**, not a
`@pytest.mark.timeout` marker -- important because "raise the pytest-timeout budget" from the
task description maps to a different literal knob in each case:

1. `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py`
   (`TestBimodalIteratorReal.test_iterate_two_produces_distinct_models`, method at line 245;
   shared fixture `_build_example` at lines 220-235). The example settings dict at line 234 sets
   `'max_time': 30` with a comment already documenting "observed solve times for this example are
   2-4s in isolation and vary further under full-suite load." The test asserts
   `example.model_structure.z3_model_status` is truthy (line 264-265, "First model was not
   satisfiable; cannot exercise iteration"). Under CI contention, Z3 hits the 30s `max_time` cap
   before finding a model, so `z3_model_status` comes back false/unsat and the assertion fails --
   this is the reported "Z3 returned unsat first model under load," not a `pytest-timeout`
   exception. There is no `@pytest.mark.timeout` anywhere in this file (verified by grep). Fix:
   raise the `max_time` value at line 234 (e.g. `30 -> 60`) to give the solver more headroom on a
   contended runner; the existing comment already anticipates this exact failure mode, so the fix
   is a one-line budget increase plus an updated comment, not a new mechanism.

2. `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py`
   (`TestFullPipeline.test_theory_library_execution`, method at line 52). This test shells out via
   `run_dev_cli` (defined lines 29-50), which wraps `subprocess.run(..., timeout=15)` (line 44,
   comment: "Prevent hanging - reduced timeout for faster tests"). The generated example module
   (lines 61-70) sets `general_settings = {}` -- no explicit `max_time`, so the bimodal theory's
   own default applies (documented elsewhere in the tree, `code/tests/integration/
  test_performance.py`'s header comment, as 1 second). Under CI contention that 1s budget is
   exceeded before Z3 finishes, and bimodal's own model code prints `"TIMEOUT: Model search
   exceeded maximum time of {max_time} seconds"` to stdout instead of rendering the model
   (confirmed source: `code/src/model_checker/theory_lib/bimodal/semantic/model.py:594`, the
   same message family exists in `exclusion/semantic/model.py:315` and
   `logos/semantic/model.py:168`). The test then fails
   `assertIn("World Histories", result.stdout)` against that timeout string -- matching the
   observed `AssertionError: 'World Histories' not found in 'TIMEOUT: Model search exc...'`.
   Fix has two parts, both budget increases:
   - Add an explicit, generous `max_time` (e.g. `10`) to the generated example's settings dict
     (currently `example_range`/`general_settings` at lines 63-69 of the temp-file text) so the
     bimodal solve itself gets real headroom under contention.
   - Raise `run_dev_cli`'s outer `subprocess.run(..., timeout=15)` at line 44 to comfortably
     exceed the new inner `max_time` plus process-startup/import overhead (e.g. `timeout=30`),
     so the outer guard doesn't become the new bottleneck once the inner budget grows.

These are correctness tests (they exercise real solve/execution paths), so per the task's
explicit instruction they must NOT be deselected -- only their timeout budgets raised. Nothing
in `tests.yml` or `flake.nix` needs a selector change for these two; they carry no `performance`
marker and should not receive one.

## Class 3 -- pre-existing differential-tests.yml timeout (lowest priority, not release-blocking)

`.github/workflows/differential-tests.yml` runs
`oracle/bimodal_logic/tests/test_cross_oracle_differential.py` twice: once broadly with
`-m "not slow and not differential"` and `--timeout=300` (lines 34-39), once against an explicit
list of six classes with the same `--timeout=300` (lines 41-52). The failing test,
`TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`
(`oracle/bimodal_logic/tests/test_cross_oracle_differential.py:2324`), is decorated with neither
`@pytest.mark.slow` nor `@pytest.mark.differential` (confirmed: only `TestBimodalHarnessIntegration`
at line 1204 carries `@pytest.mark.differential`, and `TestFullScanReport` at line 2451 carries
`@pytest.mark.slow`). It therefore runs inside the FIRST (broad) step, not the explicitly-listed
second step, and is what timed out (1 failed / 62 passed in 620s against a 300s budget). The
class's own docstring (lines 2299-2318) explains it is deliberately NOT marked `slow` -- it's
meant to run every gating pass as a soundness check over the known-conclusive subset -- and IS
marked `xdist_serial` so its floor (`MIN_CONCLUSIVE_GATING_FORMULAS`) is deterministic rather than
contention-dependent. That serial-only property is itself evidence this failure is a genuine
budget-too-tight issue rather than resource contention from parallel workers (the diagnostic class
2 relies on): `xdist_serial` means it already runs alone.

Task guidance offers two options; given (1) this suite already runs pytest-timeout serially with
no sibling worker contention, (2) the class explicitly re-solves real formulas (correctness value,
same as class-2(b) above), and (3) the task's general preference for "generous budgets over tight
ones," the report recommends **raising `--timeout=300` in the first step** (line 38) to a
noticeably larger value (e.g. `900`) rather than marking the class `@pytest.mark.slow` (which
would silently drop it from every regular gating run, mirroring the class-2(b) "don't deselect
real correctness coverage" reasoning). The alternative (mark `@pytest.mark.slow`, matching
`TestFullScanReport`/`TestBimodalHarnessIntegration`'s existing manual-only precedent) is legitimate
and lower-effort if the implementer judges 900s still insufficient or judges this scan's cost
fundamentally CI-inappropriate; either is acceptable per the task description ("Either raise its
300s budget or make that scan manual-only"). This class is explicitly NOT a regression from the
CI-gate work and NOT release-blocking; the task instructs not to let it block the release.
If raising the timeout: only line 38 (`--timeout=300` in the first/broad pytest invocation) needs
to change -- line 52 (the explicit six-class step) does not include `TestGatingConclusiveScan` and
is unaffected either way.

## Cross-cutting notes for implementation

- All edits are confined to: `.github/workflows/packaging.yml`, `.github/workflows/release.yml`,
  `.github/workflows/tests.yml`, `flake.nix`, `.github/workflows/differential-tests.yml`, plus the
  three test files (`test_refactoring_target_behavior.py`, `code/tests/integration/
  test_performance.py`, `bimodal/tests/integration/test_iterate.py`,
  `builder/tests/e2e/test_full_pipeline.py`).
- No production/library code changes are implicated anywhere in this task -- confirms the task
  description's framing that none of this is a semantic defect.
- `tests.yml`'s existing `-m "not packaging"` selector and `flake.nix`'s identical selector must
  both gain `and not performance` together, or the two gates (PyPI z3-solver toolchain vs.
  nixpkgs-native toolchain) will diverge on which tests they treat as CI-appropriate -- exactly
  the class of gap the task's "CONTEXT WORTH KNOWING" section describes for the earlier
  `flake.nix` broadening.
- Per `.claude/rules/pr-prohibition.md`, implementation must stop at "changes ready, here are the
  exact workflow runs to check" -- no push, no PR, no tag. The workflows that will need
  re-observation once these fixes land on a pushed branch: `.github/workflows/packaging.yml`
  (Class 1), `.github/workflows/tests.yml` (Classes 1 selector interaction + 2a), the `flake
  flake-check` job inside `.github/workflows/tests.yml` (Class 2a), and
  `.github/workflows/differential-tests.yml` (Class 3, if touched). `.github/workflows/release.yml`
  cannot be observed without a tag push, which is explicitly out of scope for this agent
  (user-only, per `skill-tag`/`pr-prohibition.md`) -- its `build`-job fix is verified by static
  inspection (identical `pip install ... build` + `python -m build` shape to `packaging.yml`) and
  by the fact that `packaging.yml`'s CI run, once fixed, exercises the same failure mode.

## Exact edit sites (summary table)

| File | Line(s) | Current | Change |
|------|---------|---------|--------|
| `.github/workflows/packaging.yml` | 27 | `pip install pytest build` | `pip install pytest build wheel` |
| `.github/workflows/release.yml` | 99 | `pip install build twine` | `pip install build twine wheel` |
| `.github/workflows/tests.yml` | 66 | `-m "not packaging"` | `-m "not packaging and not performance"` |
| `flake.nix` | 147 | `-m "not packaging"` | `-m "not packaging and not performance"` |
| `code/src/model_checker/builder/tests/test_refactoring_target_behavior.py` | 311 | undecorated | add `@pytest.mark.performance` |
| `code/tests/integration/test_performance.py` | 53 | `@pytest.mark.timeout(30)` only | add `@pytest.mark.performance` |
| `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` | 234 | `'max_time': 30` | raise, e.g. `'max_time': 60` |
| `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` | 44 | `timeout=15` | raise, e.g. `timeout=30` |
| `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` | 61-70 (generated module text) | no `max_time` key | add explicit generous `max_time`, e.g. `10` |
| `.github/workflows/differential-tests.yml` | 38 | `--timeout=300` (first step) | raise, e.g. `--timeout=900`, OR mark `TestGatingConclusiveScan` `@pytest.mark.slow` instead |

## Verification plan for the implementer

Local runs are necessary but not sufficient (this task exists precisely because local green did
not predict CI green). After implementing:
1. Run the affected test files locally to confirm no syntax/marker errors and that the two
   speed tests are correctly deselected by the new selector.
2. Report the fix as ready without asserting CI-green, and name these workflow runs for the user
   to check after they push: `.github/workflows/packaging.yml`, `.github/workflows/tests.yml`
   (both the `general-tests` matrix and the `flake-check` job), and
   `.github/workflows/differential-tests.yml` if Class 3 was touched. `.github/workflows/
  release.yml` can only be observed by tagging, which is a user-only action.
