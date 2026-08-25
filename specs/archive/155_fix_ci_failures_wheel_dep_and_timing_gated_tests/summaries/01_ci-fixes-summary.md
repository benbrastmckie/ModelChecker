# Implementation Summary: Fix CI failures (wheel dep and timing-gated tests)

- **Task**: 155 - fix_ci_failures_wheel_dep_and_timing_gated_tests
- **Plan**: `specs/155_fix_ci_failures_wheel_dep_and_timing_gated_tests/plans/01_ci-fixes-wheel-and-timing.md` (revision r1)
- **Phases completed**: 6 of 6

## What changed, per class

### Class 1 -- missing `wheel` build dependency (release-blocking)

- `.github/workflows/packaging.yml:27`: `pip install pytest build` -> `pip install pytest build wheel`
- `.github/workflows/release.yml:99` (the `build` job): `pip install build twine` -> `pip install build twine wheel`
- `.github/workflows/release.yml:51` (the `test-and-release` job) confirmed unchanged --
  it already reads `pip install build wheel setuptools`.

### Class 2(a) -- wall-clock speed assertions (marked + deselected)

- `@pytest.mark.performance` added to:
  - `code/src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetLoaderBehavior::test_performance_improvement`
  - `code/tests/integration/test_performance.py::TestExecutionPerformance::test_complex_model_performance`
    (stacked alongside its existing `@pytest.mark.timeout(30)`, which was left in place)
- `.github/workflows/tests.yml:66` and `flake.nix:147` both extended, as a single atomic-batch
  edit, from `-m "not packaging"` to `-m "not packaging and not performance"` -- the two CI
  gates do not diverge.

### Class 2(b) -- correctness tests that ran out of time (budgets raised, nothing deselected)

- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py`
  (`_build_example`'s shared `example_case` settings, used by
  `test_iterate_two_produces_distinct_models`): `'max_time': 30` -> `'max_time': 60`.
  Local run of this exact test took 61.25s wall-clock -- confirming the raise was necessary,
  not merely cosmetic, on this machine.
- `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py`:
  - `test_theory_library_execution`'s generated temp module: `{"N": 2}` ->
    `{"N": 2, "max_time": 10}` in the `example_range` settings dict (not
    `general_settings`, which stays `{}`).
  - `run_dev_cli`'s outer `subprocess.run(..., timeout=15)` -> `timeout=30`.
- Neither test gained `@pytest.mark.performance` -- both remain unmarked, always-run
  correctness tests.

### Class 3 -- pre-existing differential-tests budget

- `.github/workflows/differential-tests.yml`'s broad/first pytest step (line 38, the one that
  is NOT `TestGatingConclusiveScan`-excluding): `--timeout=300` -> `--timeout=900`, with a
  comment recording that `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`
  is `xdist_serial` (already runs alone -- a genuine budget-too-tight issue, not worker
  contention), does real re-solving work, and is deliberately left unmarked (no
  `@pytest.mark.slow`) so it keeps running every gating pass.
- The explicit six-class step (line ~52, now ~57) is confirmed unchanged at `--timeout=300`;
  its class list (`TestCIGate`, `TestFormulaEnumerator`, `TestDifferentialInfrastructure`,
  `TestKnownFormulaBaseline`, `TestDifferentialComparison`, `TestDifferentialReport`) does not
  include `TestGatingConclusiveScan`.

## Change-set verification

`git diff --name-only` against the pre-task base commit shows exactly the nine files the plan's
Phase 6 Scope Hypothesis named, with no production/library code:

```
.github/workflows/differential-tests.yml
.github/workflows/packaging.yml
.github/workflows/release.yml
.github/workflows/tests.yml
code/src/model_checker/builder/tests/e2e/test_full_pipeline.py
code/src/model_checker/builder/tests/test_refactoring_target_behavior.py
code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py
code/tests/integration/test_performance.py
flake.nix
```

The four `theory_lib/*/VERSION` files are confirmed unmodified (empty diff for that path glob).

## Local verification results

**IMPORTANT: local green is necessary but not sufficient evidence here.** This task exists
because the first live 2026-08-12 workflow runs failed despite the underlying code being
correct -- local passing runs on this machine did not predict CI failure. Nothing below is a
claim that CI will now pass; it is a record of what was directly observed on this machine, nothing more.
**No CI run has been triggered or observed as part of this implementation, no branch was
pushed, no PR was opened, and no tag was created**, per `.claude/rules/pr-prohibition.md` and
this task's explicit constraints.

### Full CI selector, exactly as the gate will run it

```
cd code && PYTHONPATH=src python -m pytest tests/ src/model_checker -m "not packaging and not performance" -n 6 -q
```

Result: **2254 passed, 3 warnings, 0 failures, in 246.34s.**

**Delta note (reported honestly, not smoothed over):** the pre-change local baseline for the
same selector minus only `not performance` (i.e. `-m "not packaging"`, measured during Phase 3
verification via `--collect-only`) was **2256** collected items; the post-change selector
collects **2254** -- an exact **-2** delta, attributable to precisely the two newly-marked
tests and nothing else (confirmed via `--collect-only` diff in Phase 3, and now confirmed again
by this Phase 6 full run, which passed all 2254). This local delta is the load-bearing
invariant Phase 3's atomic-batch edit was designed to preserve, and it holds exactly.

This local absolute count (2254) does **not** match the task description's cited CI-observed
range (2000-2002 passed per job on 2026-08-12). That gap is expected and not a regression: this
local run and the CI `general-tests` job are different environments (different Python version,
different worker/skip conditions, no CI-only conditional skips triggered locally), so their
absolute passed counts are not directly comparable -- only the **delta** within one environment
before/after this task's edits is a meaningful invariant, and that delta is exactly -2 in both
places it was checked (Phase 3's `--collect-only` diff and this Phase 6 full run).

### The two deselected tests, run explicitly on this quiet host

```
cd code && PYTHONPATH=src python -m pytest -m performance src/model_checker tests -v
```

Result: **2 passed** (`test_performance_improvement`, `test_complex_model_performance`), 8.56s
total, confirming the marker attaches to real, currently-passing tests rather than papering
over a genuine failure.

### The two raised-budget correctness tests

```
cd code && PYTHONPATH=src python -m pytest src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py -v
```
7 passed in 121.96s, including `test_iterate_two_produces_distinct_models` (61.25s).

```
cd code && PYTHONPATH=src python -m pytest src/model_checker/builder/tests/e2e/test_full_pipeline.py -v
```
3 passed in 2.57s, including `test_theory_library_execution` (0.73s) -- its captured stdout
contained `World Histories` and not `TIMEOUT: Model search exceeded`, satisfying both assertions
inside the test.

### Local wheel build and lint (Class 1 direct observation)

Run from the **ambient shell** (`/home/benjamin/.nix-profile/bin/python`), never inside
`nix develop` -- the flake devShell's `devShells.default.packages = [ devPython ]` has no
`build`, `twine`, or `check-wheel-contents`.

```
cd code && rm -rf dist && python -m build --no-isolation
```
Exit **0**. Produced `dist/model_checker-1.3.0-py3-none-any.whl` and
`dist/model_checker-1.3.0.tar.gz`. `--no-isolation` deliberately skips provisioning
`build-system.requires` (`["setuptools>=42", "wheel"]`), so a zero exit here is a direct local
reproduction that the Class 1 fix (adding `wheel` to the ambient install lists) is the correct
remedy for the CI failure mode `ERROR Missing dependencies: wheel`.

```
check-wheel-contents dist/*.whl
```
```
dist/model_checker-1.3.0-py3-none-any.whl: W002: Wheel contains duplicate files:
  model_checker/theory_lib/bimodal/VERSION
  model_checker/theory_lib/exclusion/VERSION
  model_checker/theory_lib/imposition/VERSION
  model_checker/theory_lib/logos/VERSION
```
Exit **1**. **Expected and out of scope** per the plan's Non-blocking contract, and re-verified
at implementation time. This finding is a **pre-existing** wheel-content characteristic
(four per-theory `VERSION` files legitimately all containing `1.0.0`), unrelated to the
`wheel` install-list fix this task makes. The four `VERSION` files were not touched. A
separate task now exists to decide whether/how to address the W002 duplicate-files finding;
that decision is out of scope here.

```
check-wheel-contents --ignore W002 dist/*.whl
```
```
dist/model_checker-1.3.0-py3-none-any.whl: OK
```
Exit **0**. No wheel-content finding beyond the one known at revision time -- the "is there
anything NEW?" signal is clean.

`git status --porcelain` shows no `code/dist` entry after the build (gitignored via
`.gitignore:13`, `**/dist`); nothing under `code/dist/` was staged or committed.

## Workflow runs the user must observe after pushing

Since no CI run has been triggered from this implementation, the following are named as the
runs to check, not claimed as passing:

- **`.github/workflows/packaging.yml`** -- exercises Class 1 (the packaging contract suite's
  `python -m build` step, now with `wheel` in its install list).
- **`.github/workflows/tests.yml`** -- BOTH the `general-tests` matrix job (Class
  1-interaction/Class 2a: the extended `-m "not packaging and not performance"` selector) and
  the `flake-check` job (Class 2a via the identically-extended `flake.nix` selector).
- **`.github/workflows/differential-tests.yml`** -- Class 3 (the raised `--timeout=900` on the
  broad step).
- **`.github/workflows/release.yml`** cannot be observed without a tag push, which is
  **user-only**. Its `build`-job fix (`pip install build twine wheel`) is evidenced here only
  by static inspection: it has the identical `pip install ... build` + `python -m build` shape
  as `packaging.yml`, and a green `packaging.yml` run exercises the same underlying failure
  mode (`wheel` missing from an ambient `pip install` line feeding `python -m build`).

## Plan Deviations

- None (implementation followed plan). All nine edit sites match the plan exactly; the
  `check-wheel-contents` non-blocking contract added in revision r1 was followed as specified,
  including the exit-1-is-expected framing and the explicit refusal to touch the `VERSION`
  files.

## Explicit non-claims

- **CI-green is NOT claimed.** No workflow run was triggered or observed from this
  implementation.
- No branch was pushed, no PR was opened (`/merge` was not invoked), and no tag was created.
- The W002 wheel-content finding was reported, not fixed, per the plan's Non-blocking contract.
