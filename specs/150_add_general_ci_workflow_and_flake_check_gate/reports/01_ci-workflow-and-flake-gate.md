# Research Report: Task #150

**Task**: 150 - add_general_ci_workflow_and_flake_check_gate
**Started**: 2026-08-12
**Completed**: 2026-08-12
**Effort**: ~2-3 hours implementation (workflow authoring + flake.nix edit + ROADMAP update)
**Dependencies**: task 148 (CLI end-to-end suite), task 149 (packaging contract tests) — both COMPLETED
**Sources/Inputs**: Codebase (`.github/workflows/`, `flake.nix`, `code/pyproject.toml`, `oracle/`),
  `specs/reviews/review-20260811.md`, `specs/ROADMAP.md`, `specs/archive/122_.../baselines/
  rest-suite-disposition.md`, `specs/147-149` summaries, live test execution (see Appendix)
**Artifacts**: this report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **The 28-failure claim does NOT reproduce.** A live re-run of the "everything-else" suite on
  the current tree — `code/tests/` + `code/src/model_checker` minus `bimodal/tests` minus the
  `packaging` marker, `-n 6` — produced **1700 passed, 254 skipped, 0 failed, 0 errors in 74.10s**.
  `flake.nix:100-106`'s justification for scoping `checks.default` to bimodal-only is now false
  and should be corrected; the ROADMAP's "Follow-up task for the 28 documented 'everything-else'
  failures" item should be closed as resolved (superseded by the boundary refactor), not triaged.
- **The task description's "only two workflows exist" is itself stale.** A third workflow,
  `.github/workflows/packaging.yml`, was added by task 149 (committed the same day as this
  review) and already runs push/PR-triggered, serial, `-m packaging` coverage of
  `code/tests/packaging/`. The new general workflow must not duplicate it — and empirically
  **cannot** safely duplicate it: running `code/tests/` with `packaging`-marked tests included
  under `-n 6` produced 86 spurious `ERROR`s from a wheel/sdist build race across xdist workers
  (evidence in Appendix), none of which are real defects.
- **`nix flake check` passes cleanly today**: "all checks passed!" in 2m32s wall-clock (cold,
  this host) — checks.default's own bimodal-only pytest run agrees exactly with a standalone
  `pytest code/src/model_checker/theory_lib/bimodal/tests -n 6` (302 passed both ways).
- **Recommendation**: one new push/PR workflow running (a) `code/tests/ code/src/model_checker
  --ignore=.../bimodal/tests -m "not packaging" -n 6`, (b)
  `code/src/model_checker/theory_lib/bimodal/tests -n 6` (or just don't `--ignore` it — see
  Decision 3), and (c) `nix flake check`, on `ubuntu-latest` only across Python 3.10/3.11/3.12
  (narrower than release.yml's 3-OS matrix, with stated reason). Packaging tests and the oracle
  differential suite's cadence are both already correctly handled by existing workflows and need
  no new job.

## Context & Scope

Task 150 asks for research only: a concrete, file-and-line-level recommendation for a new
push/PR CI workflow plus a `nix flake check` gate, informed by (1) an independent, *measured*
re-verification of the flake.nix:107 "28 documented pre-existing failures" claim that currently
justifies scoping the flake's reproducibility gate to the bimodal suite alone, and (2) the actual
shape of the CLI end-to-end suite (task 148) and packaging contract tests (task 149) so the new
workflow's test selection is concrete rather than a repeat of the (partly stale) task description.
No workflow files or `flake.nix` edits were made — that is implementation work for a later phase.

## Findings

### Current workflow inventory (`.github/workflows/`)

Three workflows exist today, not two:

| File | Trigger | What it runs | Parallelism |
|---|---|---|---|
| `release.yml` | `push: tags: v[0-9]+.[0-9]+.[0-9]+` | `test-and-release` job: build+install wheel, smoke-test CLI/import, matrix `os: [ubuntu-latest, macos-latest, windows-latest] x python-version: ['3.10','3.11','3.12']`. `build` job (ubuntu only): `twine check --strict` + `pytest tests/packaging/ -v -m packaging` (added by task 149). Then TestPyPI/PyPI publish + GitHub Release. | N/A (no `-n`) |
| `differential-tests.yml` | `push`/`pull_request` path-filtered to `oracle/bimodal_logic/**`, `code/src/model_checker/theory_lib/bimodal/**`; also `workflow_dispatch` | `oracle/bimodal_logic/tests/test_cross_oracle_differential.py -m "not slow and not differential"` (main pass) then `TestCIGate`/`TestFormulaEnumerator`/etc. explicitly (belt-and-suspenders re-run) | No `-n` — fully serial |
| `packaging.yml` (task 149, new) | `push`/`pull_request`, unfiltered | `cd code && pytest tests/packaging/ -v -m packaging` (108+ tests) | No `-n` — fully serial |

**Nothing runs `code/tests/` (minus packaging) or the in-package `src/model_checker` suite on an
ordinary push/PR.** That gap (review issue 7, ROADMAP Phase 1 item 2) is real and still open —
only the count of *existing* workflows in the task description's framing is stale.

`flake.nix` (`nixpkgs#nixos-unstable`, `flake-utils`) currently exposes:
- `packages.default` — `buildPythonPackage` for `model-checker` 1.3.0, `doCheck = false` (no
  test collection during package build; see line 47-49's own comment).
- `devShells.default` — `python312` + nixpkgs' `z3-solver` (imports as `z3`, no PyPI dist-info,
  hence `pythonRemoveDeps`/`pythonRelaxDepsHook`) + `networkx`, `pytest`, `pytest-xdist`,
  `pytest-timeout`. **No `ipywidgets`/`matplotlib`/`jupyter` extras.**
- `checks.default` (lines 107-129) — `stdenv.mkDerivation` running
  `pytest src/model_checker/theory_lib/bimodal/tests -n 6 -q` only, justified by the now-false
  comment at lines 100-106 (see Decisions).

### The 28-failure claim: measured, not assumed

**Original claim** (`specs/archive/122_.../baselines/rest-suite-disposition.md`, task 122,
predates the core/theory_lib boundary refactor): `code/tests/ code/src/model_checker
--ignore=.../bimodal/tests -n 6` -> 1880 tests, 1852 passed, **28 failed**, 0 errors, 47.4s.
8 root-cause categories (A-H), all pre-existing, all independently re-run serially to rule out
xdist flakiness. Category B/G's shared cause: a malformed `"A[]"` default conclusion literal in
`code/tests/utils/helpers.py::create_test_model()` and one hardcoded duplicate in
`test_batch_output_real.py` (12 of the 28 failures).

**Re-verification method**: created an isolated venv (`/tmp/mc_verify_venv`, Python 3.13) with
`pip install z3-solver networkx pytest pytest-xdist pytest-timeout ipywidgets matplotlib jupyter
ipython` — i.e. the `jupyter`/`all` extra plus `dev` extra from `code/pyproject.toml`, matching
what the original 122 baseline almost certainly had (its run shows ~0 skips beyond the 28
failures, meaning jupyter-dependent tests were collectible and running). On this NixOS host, a
pip-installed `z3-solver` wheel cannot resolve `libstdc++.so.6` inside an isolated venv; fixed by
prepending `$(nix eval --raw nixpkgs#stdenv.cc.cc.lib)/lib` to `LD_LIBRARY_PATH` — the exact
recipe `code/tests/packaging/conftest.py::_nix_cxx_runtime_lib_dir()` already uses (task 148).

**Result** (`PYTHONPATH=code/src pytest code/tests/ code/src/model_checker
--ignore=code/src/model_checker/theory_lib/bimodal/tests -m "not packaging" -n 6 -q`):

```
6 workers [1954 items]
1700 passed, 254 skipped, 2 warnings in 74.10s (0:01:14)
```

**Zero failures, zero errors.** The Category B/G malformed `"A[]"` literal, and all other 7
categories, do not reproduce. This is consistent with the task description's framing: the
boundary refactor (and task 148's rewrite of `test_batch_output_real.py` to assert real batch
output, which touched the same file Category B's hardcoded duplicate literal lived in) resolved
the underlying causes as a side effect, not by design.

The 254 skipped (vs. ~0 in the 122 baseline) is not a regression signal — spot-checked as
environment-conditional skips (e.g. `test_inclusions.py`'s no-on-disk-notebooks cases,
theory-specific conditional skips) unrelated to the 28-failure question; none are new failures
reclassified as skips (`-rs` sampling and the full-log diff both showed only pre-existing skip
patterns, no `xfail`/`XPASS` noise).

**A packaging-inclusion artifact, not a regression**: running the same command *without*
`-m "not packaging"` (i.e. `code/tests/` unfiltered) produces **86 `ERROR`s**, 100% inside
`code/tests/packaging/` (`test_inclusions.py`, `test_parity.py`), all `AssertionError: build
failed (exit 1)` / `Backend subprocess exited when trying to invoke build_sdist`. This is a
wheel/sdist build race: `code/tests/packaging/conftest.py`'s session-scoped `built_artifacts`
fixture runs `python -m build --no-isolation` against the shared `code/` source tree once per
xdist worker (6 workers = 6 concurrent `setup.py`-style builds against the same directory), and
task 149's own fix (clearing `code/build/`/`*.egg-info` before/after each build) is not
worker-safe under this kind of parallelism. `packaging.yml` and `release.yml`'s `build` job both
already run packaging tests **serially** (no `-n` flag) — this is not a coincidence, it is the
only way this fixture is currently safe to run. **The new general workflow must exclude the
`packaging` marker** (see Decision 2) both to avoid duplicating `packaging.yml`'s coverage and to
avoid reintroducing this exact race.

### Bimodal suite and `nix flake check`, measured

- `pytest code/src/model_checker/theory_lib/bimodal/tests -n 6 -q` (this host, **while a second
  heavy pytest run was concurrently in flight** — i.e. under load): **302 passed, 0 failed, 77.13s**.
  `flake.nix`'s own comment cites 286/286 at 43.4s on an idle machine; the +16 tests are net new
  since that baseline was recorded, and the ~1.8x slowdown under concurrent load is a live,
  first-hand data point corroborating the CPU-contention-flake warning already in `flake.nix` and
  the task description's hazard bullet — not a new problem, but real evidence the concern is
  live, not theoretical.
- `nix flake check` (real build, not `--no-build`): `all checks passed!` in **2m32s** wall-clock
  on this host (cold — no prior local build of this derivation). `checks.x86_64-linux.default`'s
  own pytest run and the standalone bimodal run above agree exactly (302 passed both ways),
  cross-confirming the flake's hermetic build reaches the same result as the ordinary
  pip/PYTHONPATH path.
- **This 2m32s figure is a warm-nixpkgs-cache, single-derivation number on a dev machine.** A
  cold GitHub Actions runner with no Nix store cache will pay real evaluation+build cost
  (fetching `nixpkgs`, building/fetching `python312` + `z3-solver` + `networkx` closures) on top
  of this — budget accordingly and strongly consider a cache action (e.g.
  `cachix/install-nix-action` plus `DeterminateSystems/magic-nix-cache-action` or a `cachix` cache)
  so this isn't repeated from scratch on every push. No such action exists in this repo today
  (confirmed by grep; the only prior mention is aspirational, in an archived task-117 teammate
  finding).

### Task 148 (CLI end-to-end suite) — what it added and where it lives

- `code/tests/cli/` (new package, **not** `packaging`-marked): `test_parse_file_flags.py`
  (`ParseFileFlags` unit tests + short/long flag-equivalence sweep, 24 tests) and
  `test_flag_matrix.py` (~15-flag behavioral matrix via `python -m model_checker` subprocess, 36
  tests). Fast, no wheel build — these run as ordinary `code/tests/` tests in the new workflow.
- `code/tests/packaging/test_cli_console_script.py` and `test_generate_then_execute.py` (new,
  **`packaging`+`slow`-marked** like every other file in that directory) — real `model-checker`
  console-script invocation and the four-theory "generate a project, then run it" sweep. The
  `bimodal` case alone costs ~90-91s (per both task 148's summary and this report's own
  `--durations` output at `tests/packaging/test_generate_then_execute.py::test_generate_then_execute[bimodal]`,
  91.08s). These are already exercised by `packaging.yml` (serial) and are excluded from the new
  workflow by the same `-m "not packaging"` filter as task 149's suite (see Decision 2).
- A real production defect was found and fixed along the way (`--cvc5` crashed unconditionally,
  `code/src/model_checker/builder/runner.py`, commit `8f33ef9a`) — not relevant to workflow
  design, noted for completeness.
- **Verified, current full-suite baseline** (task 148 Phase 8, re-confirmed structurally by this
  report's own runs): top-level `code/tests/` = 468 passed/4 skipped in 151.15s (includes the
  packaging-marked console-script/generate-then-execute tests once environment-repaired);
  in-package `code/src/model_checker/` = 1902 passed in 389.99s (~6.5 min, includes bimodal).
  **The task description's cited "283 tests, ~32s" / "1910 tests, ~7min" figures are themselves
  the stale pre-task-148 baseline** (task 148's own summary documents correcting an even earlier
  283+1910=2193 citation against the true parent commit `55ea4e8f`'s measured 401+1912=2313). Use
  the numbers in this report's Appendix/tables, not the task description's, for CI timeout budgets.

### Task 149 (packaging contract tests) — what it added and where it lives

`code/tests/packaging/` (`conftest.py` + 6 test modules, all `pytestmark = [pytest.mark.packaging,
pytest.mark.slow]`), 108 tests at task-149-close, builds a fresh wheel+sdist per session and
asserts exclusion/inclusion/parity/entry-point contracts. Already wired into two CI entry points
(`packaging.yml`, `release.yml`'s `build` job) — task 149's own summary states this was a
deliberate, narrow scope, explicitly not a general CI job, and that decision holds up: the new
general workflow should route around `code/tests/packaging/` entirely via `-m "not packaging"`
rather than re-running it.

### Oracle differential suite cadence (hazard bullet 3)

This question was already substantively answered by task 138
(`specs/138_make_oracle_suite_fast_and_observable/`, referenced from
`code/docs/core/TESTING_GUIDE.md` section 8.8 and `oracle/run-oracle-suite.sh`'s own header):

- `oracle/run-oracle-suite.sh` is the **gating** variant: two passes — `-n 6` for the bulk
  (measured 649.09s solo/idle) and a serial (`xdist_serial`, zero workers) second pass for
  contention-sensitive tests (measured ~446s solo/idle) — deselecting `slow` on both passes.
  `differential-tests.yml` runs a subset of this same gating philosophy (`-m "not slow and not
  differential"`, single serial pass, no `-n`) on every push/PR touching bimodal/oracle paths.
- The **exhaustive** complexity-5 self-consistency scan (`TestFullScanReport`, `@pytest.mark.slow`)
  has its own dedicated, explicitly-invoked-only entry point,
  `oracle/run-oracle-exhaustive-scan.sh`, whose header states outright: "This is NEVER part of
  the gating path... costs roughly 60-90 minutes of wall clock... and is invoked explicitly."
  `TestBimodalHarnessIntegration` (`@pytest.mark.differential`) additionally self-skips via
  `setup_method` whenever BimodalHarness (a hardcoded sibling-checkout path,
  `/home/benjamin/Projects/BimodalHarness/src`) isn't importable — which it never will be on a
  GitHub Actions runner.
- **Conclusion**: there is no gap to fill. The exhaustive/BH-dependent tests were deliberately
  designed to be un-schedulable by task 138, not accidentally omitted. No new nightly/scheduled
  job is needed; `differential-tests.yml`'s current push/PR cadence for the gating subset is
  correct and should be left alone. The ROADMAP item can be closed with this rationale, the same
  way the 28-failures item is being closed — both were already effectively resolved by prior
  tasks (138 and the boundary refactor respectively), just not marked as such.

### Python/OS matrix (hazard bullet 2)

`release.yml`'s matrix is `os: [ubuntu-latest, macos-latest, windows-latest] x python-version:
['3.10', '3.11', '3.12']` (9 combinations) — appropriate for a release build, where the goal is
"does the published wheel install and import on every platform we claim to support." The new
push/PR gate's goal is different: fast, cheap regression detection on every commit. Recommend
**`ubuntu-latest` only, matrix `python-version: ['3.10', '3.11', '3.12']`** (3 combinations, not
9) for the new workflow, explicitly narrower than the release matrix by design:
cross-OS packaging/install breakage is a release-time concern already caught by `release.yml`
and, more cheaply, by `packaging.yml`'s wheel/sdist contract checks on every push; it is not the
kind of regression `code/tests/`/`src/model_checker` behavioral tests are testing for, and
tripling(x3 OS) the per-push cost of an already ~2.5-4 minute job for that marginal coverage is
not a good trade. State this reasoning in the workflow's own comments (per the constraint's
"or state deliberately why the PR gate runs a narrower matrix for speed").

## Decisions

1. **flake.nix:107's `checks.default` should be broadened**, since the 28-failure justification
   at lines 100-106 no longer holds. Recommend replacing the bimodal-only `checkPhase` with one
   that runs `pytest src/model_checker code/tests -m "not packaging"` (or, if the flake's
   `src = ./code` root makes `code/tests` path-awkward from inside the derivation, an equivalent
   two-invocation `checkPhase` covering both trees) — **but only after adding `ipywidgets` (and
   probably `matplotlib`) to `devPython`'s package list**. Evidence: a bare-`devShells.default`
   run of the same suite (no jupyter deps) produced genuine `AttributeError`s (not skips) in
   `code/src/model_checker/jupyter/tests/integration/test_widget_interaction.py`, because
   `unittest.mock.patch('model_checker.jupyter.interactive.widgets', ...)` requires the target
   attribute to already exist — it only exists when `ipywidgets` is actually importable, so
   missing the dep produces a hard error, not a graceful skip. This is a concrete blocker for
   naively broadening `checks.default` and should be called out explicitly in the implementation
   plan, not discovered mid-implementation. Alternative if adding the extra is unwanted: exclude
   `code/src/model_checker/jupyter/` from the broadened check via `--ignore`.
2. **Packaging-contract tests are excluded from the new general workflow**, via `-m "not
   packaging"` on every invocation that touches `code/tests/`. Two independent reasons: (a)
   `packaging.yml` (task 149) and `release.yml`'s `build` job already run them on every relevant
   trigger — including them again is pure duplication; (b) they are empirically unsafe under
   `-n 6` (86-error build race demonstrated above) — this is not a hypothetical risk, it was
   reproduced live in this research session.
3. **The in-package job should NOT `--ignore` the bimodal suite.** Unlike the diagnostic
   "everything-else" run used to verify the 28-failure claim (which excluded bimodal specifically
   to isolate it from `nix flake check`'s coverage), the new general workflow's plain-Python job
   should run the **full** `code/src/model_checker` tree, bimodal included, at `-n 6`. Rationale:
   `nix flake check`'s `checks.default` exercises the *nixpkgs-packaged* Z3/Python toolchain,
   while the plain-pip job exercises the *PyPI-published* `z3-solver` dependency users actually
   install — these are different toolchains and both are worth continuously verifying; running
   bimodal in both is deliberate cross-toolchain coverage, not redundant duplication. Use `-n 6`
   for this job (never `-n auto`), per the flake.nix-documented and this-report-reproduced
   CPU-contention flake, and prefer a generous timeout (e.g. 15-20 min) over a tight one given
   CI-runner contention.
4. **Job structure**: three logical jobs (or three steps with independent failure surfacing) —
   (a) `code/tests/` minus `packaging` marker, `-n 6`; (b) `code/src/model_checker` (all of it,
   including bimodal), `-n 6`; (c) `nix flake check`. (a)+(b) can run on the 3-way Python matrix
   on `ubuntu-latest`; (c) needs only one job (nix pins its own Python via `flake.nix`, matrix
   variation doesn't apply) and should use a Nix installer action with caching (see
   `nix flake check` finding above).
5. **No changes to `differential-tests.yml`, `packaging.yml`, or `release.yml`** are needed for
   this task's stated deliverable. Both open ROADMAP cadence questions (28-failures, oracle
   cadence) resolve to "already answered by a prior task, mark as such" rather than new work.

## Risks & Mitigations

- **Cold Nix builds inflate the `nix flake check` job's wall-clock on GitHub Actions** far beyond
  this report's 2m32s warm-cache figure. Mitigate with a Nix caching action; budget the job
  timeout generously (e.g. 20-30 min) until real CI numbers are observed.
- **Broadening `checks.default` without adding `ipywidgets` will introduce false failures**, not
  false passes — safer failure mode than the reverse, but still a footgun for whoever implements
  Decision 1 without reading this report's jupyter finding first.
- **`-n auto` anywhere in the new workflow risks reintroducing the documented CPU-contention
  flake** (`test_bimodal.py::test_example_cases[BM_CM_1-example_case7]` per the task description;
  this report's own concurrent-load bimodal run showing a 1.8x slowdown is corroborating, if
  indirect, evidence). Use `-n 6` uniformly, never `-n auto`, anywhere this workflow touches
  bimodal or the full in-package suite.
- **Packaging tests under `-n 6`/`-n auto` will race and produce spurious errors** if anyone later
  "simplifies" the workflow by dropping the `-m "not packaging"` filter — this report reproduced
  that failure mode concretely; worth a code comment in the eventual workflow file pointing back
  at this rationale (or at `packaging.yml`'s own already-serial design) so it isn't silently
  reintroduced.

## Context Extension Recommendations

- **Topic**: CI workflow inventory and design rationale.
- **Gap**: `.github/workflows/README.md` documents what exists but not the *why* of each
  scoping decision (why packaging is serial-only, why bimodal is nix-scoped, matrix-narrowing
  rationale for a PR gate vs. release build). This report's Decisions section is a reasonable
  seed for a future addition to that README once the new workflow lands, so the next person
  editing these files doesn't have to re-derive the same reasoning from scratch.

## Appendix

### Search/verification commands used

```bash
# Workflow/flake inventory
cat .github/workflows/{release,differential-tests,packaging,README}.{yml,md}
cat flake.nix

# Prior baseline (archived)
cat specs/archive/122_rootcause_crossoracle_differential_and_establish_t/baselines/rest-suite-disposition.md

# Task 147/148/149 summaries
cat specs/{147,148,149}_*/summaries/01_*.md

# Independent 28-failure re-verification (isolated venv, full deps incl. jupyter extra)
python3 -m venv /tmp/mc_verify_venv
PIP_USER=0 /tmp/mc_verify_venv/bin/pip install z3-solver networkx pytest pytest-xdist \
  pytest-timeout ipywidgets matplotlib jupyter ipython
LIBDIR=$(nix eval --raw nixpkgs#stdenv.cc.cc.lib)/lib
PYTHONPATH=code/src LD_LIBRARY_PATH="$LIBDIR" /tmp/mc_verify_venv/bin/python3 -m pytest \
  code/tests/ code/src/model_checker --ignore=code/src/model_checker/theory_lib/bimodal/tests \
  -m "not packaging" -n 6 -q --durations=15
# => 1700 passed, 254 skipped, 0 failed, 0 errors, 74.10s

# Packaging-inclusion race reproduction (86 errors, all in code/tests/packaging)
PYTHONPATH=code/src LD_LIBRARY_PATH="$LIBDIR" /tmp/mc_verify_venv/bin/python3 -m pytest \
  code/tests/ code/src/model_checker --ignore=code/src/model_checker/theory_lib/bimodal/tests \
  -n 6 -q --durations=15
# => 1732 passed, 254 skipped, 86 errors (all code/tests/packaging, build_sdist race), 135.99s

# Bimodal-only timing (under concurrent load from the run above)
PYTHONPATH=code/src LD_LIBRARY_PATH="$LIBDIR" /tmp/mc_verify_venv/bin/python3 -m pytest \
  code/src/model_checker/theory_lib/bimodal/tests -n 6 -q
# => 302 passed, 77.13s

# nix flake check, real build
nix flake check
# => all checks passed!, 2m32.169s wall-clock

# Jupyter-dep gap reproduction (bare devShells.default, no ipywidgets)
nix develop --command bash -c 'PYTHONPATH=code/src pytest code/tests/ code/src/model_checker \
  --ignore=code/src/model_checker/theory_lib/bimodal/tests -n 6 -q'
# => AttributeError in jupyter/tests/integration/test_widget_interaction.py (not a skip)
```

### References

- `flake.nix` (lines 100-129: `checks.default` and its now-false justifying comment)
- `.github/workflows/{release,differential-tests,packaging}.yml`, `.github/workflows/README.md`
- `code/pyproject.toml` (`[tool.pytest.ini_options]` markers, `[project.optional-dependencies]`)
- `code/tests/packaging/conftest.py` (`_nix_cxx_runtime_lib_dir`, `_add_cxx_runtime_to_env`,
  `_provisioning_failure`)
- `oracle/run-oracle-suite.sh`, `oracle/run-oracle-exhaustive-scan.sh`,
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
- `code/docs/core/TESTING_GUIDE.md` section 8.8 ("Oracle Suite: Gating vs. Exhaustive Split")
- `specs/archive/122_rootcause_crossoracle_differential_and_establish_t/baselines/
  rest-suite-disposition.md`
- `specs/148_cli_end_to_end_verification_suite/summaries/01_cli-e2e-verification-summary.md`
- `specs/149_wheel_and_sdist_packaging_contract_tests/summaries/01_packaging-contract-tests-summary.md`
- `specs/reviews/review-20260811.md` (issue 7), `specs/ROADMAP.md` (Phase 1 items 2-4)
