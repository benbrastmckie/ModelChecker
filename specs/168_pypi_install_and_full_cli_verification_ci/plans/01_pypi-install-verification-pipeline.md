# Implementation Plan: PyPI Install and Full-CLI Verification Pipeline

- **Task**: 168 - Pypi install and full cli verification ci
- **Status**: [NOT STARTED]
- **Effort**: 8 hours
- **Dependencies**: Task 158 (completed -- `release.yml`'s 7-job post-158 topology is the baseline this plan extends)
- **Research Inputs**: specs/168_pypi_install_and_full_cli_verification_ci/reports/01_pypi-install-full-cli-verification-ci.md
- **Artifacts**: plans/01_pypi-install-verification-pipeline.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Make the existing `code/tests/packaging/` full-CLI verification suite (entry point, console
script, generate-then-execute across every registered theory) runnable against a *published*
artifact instead of only a locally built wheel, by parameterizing the `installed_venv` fixture
over install source. Then consume that one parameterization twice: as a post-publish PyPI
confirmation matrix in `release.yml` (which today has zero verification after `publish-pypi`),
and as a new scheduled + dispatchable `pypi-smoke.yml` with opt-in tmate SSH debugging. Both
new CI surfaces are thin wrappers around the same pytest invocation -- no fourth and fifth
hand-rolled shell smoke script. Definition of done: the default (unset-env-var) path is
byte-for-byte behaviourally unchanged for `packaging.yml` and `release.yml`'s `build` job, and a
`MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=pypi` run passes end to end from the NixOS development
host against the currently published `model-checker` release.

### Research Integration

The research report (`reports/01_pypi-install-full-cli-verification-ci.md`) is integrated as
follows:

- **Gap 1 (fixture has zero parameterization)** drives Phases 1-3, sequenced first per the
  report's recommendation 1 because it is self-contained, network-free by default, and unlocks
  both CI deliverables without duplicating any test file.
- **Gap 2 (`publish-pypi` has no post-publish verification; `verify-testpypi` is single-OS)**
  drives Phase 4. This is a genuinely new job, not an extension of 158's `verify-testpypi`.
- **Gap 3 (`pypi-smoke.yml` does not exist; tmate and tag-less version resolution have no repo
  precedent)** drives Phase 5. `unstable-watch.yml` is the only `schedule:` precedent and is
  mirrored for the trigger block only.
- **Already solved, not re-implemented**: `conftest.py`'s `_nix_cxx_runtime_lib_dir()` /
  `_add_cxx_runtime_to_env()` already repair `z3-solver`'s `libstdc++.so.6` link failure inside
  an isolated venv on a non-FHS host, and are inert on FHS/CI runners. The parameterized fixture
  keeps calling `_add_cxx_runtime_to_env(env)` on **every** branch (local/testpypi/pypi); this
  satisfies the task's "verified end-to-end from a NixOS development host" clause with no new
  code. `handle_known_venv_libz3_link_failure` remains the untouched backstop.
- **Report recommendation 2 (version resolution) is resolved below** as two code paths behind a
  single env var. **Report recommendation 3 (tmate shape) is resolved below** as
  default-false + failure-gated + step-level timeout.

### Prior Plan Reference

No prior plan. `specs/168_pypi_install_and_full_cli_verification_ci/plans/` was empty at
planning time; this is plan version 1.

### Roadmap Alignment

`specs/ROADMAP.md` exists but no `roadmap_path` was supplied in the delegation context and no
roadmap flag was set, so no roadmap review/update phases are included and ROADMAP.md is not
modified by this plan. For reference only: this task sits under the roadmap's
release-engineering theme (Phase 1's "Merge and publish 1.3.0 [USER-ONLY]" entry and the 158
TestPyPI-gate lineage), but advances no roadmap checkbox directly -- it hardens the pipeline
those entries depend on. No agent performs any publish, push, tag, or PR step at any point in
this plan (`.claude/rules/pr-prohibition.md`).

## Resolved Design Decisions

These are settled here so the implementer does not re-litigate them. Each was an open question
in the research report.

### D1. Source selector: two env vars, no new pytest CLI option, no new marker

| Variable | Values | Default (unset) |
|----------|--------|-----------------|
| `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE` | `local`, `testpypi`, `pypi` | `local` -- current behavior exactly |
| `MODEL_CHECKER_PACKAGING_INSTALL_VERSION` | a literal version (e.g. `1.3.7`), or the sentinel `latest` | unset -- pin to `code/pyproject.toml`'s `version` |

Rationale (from the report): no `pytest_addoption` hook exists anywhere in `code/` (`code/conftest.py`
and `code/tests/conftest.py` both checked), so a CLI flag is new plumbing; an env var matches the
`CI`/`PIP_USER` convention this fixture module already uses. A new pytest *marker* is rejected
because marker registration lives in `code/pyproject.toml`, which is **outside this task's
file_scope**.

An unrecognized value for either variable must `pytest.fail` with the offending value echoed --
fail-fast per project principles, never a silent fallback to `local`.

### D2. Version resolution: two distinct code paths behind one variable

Per report recommendation 2, these are genuinely two contracts and must not be collapsed:

1. **Exact pin (default, `..._INSTALL_VERSION` unset)**: parse `version = "..."` from
   `code/pyproject.toml` -- the same literal `preflight` already treats as ground truth. Correct
   immediately after a release tag; **wrong** on an arbitrary `master` commit between releases,
   where that version is not yet published. This is the path `release.yml`'s new confirmation
   matrix uses.
2. **Latest-from-index (`..._INSTALL_VERSION=latest`)**: query the JSON API
   (`https://pypi.org/pypi/model-checker/json`, or `https://test.pypi.org/pypi/model-checker/json`
   for `testpypi`) and take `info.version`. Correct on any commit with no tag context. This is
   the path `pypi-smoke.yml`'s `schedule:` trigger uses. Resolution happens **in the fixture**,
   not in workflow shell, so both workflows stay thin and the logic is unit-testable.
3. **Explicit literal**: used verbatim, no network lookup. Escape hatch for a human debugging a
   specific published version via `workflow_dispatch`.

Do **not** substitute `pip index versions` (stale advice in
`code/docs/development/PYPI_RELEASE_GUIDE.md:149`, flagged by 158; that file is outside
file_scope and is not touched here).

### D3. Index URLs and retry mirror `verify-testpypi` exactly

- `testpypi`: `--index-url https://test.pypi.org/simple/ --extra-index-url https://pypi.org/simple/`
  (TestPyPI does not mirror `z3-solver`/`networkx`), always with an exact `==` pin -- test.pypi.org
  still carries a stale `0.1` from a pre-CI manual upload that an unpinned install would resolve.
- `pypi`: default index, `==` pin.
- Bounded retry for index propagation lag: 10 attempts, 15s apart, mirroring `verify-testpypi`'s
  loop. No other retry idiom exists in this repo to reuse.

### D4. Byte-level artifact tests are not applicable in index mode

`test_build_smoke.py`, `test_parity.py`, `test_inclusions.py`, and `test_exclusions.py` consume
`wheel_member_set`/`sdist_member_set` (i.e. `built_artifacts`), not `installed_venv`. They assert
on the *local build's* bytes and are already covered by `release.yml`'s `build` job and
`packaging.yml`. In index mode they must not force a local build.

Mechanism (all inside `code/tests/packaging/conftest.py`, i.e. inside file_scope):
- `installed_venv` requests `built_artifacts` **lazily**, via `request.getfixturevalue("built_artifacts")`
  inside the `local` branch only -- so index mode never triggers a local `python -m build`.
- A `pytest_collection_modifyitems` hook adds a `skip` marker, carrying an explicit
  "not applicable for install source `{source}`" reason, to any item whose fixture closure
  includes `built_artifacts`, when the source is non-local. This is a
  correct-by-design not-applicable skip, distinct from `_provisioning_failure`'s CI-gated
  skip/fail policy, which is unchanged.

This keeps both new workflows able to invoke the generic `pytest tests/packaging/` path rather
than hardcoding a test-file list that a future CLI test would silently miss.

### D5. `release.yml` job graph

New job `verify-pypi`, `needs: [publish-pypi]`, matrix `os: [ubuntu-latest, macos-latest,
windows-latest]` x `python-version: ['3.10', '3.11', '3.12']` (matching `requires-python` and
the existing `test-and-release` matrix), `fail-fast: false`. `github-release`'s `needs:` is
extended to include `verify-pypi`, so a failed cross-platform confirmation blocks *announcing*
the release. The package cannot be unpublished at that point -- the value is a loud, per-OS
signal before the GitHub Release page exists, not a rollback.

Cost note to state in the job comment: this adds 9 post-publish legs per release. It runs only
on the `v*.*.*` tag path, so the per-release cost is bounded and the per-push cost is zero.

### D6. `pypi-smoke.yml` tmate shape

Per report recommendation 3, with no repo precedent to copy: `mxschmitt/action-tmate@v3`, gated
on a `workflow_dispatch` boolean input `debug_tmate` that **defaults to `false`**, with
`if: ${{ failure() && inputs.debug_tmate }}` and its own `timeout-minutes` cap so an unattended
`schedule:` run can never hang waiting for a human who is not there. This mirrors how
`release.yml` already gates its `skip_testpypi` boolean off by default.

### D7. Both new pytest invocations carry `and not unstable`

Marker expression `-m "packaging and not unstable"`, matching `release.yml`'s `build` job.
`code/tests/ci/test_unstable_deselection_wiring.py` scans only `tests.yml`, `flake.nix`,
`differential-tests.yml`, and `run-oracle-suite.sh` -- it does not scan `release.yml` or
`pypi-smoke.yml`, and extending its scanned-file list is outside this task's file_scope (see
Non-Goals).

## Goals & Non-Goals

**Goals**:
- `installed_venv` installs from local wheel (default, unchanged), TestPyPI, or PyPI, selected
  by env var, with both version-resolution contracts of D2.
- `release.yml` gains a cross-platform post-publish PyPI confirmation matrix that reuses the
  packaging suite rather than a fourth inline shell smoke script.
- `pypi-smoke.yml` exists: `schedule:` + `workflow_dispatch:` (with `version` and `debug_tmate`
  inputs), reusing the same suite.
- The published package is verified end to end from the NixOS development host via the existing
  `_add_cxx_runtime_to_env` repair, with no new NixOS-specific code.
- Default-path behavior and runtime cost of `packaging.yml` and `release.yml`'s `build` job are
  unchanged.

**Non-Goals**:
- No publish, push, tag, or PR is performed at any point (`.claude/rules/pr-prohibition.md`).
  Verification runs against already-published artifacts only.
- No changes to `code/pyproject.toml` (no new marker, no new `addopts`) -- outside file_scope.
- No rewrite of `test-and-release`'s or `verify-testpypi`'s existing inline shell smoke scripts
  onto the new fixture. They work, they are on 158's just-landed gating path, and touching them
  is churn this task does not need. (Worth a follow-up task; note it in the summary.)
- No extension of `code/tests/ci/test_unstable_deselection_wiring.py`'s scanned-driver list to
  cover `release.yml`/`pypi-smoke.yml` -- `code/tests/ci/` is outside file_scope. Note as a
  follow-up.
- No update to `code/docs/development/PYPI_RELEASE_GUIDE.md`'s stale `pip index versions`
  advice -- outside file_scope, still unowned.
- No re-assertion of wheel/sdist byte contents against index-installed artifacts (same bytes CI
  already checked pre-upload).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Fixture change silently alters the default local path, breaking `packaging.yml` / `build` | H | M | Default resolves to the exact current code path; Phase 3 verification runs the full packaging suite with the env var unset and diffs pass/skip counts against a pre-change baseline recorded in Phase 1 |
| Index-mode run forces an unwanted local `python -m build` (slow, needs `build` installed) | M | M | D4's lazy `request.getfixturevalue` + collection-hook skip; Phase 3 verifies no build occurs in index mode |
| New 9-leg post-publish matrix is flaky on macOS/Windows for reasons unrelated to the package (`z3-solver` wheel resolution) | M | M | `fail-fast: false` so one leg's failure still yields full per-platform signal; retry loop absorbs index propagation lag; job is post-publish so it cannot block the publish itself |
| `pypi-smoke.yml`'s scheduled run hangs waiting on tmate | H | L | `debug_tmate` defaults false, step gated on `failure() && inputs.debug_tmate` (never reachable from `schedule:`), step-level `timeout-minutes`, job-level `timeout-minutes` |
| JSON-API `info.version` returns a yanked or pre-release version | M | L | Echo the resolved version loudly before installing; explicit-literal escape hatch (D2.3) available via `workflow_dispatch` input |
| Windows path handling in the venv/console-script helpers regresses under the new branch | M | L | `_venv_bin_dir`/`_console_script_path` are untouched; the new code changes only what is passed to `pip install`, not venv layout |
| Cannot verify workflow YAML without pushing | M | H | Phase 6 validates with `actionlint` if available, else a Python YAML parse plus a structural assertion of `needs:`/`if:`/matrix keys; explicitly reported either way |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Baseline capture and RED tests for the source selector [NOT STARTED]

**Goal**: Record the current packaging-suite baseline, then write failing tests that pin the
env-var contract (D1) and both version-resolution paths (D2) before any fixture code exists.

**Tasks**:
- [ ] Record a pre-change baseline: `cd code && python -m pytest tests/packaging/ -v -m packaging`
  -- save the pass/skip/fail counts and the skip reasons into
  `specs/168_pypi_install_and_full_cli_verification_ci/baselines/` (create the directory lazily).
- [ ] Create `code/tests/packaging/test_install_source_selection.py`, marked `packaging`, with
  RED tests for the pure helpers Phase 2 will add to `conftest.py`:
  - `_resolve_install_source()`: unset -> `local`; each of `local`/`testpypi`/`pypi` -> itself;
    unrecognized value -> failure carrying the offending value.
  - `_resolve_install_version(source)`: unset -> the literal parsed from `code/pyproject.toml`;
    an explicit literal -> itself, with no network call; `latest` -> delegates to the JSON-API
    lookup (assert via monkeypatched lookup function, never a live network call in this test).
  - `_pypi_json_api_url(source)`: `pypi` -> `https://pypi.org/pypi/model-checker/json`;
    `testpypi` -> `https://test.pypi.org/pypi/model-checker/json`.
  - `_pip_install_args(source, version)`: `local` -> the wheel path form; `testpypi` -> both
    index URLs plus `model-checker=={version}`; `pypi` -> default index plus the `==` pin.
- [ ] Use `monkeypatch.setenv`/`delenv` for every env-var case so no test leaks state.
- [ ] Confirm the new tests fail for the right reason (missing helpers), not an import error in
  an unrelated module.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: this phase asserts the baseline suite is green-or-explicitly-skipped
before any change, and that exactly one new test module is added. Confirm by running the
baseline command above and recording its actual counts -- if the suite is already red or
skipping on this host, record that fact in the baseline file and proceed against the recorded
state rather than assuming green.

**Files to modify**:
- `code/tests/packaging/test_install_source_selection.py` - new RED test module for the selector
  and version-resolution helpers
- `specs/168_pypi_install_and_full_cli_verification_ci/baselines/` - new; pre-change suite
  baseline

**Verification**:
- New module collects, and every new test fails with a `NameError`/`AttributeError`/`ImportError`
  naming a missing helper.
- No pre-existing packaging test changes status relative to the recorded baseline.

---

### Phase 2: Implement the selector and version-resolution helpers [NOT STARTED]

**Goal**: Turn Phase 1 GREEN by adding the pure helper functions to
`code/tests/packaging/conftest.py`. No fixture is rewired in this phase.

**Tasks**:
- [ ] Add module-level constants for the two env-var names (D1) and the three source values.
- [ ] Implement `_resolve_install_source()` -- unset -> `local`; validated against the closed
  three-value set; `pytest.fail` with the offending value on anything else.
- [ ] Implement `_pyproject_version()` -- parse `version = "..."` from `CODE_ROOT / "pyproject.toml"`
  with the same `grep`-equivalent single-line match `preflight` uses; fail loudly if absent.
- [ ] Implement `_pypi_json_api_url(source)` and `_latest_published_version(source)` (JSON API
  lookup via `urllib.request` -- no new third-party dependency; bounded timeout; loud failure
  message naming the URL on any non-200/parse failure).
- [ ] Implement `_resolve_install_version(source)` per D2's three cases.
- [ ] Implement `_pip_install_args(source, version, wheel_path)` per D3, returning the argument
  list appended after `pip install --no-user`.
- [ ] Extend the module docstring with a short subsection naming the two env vars, their
  defaults, and the two version-resolution contracts.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Files to modify**:
- `code/tests/packaging/conftest.py` - new helper functions and constants; docstring subsection

**Verification**:
- `cd code && python -m pytest tests/packaging/test_install_source_selection.py -v` is fully
  green.
- `cd code && python -m pytest tests/packaging/ -v -m packaging` matches the Phase 1 baseline
  exactly (helpers are not yet wired into any fixture, so nothing else may move).

---

### Phase 3: Parameterize `installed_venv` and gate the byte-level tests [NOT STARTED]

**Goal**: Wire the helpers into `installed_venv` with a retry loop, make the local build lazy,
and skip byte-level artifact tests in index mode (D4) -- with the default path provably
unchanged.

**Tasks**:
- [ ] Change `installed_venv`'s signature to take `request` and drop the direct `built_artifacts`
  parameter; obtain the wheel via `request.getfixturevalue("built_artifacts")` inside the `local`
  branch only.
- [ ] Keep `_add_cxx_runtime_to_env(env)` and the `PYTHONPATH`-stripping / `PIP_USER=0` env
  construction on **every** branch, before the install (this is the NixOS clause; do not
  duplicate or reimplement it).
- [ ] For non-local sources: resolve the version, echo it, and run the `pip install` through a
  bounded 10-attempt / 15s-sleep retry loop (D3), failing via `_provisioning_failure` with the
  attempt count and last stderr tail on exhaustion.
- [ ] Keep the existing `handle_known_venv_libz3_link_failure` backstop reachable unchanged.
- [ ] Add `pytest_collection_modifyitems` implementing D4's not-applicable skip, with a reason
  string naming the resolved source.
- [ ] Add an assertion (or a loud log line) that the installed `model_checker.__version__`
  matches the resolved version in index mode, so a stale-index install cannot pass silently.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: full

**Scope Hypothesis**: this phase asserts that exactly three test modules consume `installed_venv`
(`test_entry_point.py`, `test_cli_console_script.py`, `test_generate_then_execute.py`) and
exactly four consume the build-artifact fixtures (`test_build_smoke.py`, `test_parity.py`,
`test_inclusions.py`, `test_exclusions.py`), and that **none of those seven files needs editing**.
Confirm at implementation time with
`grep -ln 'installed_venv' code/tests/packaging/test_*.py` and
`grep -ln 'wheel_member_set\|sdist_member_set\|built_artifacts' code/tests/packaging/test_*.py`
before relying on the split; if a file appears in both lists or a new one appears, adjust the
collection hook rather than the test file.

**Files to modify**:
- `code/tests/packaging/conftest.py` - `installed_venv` parameterization, retry loop, lazy
  `built_artifacts`, `pytest_collection_modifyitems`

**Verification**:
- Default path: `cd code && python -m pytest tests/packaging/ -v -m packaging` matches the Phase 1
  baseline exactly (same passes, same skips, same reasons).
- Index path: `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=pypi cd code && python -m pytest
  tests/packaging/ -v -m "packaging and not unstable"` -- the three CLI modules run against the
  published artifact and pass; the four byte-level modules skip with the not-applicable reason;
  no local `python -m build` is invoked (confirm via `-v` output and the absence of a `pkgdist`
  temp dir).
- Invalid-value path: an unrecognized `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE` fails loudly with
  the offending value in the message.

---

### Phase 4: Post-publish PyPI confirmation matrix in `release.yml` [NOT STARTED]

**Goal**: Add a `verify-pypi` job after `publish-pypi` that runs the parameterized suite across
the OS/Python matrix, and gate `github-release` on it (D5).

**Tasks**:
- [ ] Add `verify-pypi`, `needs: [publish-pypi]`, `runs-on: ${{ matrix.os }}`, with
  `strategy: fail-fast: false` and the 3x3 `os` / `python-version` matrix.
- [ ] Steps: checkout; `actions/setup-python@v5` with `${{ matrix.python-version }}`;
  `pip install pytest build wheel`; run
  `cd code && python -m pytest tests/packaging/ -v -m "packaging and not unstable"` with
  `env: MODEL_CHECKER_PACKAGING_INSTALL_SOURCE: pypi` (version left unset -> the
  `code/pyproject.toml` exact pin of D2.1, which is correct on the tag path).
- [ ] Add `timeout-minutes` to the job, consistent with the workflow's existing jobs.
- [ ] Extend `github-release`'s `needs:` to include `verify-pypi`; re-read that job's existing
  `if:` expression and update it explicitly if it spells out upstream results (a job-level `if:`
  **replaces** the implicit `if: success()` -- the same trap `verify-testpypi`'s comment block
  already documents).
- [ ] Add a comment block on `verify-pypi` recording: why it exists (nothing verified PyPI
  post-publish before), that it deliberately reuses the packaging suite instead of a fourth
  inline smoke script, and the 9-leg per-release cost.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: interface

**Scope Hypothesis**: this phase asserts the matrix is exactly 9 legs (3 OS x 3 Python, matching
`requires-python` and the existing `test-and-release` matrix) and that `github-release` is the
only downstream job whose `needs:`/`if:` must change. Confirm by re-reading `test-and-release`'s
matrix block and by `grep -n 'needs:' .github/workflows/release.yml` before editing -- if any
other job names `publish-pypi`, include it in the edit.

**Files to modify**:
- `.github/workflows/release.yml` - new `verify-pypi` job; `github-release` `needs:`/`if:` update

**Verification**:
- YAML parses (`python -c "import yaml,sys; yaml.safe_load(open('.github/workflows/release.yml'))"`,
  or `actionlint` if available).
- Structural assertions: `verify-pypi` needs `publish-pypi`; matrix has 3 OS x 3 Python;
  `fail-fast: false` present; `github-release` needs `verify-pypi`; the pytest invocation carries
  `and not unstable` (D7).
- No other job's `needs:` or `if:` was altered.

---

### Phase 5: New `pypi-smoke.yml` workflow [NOT STARTED]

**Goal**: Add the scheduled + dispatchable smoke workflow as a thin wrapper around the same
suite, with the opt-in tmate shape of D6.

**Tasks**:
- [ ] Create `.github/workflows/pypi-smoke.yml` with a header comment stating its non-gating
  contract (it must never appear in another workflow's `needs:` nor in branch-protection
  required checks), mirroring `unstable-watch.yml`'s precedent.
- [ ] Triggers: `schedule:` with a daily cron deliberately offset from `unstable-watch.yml`'s
  `0 5 * * *` (use `0 7 * * *`), plus `workflow_dispatch:` with inputs
  `version` (string, default `''` -> the fixture's `latest` sentinel) and
  `debug_tmate` (boolean, default `false`).
- [ ] `permissions: contents: read`; job-level `timeout-minutes`.
- [ ] Steps: checkout; setup-python (single version -- 3.12, the newest supported; the
  cross-platform breadth belongs to `release.yml`'s matrix, this workflow answers "is the
  currently published artifact still installable and runnable today"); `pip install pytest build
  wheel`; run the suite with
  `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE: pypi` and
  `MODEL_CHECKER_PACKAGING_INSTALL_VERSION: ${{ inputs.version || 'latest' }}`.
- [ ] tmate step last: `mxschmitt/action-tmate@v3`, `if: ${{ failure() && inputs.debug_tmate }}`,
  with its own `timeout-minutes` cap and a comment recording why both guards are required (a
  `schedule:` run has no `inputs.debug_tmate`, so it can never reach this step).
- [ ] Echo the resolved version in the log before the pytest step so a failure report names the
  version under test.

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: local

**Files to modify**:
- `.github/workflows/pypi-smoke.yml` - new file

**Verification**:
- YAML parses; `actionlint` clean if available.
- Structural assertions: both triggers present; `debug_tmate` defaults `false`; the tmate step's
  `if:` contains both `failure()` and `inputs.debug_tmate`; the tmate step carries
  `timeout-minutes`; the pytest invocation carries `and not unstable`.
- The workflow appears in no other workflow's `needs:`
  (`grep -rn 'pypi-smoke' .github/workflows/` returns only the file itself).

---

### Phase 6: End-to-end verification from the NixOS host [NOT STARTED]

**Goal**: Prove the whole pipeline on the development host and confirm no default-path
regression anywhere, then write the summary.

**Tasks**:
- [ ] Default-path regression check: `cd code && python -m pytest tests/packaging/ -v -m packaging`
  -- diff against the Phase 1 baseline; any movement is a defect to fix, not to accept.
- [ ] Real published-artifact run from this NixOS host:
  `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=pypi` with the version left unset (exact pin to
  `code/pyproject.toml`'s current `version`) -- the three CLI modules must pass end to end
  through `_add_cxx_runtime_to_env`'s repair, not skip via the `libz3` backstop. If the pinned
  version is not yet published, re-run with `MODEL_CHECKER_PACKAGING_INSTALL_VERSION=latest` and
  record which contract was exercised.
- [ ] `latest` path check: `MODEL_CHECKER_PACKAGING_INSTALL_VERSION=latest` resolves via the JSON
  API and installs, confirming D2.2 independently of D2.1.
- [ ] `testpypi` path check: exercise the third source at least once, accepting a documented
  failure if the pinned version is absent from TestPyPI -- record the observed behavior either
  way; the point is that the branch is exercised, not that TestPyPI holds any given version.
- [ ] Run the CI-contract suite that could be affected by workflow edits:
  `cd code && python -m pytest tests/ci/ -v`.
- [ ] Validate both workflow files (actionlint if available, else YAML parse plus the structural
  assertions from Phases 4-5) and report which tool was used.
- [ ] Write `summaries/01_pypi-install-verification-pipeline-summary.md`, recording: the resolved
  design decisions as implemented, the actual observed verification output (not a claim of
  success), and the three follow-ups named in Non-Goals (fold `test-and-release`/`verify-testpypi`
  inline scripts onto the fixture; extend `test_unstable_deselection_wiring.py`'s driver list;
  fix `PYPI_RELEASE_GUIDE.md:149`'s stale `pip index versions` advice).

**Timing**: 1.5 hours

**Depends on**: 4, 5

**Verification Tier**: full

**Files to modify**:
- `specs/168_pypi_install_and_full_cli_verification_ci/summaries/01_pypi-install-verification-pipeline-summary.md` - new

**Verification**:
- Default path identical to baseline; `pypi` path green from the NixOS host with real published
  bytes; `tests/ci/` green; both workflows validate.
- Every claim in the summary is backed by quoted command output.

---

## Testing & Validation

- [ ] `cd code && python -m pytest tests/packaging/test_install_source_selection.py -v` green
      (helper-level contract, no network).
- [ ] `cd code && python -m pytest tests/packaging/ -v -m packaging` identical to the Phase 1
      baseline with the env vars unset (default path unchanged -- this is the load-bearing
      non-regression check for `packaging.yml` and `release.yml`'s `build` job).
- [ ] `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=pypi` run: three CLI modules pass against the
      published artifact; four byte-level modules skip with the not-applicable reason; no local
      build occurs.
- [ ] `MODEL_CHECKER_PACKAGING_INSTALL_VERSION=latest` resolves through the JSON API.
- [ ] Invalid env-var values fail loudly, naming the offending value.
- [ ] `cd code && python -m pytest tests/ci/ -v` green after workflow edits.
- [ ] `.github/workflows/release.yml` and `.github/workflows/pypi-smoke.yml` validate
      (actionlint preferred; YAML parse plus structural assertions as the documented fallback).

## Artifacts & Outputs

- `code/tests/packaging/conftest.py` (modified) - source selector, version resolution,
  parameterized `installed_venv`, collection hook
- `code/tests/packaging/test_install_source_selection.py` (new) - helper contract tests
- `.github/workflows/release.yml` (modified) - `verify-pypi` matrix job; `github-release` gating
- `.github/workflows/pypi-smoke.yml` (new) - scheduled + dispatchable smoke workflow
- `specs/168_pypi_install_and_full_cli_verification_ci/baselines/` (new) - pre-change suite
  baseline
- `specs/168_pypi_install_and_full_cli_verification_ci/summaries/01_pypi-install-verification-pipeline-summary.md`
  (new)
- `specs/168_pypi_install_and_full_cli_verification_ci/plans/01_pypi-install-verification-pipeline.md`
  (this file)

## Rollback/Contingency

Each phase commits separately (`per-substep` commit mode throughout), so revert granularity is
per phase:

- **Phases 4-5 fail or prove unverifiable**: revert the two workflow commits. Phases 1-3 stand
  alone -- the parameterized fixture is independently useful for manual verification from a
  developer host with no CI change at all.
- **Phase 3 regresses the default path**: revert the `installed_venv` rewiring commit only; the
  Phase 2 helpers are pure additions with no call sites and can remain harmlessly, or be
  reverted with them.
- **Whole task**: `git revert` the phase commits in reverse order. No published artifact, no
  remote state, and no `code/dist/` content is touched by any phase, so rollback is purely local
  and leaves no external side effects.
