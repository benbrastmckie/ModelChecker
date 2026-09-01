# Research: PyPI Install and Full-CLI Verification CI

**Date (UTC)**: 2026-08-31
**Dependency status**: task 158 (`harden_release_ci_testpypi_gate`) just completed in this
session. `.github/workflows/release.yml` was substantially rewritten -- read fresh below, not
from any prior memory of a 5-job topology.

## Scope

Three file_scope entries, all read in full: `.github/workflows/release.yml` (450 lines, current),
`.github/workflows/pypi-smoke.yml` (does not exist yet), `code/tests/packaging/` (9 test/support
files, all read). This report identifies exactly what remains to build for the task's three
named deliverables:

1. Parameterize `installed_venv` over install source (local wheel / TestPyPI / PyPI).
2. Add a post-publish PyPI confirmation matrix to `release.yml`.
3. Add a dispatchable + scheduled `pypi-smoke.yml` with opt-in tmate SSH debugging.

## Current `release.yml` topology (7 jobs, post-158)

`preflight` -> `test-and-release` (3x3 OS/Python matrix, builds+installs+smokes a **local**
wheel per leg) -> `build` (single ubuntu build + `twine check` + packaging pytest suite +
artifact upload) -> `publish-testpypi` (hard gate, `skip_testpypi` escape) -> `verify-testpypi`
(single ubuntu-only job: installs the just-published TestPyPI artifact with a bounded 10x/15s
retry, smoke-tests import/`__version__`/`--help`) -> `publish-pypi` -> `github-release`.

**Confirmed gap 1**: `publish-pypi` (`release.yml:339-357`) has **no verification step
whatsoever** after it -- no job depends on it except `github-release`, which only creates a
GitHub Release page and never installs anything. Unlike `publish-testpypi`, which is now gated
by `verify-testpypi`, a real PyPI publish is currently unverified end-to-end. This is exactly
task 168's "post-publish PyPI confirmation matrix" item, and it does not yet exist in any form.

**Confirmed gap 2**: `verify-testpypi` (`release.yml:301-337`) runs on a single `ubuntu-latest`
runner only -- no matrix. It proves the artifact is importable and CLI-runnable on Linux, but
says nothing about macOS/Windows install behavior for the *published* artifact. `test-and-release`
does exercise all three OSes x three Python versions (3.10/3.11/3.12, matching
`requires-python` in `code/pyproject.toml`), but only against a **freshly built local wheel**,
never anything from an index. A "confirmation matrix" against real PyPI is a genuinely new job,
not an extension of an existing one -- there is no OS/Python-matrixed index-install job anywhere
in this workflow today.

`model-checker` itself is a pure-Python, OS-independent wheel (`code/pyproject.toml:20`:
`"Operating System :: OS Independent"`; only dependency `z3-solver>=4.8.0` carries
platform-specific wheels). A cross-platform confirmation matrix against real PyPI is therefore
primarily proving `z3-solver`'s per-platform wheel resolves correctly from a real PyPI install on
each OS/Python combination -- not that `model-checker`'s own wheel differs by platform.

## `installed_venv` fixture -- zero parameterization today

`code/tests/packaging/conftest.py:246-286` (`installed_venv`): unconditionally does
`pip install --no-user <built_artifacts["wheel"]>` -- i.e. installs the **local**, freshly-built
wheel from `built_artifacts` (itself a fresh `python -m build --no-isolation` invocation, never
`code/dist/`). There is no env var, pytest CLI option, or marker anywhere in this directory (or
in `code/pyproject.toml`'s `addopts`/`markers`) that switches the install source. `git grep` for
`TESTPYPI`/`INSTALL_SOURCE`/`install_source` inside `code/tests/` and `code/pyproject.toml`
returns nothing.

Every packaging test that depends on installed CLI *behavior* (as opposed to wheel/sdist byte
contents) consumes `installed_venv` transitively:
- `test_entry_point.py` -- console-script exists/executable, `--version` runs, entry-point
  importable.
- `test_cli_console_script.py` -- `--version`/`--help` cross-checked against `python -m`, a real
  example run, and a no-`PYTHONPATH` self-sufficiency check.
- `test_generate_then_execute.py` -- registry-driven, one test per theory
  (`registry.get_registered()`): generates a real project via `BuildProject.generate()` and runs
  its `examples.py` through the installed console script end to end.

Parameterizing `installed_venv` over source is therefore the single highest-leverage change in
this task: it makes the entire existing "full CLI verification" suite (entry point + CLI
behavior + all-theory generate-then-execute) runnable against TestPyPI or PyPI with **no
duplication** of those three test files. `test_build_smoke.py`, `test_parity.py`, and
`test_inclusions.py` consume `built_artifacts`/`wheel_member_set`/`sdist_member_set` directly
(byte-level wheel/sdist contract checks), not `installed_venv` -- those stay wired to the local
build regardless of source parameterization, which is correct: TestPyPI/PyPI artifacts are the
same bytes as what CI built and uploaded, so re-asserting wheel-content parity against them adds
nothing `build`'s existing packaging-suite run doesn't already cover.

**What building the parameterization requires, concretely**:
- A source selector (env var is the natural mechanism, matching this fixture module's existing
  `CI`-env-var-driven `_provisioning_failure` pattern) with three values: local (default,
  current behavior, no network) / testpypi / pypi.
- For the testpypi/pypi branches, `built_artifacts` is no longer the install source, but the
  fixture still needs a **version to pin to** -- there is no tag/`$GITHUB_REF` available when
  this suite runs as a plain `pytest` invocation (unlike `verify-testpypi`'s job, which reads
  `${GITHUB_REF#refs/tags/v}`). The natural source of truth is `code/pyproject.toml`'s
  `version = "..."` line (same literal `preflight`'s tag-vs-pyproject check already treats as
  ground truth) -- but note this only resolves correctly when the fixture runs against a
  revision whose `pyproject.toml` version has actually been published (true right after a
  release tag; not true on an arbitrary `master` commit between releases, where the PyPI/TestPyPI
  branches would need a different resolution strategy, e.g. "latest available" via the JSON API
  described below, rather than an exact-version pin).
- Both indexes for the testpypi branch (`--index-url test.pypi.org/simple/ --extra-index-url
  pypi.org/simple/`) exactly as `verify-testpypi` already does, since TestPyPI does not mirror
  `z3-solver`/`networkx`.
- A bounded retry for index propagation lag, mirroring `verify-testpypi`'s 10x/15s loop -- no
  other retry-loop idiom exists anywhere in this repo's scripts to reuse (confirmed absent by
  158's research; still absent as of this reading).
- The venv-vs-ambient-interpreter Nix/NixOS caveat is **already solved** in this exact file:
  `_nix_cxx_runtime_lib_dir()` / `_add_cxx_runtime_to_env()` (`conftest.py:69-108`) detect a
  `nix`-on-PATH host and prepend the Nix C++ stdenv's lib dir to `LD_LIBRARY_PATH`, resolving
  `z3-solver`'s bundled `libz3.so` -> `libstdc++.so.6` link failure inside an isolated venv on a
  non-FHS host. `installed_venv` already calls this before its `pip install` (`conftest.py:277`)
  and it is inert (`nix` absent) on a standard FHS/CI Linux runner. This is precisely the
  mechanism task 168's "verified end-to-end from a NixOS development host" phrase is asking for
  -- it needs no new code, only for the parameterized fixture to keep calling it on every branch
  (local/testpypi/pypi), which is the natural outcome of extending the existing fixture rather
  than writing a parallel one. `handle_known_venv_libz3_link_failure` remains the correct
  backstop for any host where the LD_LIBRARY_PATH repair doesn't apply.
- `packaging.yml` (push/PR-triggered contract suite) runs `pytest tests/packaging/ -v -m
  packaging` with no source selector set -- confirm the new fixture's default (unset env var)
  resolves to the current local-build behavior, so this existing workflow's behavior and runtime
  cost are unchanged. `release.yml`'s `build` job's packaging-suite invocation
  (`-m "packaging and not unstable"`) has the same requirement.

## `pypi-smoke.yml` -- does not exist; no local precedent for two of its three asks

Confirmed via `ls .github/workflows/`: five workflows exist (`differential-tests.yml`,
`packaging.yml`, `release.yml`, `tests.yml`, `unstable-watch.yml`, plus `README.md`); no
`pypi-smoke.yml`.

**Scheduling precedent exists, is thin**: `unstable-watch.yml` is this repo's *only*
`schedule:`-triggered workflow (`.github/workflows/unstable-watch.yml:10-16`): `schedule: - cron:
'0 5 * * *'` (nightly) plus a bare `workflow_dispatch:` (no inputs), `permissions: contents:
read`, single job, no matrix, 20-minute timeout. This is the right shape to mirror for
`pypi-smoke.yml`'s trigger block, but the job body itself (installing and smoke-testing a
published PyPI artifact) has no analog in `unstable-watch.yml`, which just runs one pytest
marker selection.

**tmate SSH debugging has zero precedent anywhere in this repo**: `grep -rn tmate
.github/ code/` returns nothing. This is new pattern territory (the standard mechanism is
`mxschmitt/action-tmate@v3`, gated behind a `workflow_dispatch` boolean input read via
`if: ${{ inputs.debug_tmate }}` and a `timeout-minutes` cap on the tmate step itself so an
unattended scheduled run never hangs waiting for a human who isn't there -- the input must
default `false` and the step must be conditional on it, exactly mirroring how `release.yml`
already gates its own `skip_testpypi` boolean input off by default).

**Version resolution has no tag to key off**: `pypi-smoke.yml`'s `schedule:` trigger runs against
whatever `master` looks like on that day, with no `push: tags:` context and no `$GITHUB_REF`
version. `verify-testpypi`'s `${GITHUB_REF#refs/tags/v}` derivation is not reusable as-is here.
158's research report already flagged the right mechanism for this exact class of problem: the
PyPI JSON API (`https://pypi.org/pypi/model-checker/json`), noted there as the recommended
post-publish verification approach (displacing `code/docs/development/PYPI_RELEASE_GUIDE.md:149`'s
stale `pip index versions` advice, which remains untouched and out of every task's file_scope so
far). `pypi-smoke.yml` querying that endpoint for the current latest version (rather than pinning
a version literal, and rather than depending on `code/pyproject.toml`, which may be ahead of
what's actually published between releases) is the natural fit -- and if the parameterized
`installed_venv` fixture is driven by an env var carrying an explicit version rather than always
re-deriving from `pyproject.toml`, `pypi-smoke.yml` can inject the JSON-API-resolved version
into that env var directly, reusing the fixture rather than writing separate install/smoke-test
shell steps.

**Composition implication**: given the `installed_venv` parameterization above, `pypi-smoke.yml`'s
actual verification body can be as thin as "checkout, set up Python, `pip install pytest build
wheel`, set the source-selector env var to `pypi` (plus the resolved version), run `pytest
tests/packaging/ -v -m "packaging and not unstable"`" -- reusing the exact same entry-point / CLI
/ generate-then-execute suite `release.yml`'s `build` job and the proposed PyPI confirmation
matrix would also run, rather than hand-rolling a fourth copy of import/`--version`/`--help`
shell assertions (as `test-and-release` and `verify-testpypi` currently each do independently, in
slightly different shell-script forms, with no shared fixture between them). This is the
mechanism by which one fixture change serves all three of task 168's deliverables at once: the
PyPI confirmation matrix in `release.yml` and the standalone `pypi-smoke.yml` can both become
thin wrappers around `pytest tests/packaging/ -m packaging` with the source env var set to
`pypi`, rather than three independently-maintained shell-script smoke tests (`test-and-release`'s
inline script, `verify-testpypi`'s inline script, and a fourth for `pypi-smoke.yml`).

## Markers / pytest config

`code/pyproject.toml:88-97` `markers` list: `countermodel`, `theorem`, `performance`,
`differential`, `slow`, `packaging`, `unstable`, `xdist_serial`. No marker or `addopts` entry
related to install source exists. `addopts = "--durations=0 -v --import-mode=importlib"`
(`pyproject.toml:87`) has no custom `pytest_addoption` hook anywhere (`code/conftest.py`,
`code/tests/conftest.py` both checked -- neither defines `pytest_addoption`), so a new CLI flag
(vs. a plain env var) would be new infrastructure; an env var matches every existing convention
in this fixture module (`CI`, `PIP_USER`) and needs no new plumbing.

## File-scope cross-check

All three declared file_scope entries are directly implicated:
- `.github/workflows/release.yml` -- needs a new PyPI-confirmation job (matrix, post-
  `publish-pypi`, analogous in spirit to `verify-testpypi` but broader).
- `.github/workflows/pypi-smoke.yml` -- new file, schedule + workflow_dispatch (with a
  `debug_tmate` boolean input) triggers, thin wrapper around the parameterized packaging suite.
- `code/tests/packaging/` -- `conftest.py`'s `installed_venv` fixture needs the source
  parameterization; the three CLI-behavior test files need no changes themselves (they consume
  the fixture, not the source selector, directly).

No file outside these three was found to require changes for this task's three deliverables.
`code/docs/development/PYPI_RELEASE_GUIDE.md` (stale `pip index versions` advice, flagged by 158)
remains outside every task's file_scope encountered so far and is not touched by this task
either.

## Recommendations for the plan

1. Sequence: parameterize `installed_venv` first (self-contained, `code/tests/packaging/` only,
   default behavior unchanged) -> add the PyPI confirmation matrix job to `release.yml` as a thin
   wrapper around the parameterized suite -> add `pypi-smoke.yml` as a second thin wrapper
   (schedule + dispatch + tmate opt-in) reusing the same suite.
2. Decide the version-resolution contract explicitly in the plan: exact-pin via
   `code/pyproject.toml` (correct only right after a release, reusing `preflight`'s existing
   source-of-truth) vs. "latest from the PyPI JSON API" (correct on any `master` commit, needed
   for `pypi-smoke.yml`'s untied-to-a-tag schedule trigger). These likely need to be two distinct
   code paths behind the same env-var-driven fixture, not one.
3. Flag the `debug_tmate` opt-in's default-false/timeout-capped shape explicitly as a design
   decision point -- this is genuinely new infrastructure with no precedent to copy, unlike
   almost everything else in this task.
