# Research Report: Portable, Pinned Release-Verification Runner

- **Task**: 156 - portable_pinned_release_verification_runner
- **Started**: 2026-08-12T16:45:00Z
- **Completed**: 2026-08-12T17:20:00Z
- **Effort**: ~1 hour (research only)
- **Dependencies**: None
- **Sources/Inputs**: `.github/RELEASE_SETUP.md`; `flake.nix`; `specs/archive/125_release_engineering_and_pypi_rehearsal/` (plan, `PUBLISH-CHECKLIST.md`, `rehearsal/*`); `code/scripts/verify-refactor.sh`; `code/tests/packaging/conftest.py`, `test_parity.py`; `.gitignore`; `code/pyproject.toml`; PyPI JSON API (`build`, `twine`, `check-wheel-contents`, `model-checker`); local `check-wheel-contents --version`; `nix eval` probe
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-formats.md, report-format.md

## Executive Summary

- `.github/RELEASE_SETUP.md:142-148` ("Local Rehearsal (No Publish)") names `python -m build`,
  `check-wheel-contents`, `twine check --strict`, and a parity diff against
  `model-checker==1.2.12`, but points only at a stale archived evidence directory
  (`specs/archive/125_release_engineering_and_pypi_rehearsal/rehearsal/`) — there is no runnable
  artifact behind the prose.
- `flake.nix`'s `devShells.default` (line 103-104) wraps only `devPython` (lines 67-98), which
  carries `nixZ3, setuptools, pip, networkx, pytest, pytest-xdist, pytest-timeout, ipywidgets,
  matplotlib, typing-extensions` — confirmed: no `build`, no `twine`, no `check-wheel-contents`.
- `nix eval --raw nixpkgs#check-wheel-contents.name` independently reproduces the task
  description's claim: `error: flake 'flake:nixpkgs' does not provide attribute
  'packages.x86_64-linux.check-wheel-contents...'` — not resolvable from nixpkgs. The locally
  installed copy (`/home/benjamin/.nix-profile/bin/check-wheel-contents`) reports `0.6.3`, which
  matches PyPI's current latest (`check-wheel-contents` `info.version == "0.6.3"`,
  `requires_python == ">=3.10"`).
- `specs/archive/125_release_engineering_and_pypi_rehearsal/` already solved provisioning once:
  Phase 4 of its plan (lines 200-244) established venv-inside-`nix develop`, `PIP_USER=0`, and
  single-invocation `TMPDIR` as load-bearing constraints, and its `rehearsal/` directory shows
  the exact evidence-file naming the new runner must mirror. That evidence is stale — the
  `PUBLISH-CHECKLIST.md` still cites it as current, which task 156 must correct.
- `code/scripts/verify-refactor.sh` is the closest scripting precedent: `#!/usr/bin/env bash`,
  `set -uo pipefail`, `SCRIPT_DIR`/`REPO_ROOT` resolution + `cd`, a `for arg in "$@"` flag parser,
  `note()`/`fail()` helpers with a `FAILURES` counter, and `exit 1` iff `FAILURES>0` else `exit 0`.
- PyPI pins confirmed: `build==1.5.0`, `twine==7.0.0` (requires Python >=3.10 — compatible with
  the flake's Python 3.12), `check-wheel-contents==0.6.3`. `model-checker`'s PyPI `info.version`
  is `1.2.12` — confirmed as the last published release and the correct `<REF>` default.

## Context & Scope

Task 156 requires building an executable runner (`code/scripts/release-verify.sh`), a pinned
tool manifest (`code/scripts/release-tools-requirements.txt`), and rewritten checklist prose in
`.github/RELEASE_SETUP.md`, all reusing the venv-inside-`nix develop` technique the archived task
125 already worked out — not re-deriving it. This report is research only; no files were
modified.

## Findings

### 1. `.github/RELEASE_SETUP.md` current state

- File is 178 lines total (verified via `wc -l`).
- The `### Local Rehearsal (No Publish)` heading is at line 142; the body (lines 144-148) reads:
  > "The build/check portion of the pipeline can be rehearsed locally without any credentials or
  > network publish calls — see
  > `specs/archive/125_release_engineering_and_pypi_rehearsal/rehearsal/` for a worked example
  > (`python -m build`, `check-wheel-contents`, `twine check --strict`, and a parity diff against
  > the previously published `model-checker==1.2.12`)."
- This is pure prose pointing at an archived, one-off, now-stale evidence directory — there is no
  script, no pinned versions, nothing runnable. It is also the only place in the repo that
  mentions `check-wheel-contents` at all (confirmed by the task description's own grep and
  independently consistent with what this research found: no `.github/workflows/*.yml` invokes
  it — `release.yml`'s `build` job runs only `twine check --strict`, per that workflow's
  "Workflow Overview" section reproduced in `RELEASE_SETUP.md` lines ~70-92).
- Section 3 ("Ordered Release Steps") still cross-references
  `specs/archive/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` for the
  full user-only release sequence — that pointer should remain, since it documents the tag/push
  sequence, distinct from the rehearsal-evidence pointer this task must fix.

### 2. `flake.nix` devShell contents

- `devShells.default` (`flake.nix:103-104`): `packages = [ devPython ];` — nothing else.
- `devPython` (`flake.nix:67-98`) is `python.withPackages` over: `nixZ3` (the nixpkgs-native Z3
  Python binding), `setuptools`, `pip`, `networkx`, `pytest`, `pytest-xdist`, `pytest-timeout`,
  `ipywidgets`, `matplotlib`, `typing-extensions`. Each inclusion carries an inline comment
  explaining why it's needed (timeout-plugin requirement, jupyter widget mocking requirement,
  undeclared transitive dependency, etc.) — there is no comment anywhere suggesting `build`,
  `twine`, or `check-wheel-contents` were ever considered for inclusion.
  `nativeBuildInputs = [ devPython ]` also appears in the `checks.default` derivation
  (`flake.nix:140`), which is a separate, non-shell derivation for `nix flake check` — not
  relevant to `nix develop` provisioning.
- Confirms the task description's premise exactly: the devShell is fully instrumented for the
  test suite but carries zero packaging/release tooling.

### 3. Archived rehearsal technique (task 125)

- Directory: `specs/archive/125_release_engineering_and_pypi_rehearsal/`. Contains
  `plans/01_release-engineering-pypi-rehearsal.md`, `PUBLISH-CHECKLIST.md`,
  `progress/phase-{1..5}-progress.json`, `summaries/01_release-engineering-summary.md`, and the
  `rehearsal/` evidence directory (11 files, no subdirectories).
- **Plan Phase 4** ("NixOS-Safe Local Build Rehearsal and Parity Diff", lines 200-244) is the
  authoritative source of the technique and states the three constraints verbatim:
  - Line ~208-211: required `PIP_USER=0`/`--no-user` because `~/.config/pip/pip.conf` sets
    `install.user=true` globally on this NixOS host, which a venv install rejects otherwise.
  - Line ~210-211: "required running the entire venv+build+check+diff sequence in a single
    `nix develop` invocation since each invocation gets a fresh, non-persisting `TMPDIR`."
  - Line 206: `python -m venv "$TMPDIR/rehearsal-venv"` created **inside** `nix develop`, so
    `flake.nix` is never touched.
- **Evidence file names actually produced** (verified via `find` over `rehearsal/`, matching the
  task description's required mirror set exactly):
  `build.log`, `new-wheel-files.txt`, `parity-diff.md`, `pip-download-1.2.12.log`,
  `ref-1.2.12-wheel-files.txt`, `sha256sums.txt`, `top-level-dir-diff.txt`, `twine-check.txt`,
  `wheel-contents.txt`, `wheel-files-diff.txt`. (The task description's required set adds one the
  archive doesn't have as a separate file — a `--ignore W002` variant of the
  check-wheel-contents run — since the archived rehearsal predates the VERSION-file duplication
  that now triggers W002; this is new, not a mismatch to reconcile.)
- **`PUBLISH-CHECKLIST.md`** (`specs/archive/.../PUBLISH-CHECKLIST.md:40-48`) cites the same
  `rehearsal/` directory as **current, reviewable evidence** in its Section 1 pre-flight
  checklist ("Review the Phase 4 local rehearsal evidence..."). Per the task's "CORRECT A STALE
  CLAIM" directive, this is now false: `check-wheel-contents` no longer reports clean (W002 fires
  on the four theory_lib `VERSION` file duplicates) and the recorded sha256sums no longer match
  the post-refactor tree. Deliverable 3's rewrite of `RELEASE_SETUP.md` must not re-cite this
  evidence as current; it is historical context only.
- **Rehearsal evidence content** (for calibrating the new runner's evidence-file format):
  - `twine-check.txt`: two lines, `Checking dist/<wheel>: PASSED` / `Checking dist/<sdist>:
    PASSED` (ANSI color codes embedded in the captured file).
  - `wheel-contents.txt`: `check-wheel-contents` summary line (`dist/<wheel>: OK`) followed by the
    full `File Name / Modified / Size` listing (this is `check-wheel-contents`'s own verbose
    listing output, not something the runner constructs).
  - `parity-diff.md`: a hand-authored Markdown report (artifact identity table with SHA256s, file
    count summary, a "Classified Differences" section separating expected/intended deltas from
    unclassified ones, and a "Conclusion" stating the diff is evidentiary, not a release gate).
    The task's `<REF>` default (1.2.12) and the "informational, not a gate" framing for the
    parity diff both trace directly to this file's own stated conclusion.
  - `sha256sums.txt`: three lines — new wheel, new sdist, reference wheel — each `sha256  path`.
  - `build.log`: raw `python -m build` stdout/stderr (isolated-env pip installs, setuptools
    deprecation warnings, per-file `adding '...'` lines, final `Successfully built ...` line),
    plus a trailing `dist/` directory listing appended by the rehearsal's own capture logic (not
    something `python -m build` itself prints).
  - `pip-download-<version>.log`: raw `pip download --no-deps` output.
  - `top-level-dir-diff.txt` / `wheel-files-diff.txt`: raw unified `diff` output between
    maxdepth-2 directory listings / full sorted file listings of the two wheels.

### 4. `code/scripts/verify-refactor.sh` conventions

Closest existing precedent for a checked-in Bash verification runner in this repo:

- Shebang `#!/usr/bin/env bash`; header comment block (lines 1-39) documents purpose, numbered
  steps, and a `Usage:` line.
- `set -uo pipefail` (line 40) — note: **not** `-e`; the script accumulates failures rather than
  aborting on the first one.
- Path-independence pattern (lines 42-44):
  ```bash
  SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
  cd "$REPO_ROOT"
  ```
- Flag parsing via `for arg in "$@"; do case "$arg" in ... esac; done` (lines 47-51) — a single
  boolean flag (`--skip-oracle`) in this precedent; task 156's runner needs positional/named
  args (`<REF>` with a default, `--out DIR`), which is a step beyond this precedent's shape but
  consistent with its plain-Bash argument style (no `getopts`, no external arg-parsing library).
- `note()`/`fail()` helpers (lines 100-102): `note()` echoes `[verify-refactor] $*`; `fail()`
  echoes `[verify-refactor] FAIL: $*` to stderr and increments a `FAILURES` counter — never exits
  immediately, so the whole check sequence always runs to completion and reports one consolidated
  failure count at the end (lines 296-302: `exit 1` iff `FAILURES>0`, else `exit 0`).
- Named evidence files: intermediate command output is captured to named files under `/tmp/`
  (e.g. `/tmp/verify-refactor-bimodal-1.txt`, referenced in the corresponding `fail` message) —
  the same "every step writes a named file, referenced by the failure/success message" discipline
  task 156's Deliverable 1 requires, just targeting `/tmp/` instead of a task-controlled `--out`
  directory (verify-refactor.sh has no `--out` concept; the new runner introduces one).
- Delegates to other scripts rather than re-implementing their logic inline where one already
  exists (line 280: `bash oracle/run-oracle-suite.sh`) — directly analogous to task 156's
  requirement that the release-rehearsal re-run task "consume the runner rather than open-code
  the sequence" once this task lands.
- No `--out`/output-directory parameter exists in this precedent — every existing repo script in
  `code/scripts/` (`compare_bimodal_baseline.sh`, `comparison.py`, `verify-refactor.sh`) writes
  either to `/tmp/` or to a fixed relative path, never to a caller-supplied directory. Task 156's
  `--out DIR` parameter is a genuinely new convention for this script family, not one to copy
  from an existing file.

### 5. `code/tests/packaging/` — what it already verifies (so the runner doesn't duplicate it)

Seven files: `test_build_smoke.py`, `test_cli_console_script.py`, `test_entry_point.py`,
`test_exclusions.py`, `test_generate_then_execute.py`, `test_inclusions.py`, `test_parity.py`,
plus shared `conftest.py`.

- **`conftest.py`** builds a fresh wheel+sdist into a pytest temp dir every session (never
  reading stale `code/dist/`), with an **ambient-fast-path / venv-fallback** toolchain
  provisioning pattern directly relevant to task 156's runner:
  - Fast path: use `build` if already importable in the current interpreter (no venv, no
    network).
  - Fallback: `venv.EnvBuilder(with_pip=True)`, then `pip install --no-user build setuptools
    wheel` with `env["PIP_USER"] = "0"` set explicitly — the **exact same** `PIP_USER=0`/
    `--no-user` requirement the archived rehearsal plan documented, independently re-derived
    here as a fixture-level workaround for the same `~/.config/pip/pip.conf`
    `install.user=true` setting.
  - Failure policy: `pytest.skip` (loud reason) when `CI` is unset, `pytest.fail` when `CI` is
    set — "packaging drift must never pass silently in CI" (docstring, lines 1-11). This
    skip/fail split does not directly transfer to release-verify.sh (a standalone script has no
    pytest skip concept), but the underlying principle — network/provisioning failure must never
    produce a silent, success-looking partial evidence set — is exactly what the task description
    demands for steps (a) and (e) of Deliverable 1.
  - `installed_venv` fixture also prepends a Nix C++ runtime dir to `LD_LIBRARY_PATH` so a
    pip-installed `z3-solver` wheel can resolve its bundled `libz3.so`/`libstdc++.so.6` inside an
    isolated venv on NixOS (`_nix_cxx_runtime_lib_dir()` / `_add_cxx_runtime_to_env()`,
    `conftest.py:70-152`). This is not directly needed by `release-verify.sh` (which does not
    need to *run* the installed package, only build/check/diff it), but is a useful precedent if
    the runner's `--out`-directory verification ever needs to actually import `model_checker`.
- **`test_parity.py`** asserts **wheel/sdist internal structural parity** — that
  `[tool.setuptools.package-data]` and `MANIFEST.in` stay in sync by comparing `.py` module sets
  and packaged-data-file sets between a freshly built wheel and sdist from the *current* tree.
  This is a completely different comparison axis from task 156's runner: `test_parity.py`
  compares **wheel vs. sdist of the same build**; the runner's parity diff compares **this
  build's wheel vs. the last published PyPI release's wheel** (cross-version, not
  cross-artifact-type). No overlap/duplication — the runner complements this suite rather than
  re-testing it.
- None of the seven files invoke `check-wheel-contents` or `twine check` at all — those two tools
  are entirely absent from the automated test suite, confirming the task description's claim
  that "Nothing in `.github/` invokes the tool; the only reference is that prose line" extends to
  `code/tests/` as well.

### 6. Pinnable PyPI versions and nixpkgs non-resolvability

Confirmed directly against PyPI's JSON API (`https://pypi.org/pypi/<name>/json`, `info.version`):

| Tool | Latest PyPI version | `requires_python` |
|------|---------------------|--------------------|
| `build` | `1.5.0` | (not separately queried; Python 3.12 in devShell is well within any reasonable floor) |
| `twine` | `7.0.0` | `>=3.10` |
| `check-wheel-contents` | `0.6.3` | `>=3.10` |

All compatible with the flake devShell's `python312` interpreter. `check-wheel-contents 0.6.3` is
also exactly the version already present in the developer's ambient nix profile
(`/home/benjamin/.nix-profile/bin/check-wheel-contents --version` → `check-wheel-contents
0.6.3`) — pinning to `0.6.3` reproduces current observed behavior (including the W002 finding)
rather than introducing a version drift on day one.

**nixpkgs non-resolvability, independently reconfirmed**: `nix eval --raw
nixpkgs#check-wheel-contents.name` (run directly during this research) failed with:
```
error: flake 'flake:nixpkgs' does not provide attribute 'packages.x86_64-linux.check-wheel-contents.name', 'legacyPackages.x86_64-linux.check-wheel-contents.name' or 'check-wheel-contents.name'
```
This corroborates (via a different attribute-path probe than the task description's four
listed attempts) that the tool cannot be pulled from nixpkgs, supporting Deliverable 2's
decision to pin via a `pip`-installed `requirements.txt` rather than a Nix package reference.

### 7. Last published PyPI release (parity-diff `<REF>`)

Confirmed via `https://pypi.org/pypi/model-checker/json`: `info.version == "1.2.12"`. The
`releases` object's key set (0.1 through the 1.2.x series) contains no version newer than
`1.2.12`. This matches the task description's expected default and the archived rehearsal's own
choice of reference version — no drift since the July 2026 rehearsal. `code/pyproject.toml`
currently declares `version = "1.3.0"` (unchanged since the archived rehearsal), so the runner's
fresh local build will again produce `model_checker-1.3.0-*` artifacts to diff against the
`1.2.12` reference — the same comparison shape as the archived evidence, just re-run against the
current (post-refactor) tree.

### 8. `.gitignore` and file-scope confirmation

- `.gitignore:13` is `**/dist` (confirmed via `sed -n` + `grep -n`), matching the task
  description's citation exactly — `code/dist/` is git-ignored, so the runner may build there (or
  anywhere under an `--out` directory) without staging anything unintended.
- `code/scripts/README.md` documents several scripts (`comparison.py`, `quantifier_benchmark.py`,
  etc.) with a `## <script>` + `### Usage` + `### Flags`/`### Output Files` convention, but does
  **not** document `verify-refactor.sh` or `compare_bimodal_baseline.sh` — i.e. not every
  verification/gate script in this directory gets a README entry under current practice. Adding
  one for `release-verify.sh` would be consistent with the README's existing style but is not
  strictly required by precedent; the task's own `file_scope` already lists
  `code/scripts/README.md`, so a documentation entry is still the expected deliverable-adjacent
  action.

## Decisions

None — this is a research-only dispatch. No files were modified; `flake.nix` and no workflow
file were touched, per the dispatch instructions.

## Recommendations

1. **Runner skeleton**: base `code/scripts/release-verify.sh` structurally on
   `verify-refactor.sh`'s conventions — `#!/usr/bin/env bash`, `set -uo pipefail`,
   `SCRIPT_DIR`/`REPO_ROOT` resolution + `cd`, `note()`/`fail()` helpers — but extend the
   argument parser beyond `verify-refactor.sh`'s single-boolean-flag `case` loop to accept a
   positional or named `<REF>` (default `1.2.12`) and `--out DIR`.
2. **Toolchain provisioning**: reuse the exact `PIP_USER=0` / `--no-user` venv-inside-`nix
   develop` recipe from the archived plan's Phase 4 (and independently corroborated by
   `code/tests/packaging/conftest.py`'s `packaging_toolchain`/`installed_venv` fixtures) —
   `python -m venv "$TMPDIR/..."`, `pip install --no-user -r
   code/scripts/release-tools-requirements.txt`, all inside one `nix develop` invocation so the
   non-persisting `TMPDIR` constraint is satisfied.
3. **Evidence file naming**: mirror the archived `rehearsal/` file names verbatim (`build.log`,
   `twine-check.txt`, `wheel-contents.txt`, `new-wheel-files.txt`,
   `ref-<version>-wheel-files.txt`, `wheel-files-diff.txt`, `top-level-dir-diff.txt`,
   `pip-download-<version>.log`, `sha256sums.txt`, `parity-diff.md`), adding the new
   `--ignore W002` variant's own named file (e.g. `wheel-contents-ignore-w002.txt`) since no
   archived precedent exists for it.
4. **`RELEASE_SETUP.md` rewrite scope**: replace only the "Local Rehearsal (No Publish)" section
   (lines 142-148) to point at the runner and describe its evidence files/exit-code contract;
   leave the "Test Release Workflow (Dry Run on GitHub)" section and the
   `PUBLISH-CHECKLIST.md` cross-reference in "Ordered Release Steps" untouched, since those cover
   unrelated, still-accurate ground.
5. **Do not re-cite archived `rehearsal/` evidence as current** anywhere in the new prose — per
   the task's "CORRECT A STALE CLAIM" directive, its check-wheel-contents result and sha256sums
   no longer reproduce.

## Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| `TMPDIR` non-persistence across `nix develop` invocations silently truncates a multi-step evidence run | Single-invocation design (already scoped in Deliverable 1) — verified necessary by the archived plan's own documented failure mode |
| `check-wheel-contents` W002 exit is misread as "the tool is broken" by a future reader | Deliverable 4's reading guide must explicitly document the expected nonzero exit and the `--ignore W002` companion run, per the task's "EXPECT W002 TO FIRE" directive |
| Network-dependent steps (venv tool install, `pip download` of the reference release) fail silently and produce a partial evidence set that looks complete | Task description already requires a named, clear error on failure for steps (a) and (e) — no additional risk found beyond what's already scoped |

## Appendix

- `.github/RELEASE_SETUP.md` lines 142-148 (Local Rehearsal section), lines ~55-136 (OIDC setup
  and Workflow Overview, for cross-reference only).
- `flake.nix` lines 67-98 (`devPython`), 103-117 (`devShells.default`), 135-157
  (`checks.default`, for contrast — not the shell consumed here).
- `specs/archive/125_release_engineering_and_pypi_rehearsal/plans/01_release-engineering-pypi-rehearsal.md`
  lines 200-244 (Phase 4).
- `specs/archive/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` lines 40-48.
- `specs/archive/125_release_engineering_and_pypi_rehearsal/rehearsal/*` (all 10 evidence files).
- `code/scripts/verify-refactor.sh` (full file, 303 lines).
- `code/tests/packaging/conftest.py` (full file, 344 lines); `code/tests/packaging/test_parity.py`
  (docstring + structure).
- `.gitignore` line 13.
- `code/pyproject.toml` lines 6, 9 (`name`, `version`).
- PyPI JSON API: `https://pypi.org/pypi/build/json`, `https://pypi.org/pypi/twine/json`,
  `https://pypi.org/pypi/check-wheel-contents/json`, `https://pypi.org/pypi/model-checker/json`.
- Local commands: `check-wheel-contents --version`; `nix eval --raw
  nixpkgs#check-wheel-contents.name`.
