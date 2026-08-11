# Research Report: Executable Tests for the Packaging Contract

**Task**: 149 — Add executable tests for the packaging contract
**Surfaced by**: `specs/reviews/review-20260811.md`, issue 10

## Summary

`code/pyproject.toml` and `code/MANIFEST.in` each carry an explicit-allowlist packaging strategy
guarded only by comments asserting the two files (and `theory_lib/docs/THEORY_ARCHITECTURE.md`'s
Theory Contract) must stay in sync. Nothing executable enforces this. This report maps the exact
current state of both allowlists, the registry mechanism a test should drive its theory list
from, the one CI job that touches build artifacts at all (tag-triggered only, contents-blind),
the isolated-venv-inside-`nix develop` technique the prior release rehearsal (task 125)
established for running `build`/`twine`/`check-wheel-contents` on this NixOS host, and one
concrete, unconfirmed candidate drift between the two allowlists that the new tests should
resolve empirically rather than by re-reading the comments.

## 1. The Two Allowlists, As They Currently Stand

### `code/pyproject.toml` (wheel), lines 70-83

```toml
[tool.setuptools.package-data]
# Explicit allowlist, not a blanket "*.md" -- a bare "*.md" glob sweeps in any markdown file
# that happens to sit in a package directory (TODO.md, history/*.md, reports/*.md), regardless
# of whether it is an intentional, contract-conforming doc. See
# theory_lib/docs/THEORY_ARCHITECTURE.md's Theory Contract for the doc file set this mirrors:
# root-level README.md/CITATION.md/LICENSE.md/VERSION, the six-file docs/ set, and notebooks/.
"*" = [
    "README.md",
    "CITATION.md",
    "LICENSE.md",
    "VERSION",
    "docs/*.md",
    "notebooks/*.ipynb",
]
```
Also relevant: `[tool.setuptools] include-package-data = true`, `package-dir = {"" = "src"}`,
`[tool.setuptools.packages.find] where = ["src"]`, and `[project.scripts] model-checker =
"model_checker.__main__:run"` (the console-script entry point).

### `code/MANIFEST.in` (sdist), full text

```
include README.md
include LICENSE
include MANIFEST.in

recursive-include src *.py

recursive-include src README.md
recursive-include src CITATION.md
recursive-include src LICENSE.md
recursive-include src VERSION
recursive-include src *.ipynb

recursive-include src/model_checker/theory_lib README.md
recursive-include src/model_checker/theory_lib/logos README.md
recursive-include src/model_checker/theory_lib/bimodal README.md
recursive-include src/model_checker/theory_lib/exclusion README.md
recursive-include src/model_checker/theory_lib/imposition README.md

recursive-include src/model_checker/jupyter README.md TROUBLESHOOTING.md NixOS_jupyter.md
recursive-include src/model_checker/jupyter/debug README.md DEBUGGING.md

recursive-include src/model_checker README.md

global-exclude TODO.md
prune */theory_lib/*/history
prune */theory_lib/*/reports
prune */theory_lib/*/examples_refactored
global-exclude __pycache__
global-exclude *.pyc
```

### Candidate concrete drift: `docs/*.md` has no MANIFEST.in mirror rule

`pyproject.toml`'s package-data list includes `"docs/*.md"` (the six-file docs set:
`README.md`, `API_REFERENCE.md`, `ARCHITECTURE.md`, `ITERATE.md`, `SETTINGS.md`,
`USER_GUIDE.md` — confirmed present on disk for all four theories, e.g.
`code/src/model_checker/theory_lib/{bimodal,exclusion,imposition,logos}/docs/`). **No line in
MANIFEST.in mentions `docs/*.md` or any `docs/` path at all.** This is exactly the kind of
silent-drift case the task description warns about — the comment in MANIFEST.in claims parity
with pyproject.toml's allowlist, but the visible ruleset doesn't cover this file class.

This is flagged as a **candidate**, not a confirmed bug, because setuptools' sdist command
(`egg_info` -> `SOURCES.txt`) auto-folds `package_data` entries into the sdist manifest when
`include-package-data = true` is set (which it is here) — independently of MANIFEST.in's
`recursive-include`/`prune`/`global-exclude` directives, which are a *template* layered on top.
Whether the `docs/*.md` files therefore already end up in the sdist despite the missing
MANIFEST.in rule, or whether they are silently dropped, is exactly the kind of question this
task says to resolve by building the artifact and inspecting it — not by reasoning about
setuptools internals. **This should be the first concrete assertion the new test suite makes**,
and its outcome (present vs. absent in the built sdist) determines whether MANIFEST.in has a live
bug to fix as a byproduct of this task, or whether the comment's claim is merely undertested
but happens to hold.

## 2. Theory Registry — Drive the Theory List From Here, Not a Literal

The task says "drive the theory list off the registry, not a literal." The registry:

- `model_checker.theory_lib.AVAILABLE_THEORIES` (`code/src/model_checker/theory_lib/__init__.py:482`)
  — `AVAILABLE_THEORIES = _core_registry.get_registered()`, a live view over the core registry,
  not an independent list.
- `model_checker.registry.get_registered()` (`code/src/model_checker/registry.py:154`) — the
  underlying source of truth.

`code/src/model_checker/theory_lib/tests/test_theory_conformance.py` is the closest existing
precedent and should be mirrored structurally: it imports `from model_checker import registry`,
binds `AVAILABLE_THEORIES = registry.get_registered()` at module level, and parametrizes tests
with `@pytest.mark.parametrize('theory', AVAILABLE_THEORIES)`. It also defines the canonical
required-file constants directly from `THEORY_ARCHITECTURE.md`'s Theory Contract:
```python
REQUIRED_ROOT_ITEMS = ['__init__.py', 'operators.py', 'examples.py', 'tests', 'docs',
                        'README.md', 'CITATION.md', 'LICENSE.md', 'VERSION']
REQUIRED_DOCS_FILES = ['README.md', 'API_REFERENCE.md', 'ARCHITECTURE.md', 'ITERATE.md',
                        'SETTINGS.md', 'USER_GUIDE.md']
```
(only the first two lines of `REQUIRED_DOCS_FILES` were directly confirmed by the grep above;
the full six-file set is stated in `THEORY_ARCHITECTURE.md` lines 42-43 and independently
confirmed present on disk for all four theories — see per-theory listing below.)

Confirmed on disk (`AVAILABLE_THEORIES` currently resolves to `bimodal`, `exclusion`,
`imposition`, `logos`):

| Theory | `docs/*.md` set | `notebooks/*.ipynb` | Root metadata |
|---|---|---|---|
| bimodal | API_REFERENCE, ARCHITECTURE, ITERATE, README, SETTINGS, USER_GUIDE | none | README/CITATION/LICENSE/VERSION all present |
| exclusion | API_REFERENCE, ARCHITECTURE, DATA, ITERATE, README, SETTINGS, USER_GUIDE (7 files — DATA.md extra) | `exclusion_examples.ipynb` present | README/CITATION/LICENSE/VERSION all present |
| imposition | API_REFERENCE, ARCHITECTURE, ITERATE, README, SETTINGS, USER_GUIDE | `imposition_examples.ipynb` present | README/CITATION/LICENSE/VERSION all present |
| logos | API_REFERENCE, ARCHITECTURE, ITERATE, README, SETTINGS, USER_GUIDE | none | README/CITATION/LICENSE/VERSION all present |

Note exclusion's `docs/DATA.md` — an extra, contract-superset file; both `docs/*.md` glob-style
allowlist entries will pick it up harmlessly since the pattern is a glob, not an enumerated list,
so this is not itself a drift risk, just a fact worth the plan being aware of when asserting
exact-set-membership vs. minimum-set-membership for the docs directory.

`REQUIRED_EXCLUDE` targets named explicitly in the task (mirrored in both files' comments and in
`builder/project.py`'s `REQUIRED_COPY_ITEMS`/`OPTIONAL_COPY_ITEMS` scaffolding allowlist, which is
the analogous "what ships into a *generated project*" contract, not packaging, but shares the
same TODO.md/history/reports/examples_refactored exclusion vocabulary):
- `oracle/` (top-level, standalone tree — Durable Decision, `specs/ROADMAP.md` lines 7-8: "kept
  as a standalone, unpacked top-level `oracle/` tree — outside `code/src/` and excluded [from the
  wheel]")
- `TODO.md` (any location — `global-exclude TODO.md` / not in package-data)
- `theory_lib/*/history/` (`prune */theory_lib/*/history`)
- `theory_lib/*/reports/` (`prune */theory_lib/*/reports`)
- `theory_lib/*/examples_refactored/` (`prune */theory_lib/*/examples_refactored`)
- `__pycache__/*.pyc` (`global-exclude __pycache__`, `global-exclude *.pyc`)

## 3. CI Currently Has No Job That Runs `code/tests/` At All

This is the single most important structural finding for the plan phase, and it directly bears
on the task's instruction to "ensure whatever CI job runs them actually does run them."

`.github/workflows/` contains exactly three files:
- `release.yml` — **tag-triggered only** (`on: push: tags: 'v[0-9]+.[0-9]+.[0-9]+'`). Its
  `test-and-release` job does `python -m build`, installs the wheel, imports it, checks
  `__version__` against the tag, and runs `python -m model_checker --help` — no pytest, no
  content inspection. Its separate `build` job does `python -m build` + `twine check --strict`
  and uploads the `dist/` artifact — still no content inspection, and `twine check` validates
  metadata/README rendering, not file membership.
- `differential-tests.yml` — path-triggered only on `oracle/bimodal_logic/**` and
  `code/src/model_checker/theory_lib/bimodal/**`; runs `pytest oracle/bimodal_logic/tests/...`.
  Unrelated to packaging.
- `README.md` — documentation only.

**There is no workflow that runs `PYTHONPATH=code/src pytest code/tests/` (or any general test
suite) on a normal push or pull request.** The 283-test top-level suite and the 1910-test
in-package suite that `specs/reviews/review-20260811.md` reports running (2193/2193 green) were
run manually during that review, not by CI. Grepping `.github/workflows/*.yml` for
`pytest.*tests/\b` confirms only the oracle path above matches; nothing else invokes the general
suite.

**Consequence for this task's plan**: adding packaging-contract tests to `code/tests/` (marked
e.g. `@pytest.mark.packaging` per the task's "mark them so they can be selected/deselected"
instruction) is necessary but not sufficient — per the task's explicit requirement, some CI job
must actually invoke them. Candidates, in rough order of how directly they solve "catch drift
before release, not just at the moment of release" (recall the task's stated problem: release.yml
is tag-triggered only and "cannot catch drift until the moment of release"):
1. Add a new push/PR-triggered workflow (e.g. `.github/workflows/tests.yml`) that runs the
   general suite (or at minimum the new packaging-marked tests) on every push/PR — this is the
   only option that actually addresses "cannot catch drift until the moment of release," since
   it runs *before* a tag exists.
2. Extend `release.yml`'s existing `build` job to also run the new packaging tests against the
   artifacts it already builds — closes the "asserts nothing about CONTENTS" gap at release time,
   but does **not** close the "TAG-TRIGGERED ONLY" gap the task also names as a problem.
Both are legitimate scope for the plan; option 1 is the one that satisfies the full problem
statement, option 2 is a strict subset of what's needed for release-time coverage. The plan
should decide explicitly rather than silently picking one.

## 4. The NixOS Isolated-Venv-Inside-`nix develop` Technique (Task 125 Precedent)

The flake devShell (`flake.nix` `devPython`) ships only `nixZ3` (nixpkgs' Z3 bindings),
`setuptools`, `pip`, `networkx`, `pytest`, `pytest-xdist`, `pytest-timeout` — **no `build`,
`twine`, or `check-wheel-contents`**, and modifying `flake.nix` to add them is out of scope
(confirmed: the task description repeats this constraint, and task 125's rehearsal treated it as
hard-out-of-scope too).

Task 125 (`specs/archive/125_release_engineering_and_pypi_rehearsal/`) already solved exactly
this problem for a one-shot manual rehearsal; its findings apply directly:

- **NixOS pip constraint**: `~/.config/pip/pip.conf` sets `install.user=true` globally on this
  host. A venv's pip rejects `--user` installs against that config, so every `pip install` inside
  the venv needs `PIP_USER=0` (env var) and/or `--no-user` (flag) — confirmed necessary, not
  theoretical (task 125's plan initially omitted it and had to add it after a real failure).
- **`TMPDIR` does not persist across `nix develop` invocations**: each `nix develop` shell gets a
  fresh `nix-shell.XXXXXX` `TMPDIR`. A venv created in one `nix develop` invocation is gone in the
  next. **The entire venv-creation + build + inspect sequence must run inside a single `nix
  develop` invocation** (e.g. `nix develop --command bash -c '...'` or a heredoc script passed to
  one `nix develop -c`), never split across separate shell invocations.
- **Concrete commands task 125 used successfully** (from `parity-diff.md` and the plan's
  Testing & Validation checklist): `python -m venv "$TMPDIR/rehearsal-venv"`; activate; `pip
  install --no-user build twine check-wheel-contents` (with `PIP_USER=0` in env); `cd code &&
  python -m build`; `check-wheel-contents dist/*.whl` (result: clean, `OK`); `twine check
  --strict dist/*` (result: `PASSED` for both wheel and sdist).
- Task 125 also established the pattern of unzipping the wheel/sdist directly and diffing file
  listings (`new-wheel-files.txt`, `wheel-files-diff.txt`) rather than relying solely on
  `check-wheel-contents`, since that tool checks wheel *hygiene* (RECORD/metadata correctness,
  no stray top-level files) but does not check for the presence/absence of specific
  project-defined paths like `oracle/` or `theory_lib/*/history/` — those need direct membership
  assertions against the unzipped file list, e.g. via Python's `zipfile`/`tarfile` modules
  invoked from inside the pytest test itself (no dependency on `check-wheel-contents` needed for
  the exclusion/inclusion/parity assertions specifically; `check-wheel-contents`/`twine` remain
  useful as an orthogonal wheel-hygiene signal but are not load-bearing for the task's core
  ASSERT list).

For an **automated, repeatable pytest test** (as opposed to task 125's one-shot manual rehearsal
transcript), the same constraints apply: the test must build fresh (never trust
`code/build/`/`code/dist/`, which the task notes "currently hold stale local artifacts referenced
by no test" — confirmed: `code/dist/` and `code/build/` exist from the task-125 rehearsal and are
gitignored, not cleaned by any test), build into a pytest `tmp_path`, and if it needs `build`
outside `nix develop`'s bare devShell it either needs its own isolated venv/subprocess
bootstrapping (mirroring the task-125 technique, generalized into fixture code) or — more simply
for an in-process pytest test — can shell out to `python -m build --outdir <tmp_path>` and rely
on whatever `pip`/`build`/`setuptools`/`wheel` toolchain is already on `PATH` in the environment
the test happens to run in (which will differ between a plain host Python and `nix develop`).
The plan phase should decide whether the new tests assume `build`/`check-wheel-contents` are
already importable/on-PATH (simpler test code, but then CI/devShell provisioning becomes the
plan's job) or whether the test itself provisions an isolated venv per the task-125 pattern
(self-contained, but slower and more complex). Given the task explicitly calls out marking these
tests slow/selectable, provisioning-inside-the-test is the more robust choice for portability
across CI runners and NixOS dev machines alike, at the cost of per-test venv setup time.

## 5. Existing Test-Suite Conventions to Follow

- `code/pyproject.toml`'s `[tool.pytest.ini_options]` already declares a `markers` list including
  `slow: Genuinely expensive tests...`. A new marker (e.g. `packaging: Tests that build and
  inspect wheel/sdist artifacts — slower than unit tests, requires a build toolchain`) should be
  added here following the same one-line-docstring style, and these tests likely warrant **both**
  `@pytest.mark.slow` and a new `@pytest.mark.packaging` (or just the new marker alone, if the
  plan decides packaging tests are a distinct selection axis from generic "slow") — the task says
  "mark them so they can be selected/deselected," which argues for a dedicated marker name
  regardless of whether `slow` is also applied.
- `code/tests/test_layering.py` is the closest existing precedent for a *whole-codebase
  architectural contract* test living directly under `code/tests/` (not nested in `unit/` or
  `integration/`) — a new `code/tests/test_packaging_contract.py` (or a `code/tests/packaging/`
  subpackage, if the plan phase wants to split exclusions/inclusions/parity/entry-point into
  separate files) fits this precedent well. `code/tests/e2e/` (currently
  `test_batch_output_real.py`, `test_project_creation.py`) is the other plausible home if the
  plan phase weighs the "invokes a real build + real venv install" character as more end-to-end
  than architectural.
- `code/src/model_checker/theory_lib/tests/test_theory_conformance.py` is the direct structural
  precedent for parametrizing per-theory assertions over the registry (see Section 2) and for
  writing multi-line rationale docstrings explaining *why* the test exists, matching this
  project's established documentation-heavy test style.
- `code/tests/conftest.py` provides an autouse `test_isolation` fixture (restores `cwd`,
  `sys.path`, `sys.modules` after each test) — relevant because packaging tests will change `cwd`
  (to `code/`, to build) and manipulate `sys.path`/venvs; confirm this fixture composes cleanly
  with subprocess-based build/install rather than assuming in-process import manipulation, since
  the packaging tests' actual installs will happen in **subprocess** venvs, not the current
  interpreter, which sidesteps most of what this fixture guards against but should still be
  verified compatible.

## 6. Entry-Point Assertion Specifics

`[project.scripts]` declares `model-checker = "model_checker.__main__:run"`. The task scopes this
narrowly: "the wheel DECLARES and INSTALLS it correctly," explicitly deferring "broader
console-script behavior" to the CLI e2e suite (`code/tests/e2e/`, already exercising CLI behavior
per `test_batch_output_real.py`/`test_project_creation.py`, and per the review's own empirical
check: `model-checker --version` from an installed wheel in a fresh venv). The new test's job is
narrower and build-specific:
1. Build the wheel.
2. `pip install` it into a fresh, isolated venv (`PIP_USER=0`, per Section 4).
3. Assert the `model-checker` script exists on the venv's `bin/`/`Scripts/` path and is
   executable.
4. Run it (e.g. `model-checker --version` or `--help`, mirroring the review's own empirical
   check) and assert a zero exit code — a minimal liveness check, not full CLI behavior coverage.

## 7. Open Questions for the Plan Phase

1. **Where do the new tests live?** `code/tests/test_packaging_contract.py` (top-level,
   `test_layering.py`-style) vs. `code/tests/e2e/test_packaging_contract.py` (build+install+run
   character) vs. a new `code/tests/packaging/` subpackage split by concern (exclusions /
   inclusions / parity / entry-point). All three are consistent with existing conventions;
   Section 5 above should inform this choice but doesn't dictate a single answer.
2. **Does the CI gap (Section 3) get closed by this task, or is it flagged as a follow-up?** The
   task's own problem statement explicitly complains that release.yml is "TAG-TRIGGERED ONLY,"
   which this research confirms is doubly true — there isn't even a push/PR-triggered general
   test job to piggyback on. Closing this fully means adding a new workflow file, which is a
   larger footprint than "add tests to code/tests/"; the plan phase should decide explicitly
   whether that's in scope for task 149 or should be spun out.
3. **Does the sdist actually include `docs/*.md` despite MANIFEST.in's missing rule (Section
   1)?** This needs to be settled empirically by the new tests themselves (build the sdist,
   inspect it) — if it turns out `docs/*.md` is silently dropped from the sdist while present in
   the wheel, that is itself a real bug this task's tests will have caught, and the plan phase
   should treat "fix MANIFEST.in" as in-scope remediation alongside "add the test that would have
   caught it."
4. **Exact-set vs. minimum-set assertions for `docs/*.md`?** exclusion's extra `docs/DATA.md`
   (Section 2) means an exact-file-list assertion would need to special-case exclusion, while a
   minimum-required-set assertion (the six canonical files present, extras tolerated) matches
   `test_theory_conformance.py`'s existing looser style. Recommend the looser form for
   consistency, but flag this as a specific decision, not an accident.
5. **Toolchain provisioning strategy** (bare `PATH` assumption vs. self-provisioning isolated
   venv per test) — see the end of Section 4. This affects both runtime and portability, and
   should be decided once rather than emerging ad hoc per test.

## Files Referenced

- `code/pyproject.toml` (lines 1-140 read in full; package-data block at line 70)
- `code/MANIFEST.in` (read in full, 33 lines)
- `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` (read in full, 111 lines)
- `code/src/model_checker/theory_lib/__init__.py` (imports/registry wiring, lines 47-489)
- `code/src/model_checker/registry.py` (function inventory)
- `code/src/model_checker/theory_lib/tests/test_theory_conformance.py` (lines 1-50, structural precedent)
- `code/src/model_checker/builder/project.py` (`REQUIRED_COPY_ITEMS`/`OPTIONAL_COPY_ITEMS`, lines 43-76)
- `code/tests/test_layering.py` (docstring, lines 1-40; top-level test placement precedent)
- `code/tests/conftest.py` (lines 1-60; `test_isolation` autouse fixture)
- `code/tests/e2e/`, `code/tests/integration/` directory listings
- `.github/workflows/release.yml` (read in full, 191 lines)
- `.github/workflows/differential-tests.yml` (read in full)
- `.github/workflows/README.md` (read in full; describes the same single-workflow model)
- `flake.nix` (read in full, 143 lines)
- `specs/ROADMAP.md` (lines 1-10, 60-75; oracle exclusion Durable Decision)
- `specs/archive/125_release_engineering_and_pypi_rehearsal/summaries/01_release-engineering-summary.md`
- `specs/archive/125_release_engineering_and_pypi_rehearsal/rehearsal/parity-diff.md`
- `specs/archive/125_release_engineering_and_pypi_rehearsal/plans/01_release-engineering-pypi-rehearsal.md` (lines 30-75, 200-310)
- `specs/reviews/review-20260811.md` (issue source; summary section)
- Per-theory `docs/`, `notebooks/`, and root-metadata directory listings for
  `bimodal`/`exclusion`/`imposition`/`logos` under
  `code/src/model_checker/theory_lib/{bimodal,exclusion,imposition,logos}/`
