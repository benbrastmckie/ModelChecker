# Implementation Plan: Wheel and Sdist Packaging Contract Tests

- **Task**: 149 - wheel_and_sdist_packaging_contract_tests
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: specs/149_wheel_and_sdist_packaging_contract_tests/reports/01_packaging-contract-tests.md
- **Artifacts**: plans/01_packaging-contract-tests.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

`code/pyproject.toml`'s `[tool.setuptools.package-data]` allowlist and `code/MANIFEST.in`'s
sdist rules each assert — in comments only — that they stay in sync with each other and with
`theory_lib/docs/THEORY_ARCHITECTURE.md`'s Theory Contract. Nothing executable enforces any of
it, and the only artifact-touching CI job (`release.yml`) is tag-triggered and contents-blind.
This plan adds a `code/tests/packaging/` suite that builds both artifacts fresh into a pytest
temp directory, then asserts exclusions, registry-driven inclusions, wheel/sdist parity, and
console-script installability — and wires a push/PR-triggered CI job that actually runs them.
Definition of done: the four assertion families from the task description are executable and
green (or have driven a MANIFEST.in fix), the tests are selectable via a dedicated marker, and
a CI workflow runs them on every push and pull request.

### Research Integration

The research report (`reports/01_packaging-contract-tests.md`) is integrated as follows, and its
five open questions are all resolved explicitly in this plan rather than left to the implementer:

| Open question | Resolution in this plan |
|---|---|
| 1. Where do tests live? | `code/tests/packaging/` — a new subpackage split by concern. This is fixed by the task's own `file_scope`, not a free choice. |
| 2. Is the CI gap in scope? | Yes, narrowly: Phase 6 adds `.github/workflows/packaging.yml` (push/PR-triggered, runs the packaging marker only) and adds one packaging-test step to `release.yml`'s existing `build` job. Adding a general-purpose full-suite CI workflow is a **non-goal**. |
| 3. Does the sdist include `docs/*.md`? | Settled empirically in Phase 4 by inspecting the built sdist. If absent, fixing `MANIFEST.in` is in-scope remediation (`code/MANIFEST.in` is in `file_scope`). |
| 4. Exact-set vs. minimum-set docs assertions? | **Minimum-set**: the six canonical `docs/*.md` files must be present; extras (exclusion's `docs/DATA.md`) are tolerated. Matches `test_theory_conformance.py`'s existing looser style. |
| 5. Toolchain provisioning? | Self-provisioning, with an ambient fast path. A session-scoped fixture uses the ambient interpreter's `build` if importable; otherwise it provisions an isolated venv (`PIP_USER=0`, `--no-user`) and builds with `--no-isolation`. Whole sequence runs in one process, so the single-`nix develop`-invocation constraint is satisfied automatically. |

Also carried forward from research: `AVAILABLE_THEORIES = registry.get_registered()` is the
registry entry point (mirroring `theory_lib/tests/test_theory_conformance.py`'s parametrization
precedent); `code/tests/conftest.py`'s autouse `test_isolation` fixture restores `cwd`/`sys.path`
and must be confirmed compatible with subprocess-based builds; `code/build/` and `code/dist/`
hold stale artifacts that must never be read.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only. Two Durable Decisions bear directly on this work and
become executable for the first time here:

- **Package identity**: the `oracle/` tree is "kept as a standalone, unpacked top-level tree —
  outside `code/src/` and excluded from the wheel". Phase 2's exclusion assertion is the first
  executable enforcement of that decision.
- **Enforced three-layer dependency model**: names `code/tests/test_layering.py` and
  `theory_lib/tests/test_theory_conformance.py` as the pattern of "not aspirational
  documentation: enforced by an executable test". This task extends that same pattern to the
  packaging contract, which is currently comment-guarded only.

No ROADMAP.md edits are made by this plan.

## Goals & Non-Goals

**Goals**:
- Build wheel and sdist fresh from `code/` into a pytest temp directory, never reading
  `code/dist/` or `code/build/`.
- Assert the six exclusion classes hold in both artifacts: `oracle/`, `TODO.md`,
  `theory_lib/*/history/`, `theory_lib/*/reports/`, `theory_lib/*/examples_refactored/`,
  `__pycache__/`+`*.pyc`.
- Assert registry-driven inclusions per theory: `VERSION`, `README.md`, `CITATION.md`,
  `LICENSE.md`, the six-file `docs/*.md` minimum set, and `notebooks/*.ipynb` where present on
  disk.
- Assert wheel/sdist parity over a precisely defined normalized path set.
- Assert the `model-checker` console script installs and runs from a fresh venv.
- Register a dedicated pytest marker so the suite is selectable/deselectable.
- Wire a CI job that actually runs these tests on push and pull request.
- Fix `code/MANIFEST.in` if — and only if — the built sdist demonstrates real drift.

**Non-Goals**:
- Adding a general-purpose full-test-suite CI workflow (the broader CI gap the research
  surfaced). Out of scope; Phase 6 covers packaging tests only.
- Modifying `flake.nix` to add `build`/`twine`/`check-wheel-contents` to the devShell.
- Broader console-script behavior coverage (belongs to `code/tests/e2e/`); the entry-point
  assertion here is a minimal declare-install-run liveness check.
- Cleaning up the stale `code/build/` and `code/dist/` directories (gitignored; the tests simply
  must not read them).
- Using `check-wheel-contents`/`twine` as load-bearing assertions — they check hygiene and
  metadata, not project-defined path membership.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Build fixture needs network (`pip install build`) and fails offline | H | M | Ambient fast path first (use `build` if already importable); on provisioning failure, `pytest.skip` with a loud reason when `CI` is unset, `pytest.fail` when `CI` is set — never a silent pass in CI |
| Session-scoped build makes the whole suite slow for local iteration | M | H | One build per session shared by every packaging test; dedicated `packaging` marker plus `slow` so `-m "not packaging"` deselects cleanly |
| `test_isolation` autouse fixture interacts badly with cwd changes during build | M | M | Build in a subprocess with an explicit `cwd=` argument rather than `os.chdir`; Phase 1 verifies the fixture composes cleanly |
| Parity assertion is under-specified and either always passes or is permanently red | H | M | Phase 4 defines the normalization and comparison set explicitly before writing the assertion (see Phase 4 tasks) |
| `docs/*.md` drift turns out to be real, expanding scope into a MANIFEST.in fix | M | M | `code/MANIFEST.in` is already in `file_scope`; Phase 4 budgets for the fix and re-verifies by rebuilding |
| Editing `release.yml` breaks the release pipeline | H | L | Phase 6 adds one additive pytest step to the existing `build` job; no changes to triggers, matrix, or publish steps |
| Registered theory set changes later, breaking hardcoded expectations | M | L | Parametrize off `registry.get_registered()`, assert nothing about the count of theories, and assert `notebooks/` only where present on disk |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 5 | 1 |
| 3 | 4 | 1, 3 |
| 4 | 6 | 2, 3, 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Build Fixture and Marker Registration [COMPLETED]

**Goal**: A `code/tests/packaging/` package exists whose session-scoped fixture builds a fresh
wheel and sdist into a temp directory and exposes their member-path listings, with a registered
`packaging` marker.

**Tasks**:
- [x] Create `code/tests/packaging/__init__.py` and `code/tests/packaging/conftest.py`.
- [x] Add to `code/pyproject.toml`'s `[tool.pytest.ini_options] markers` list:
      `"packaging: Tests that build and inspect wheel/sdist artifacts -- slower than unit tests, requires a build toolchain"`,
      matching the existing one-line-docstring style.
- [x] Implement session-scoped fixture `packaging_toolchain`: returns the interpreter to build
      with. Fast path — if `import build` succeeds in the ambient interpreter, return
      `sys.executable`. Otherwise create a venv under `tmp_path_factory.mktemp("pkgvenv")`, then
      run `pip install --no-user build setuptools wheel` with `PIP_USER=0` in the subprocess env,
      and return the venv interpreter path.
- [x] Implement the provisioning-failure policy: on venv/pip failure, `pytest.skip` with an
      explicit reason when `os.environ.get("CI")` is falsy; `pytest.fail` when it is set. Never
      silently pass.
- [x] Implement session-scoped fixture `built_artifacts`: runs
      `{interp} -m build --no-isolation --outdir {tmp}` with `cwd=` the `code/` directory
      (resolved from `Path(__file__)`, never `os.chdir`), asserts exactly one `*.whl` and one
      `*.tar.gz` land in `{tmp}`, and returns both paths. The output directory must be a pytest
      temp dir — never `code/dist/`.
- [x] Implement helpers `wheel_members(whl)` (via `zipfile.ZipFile.namelist()`) and
      `sdist_members(tgz)` (via `tarfile.open().getnames()`), each returning a `frozenset[str]`,
      plus `normalize_sdist(path)` stripping the leading `{name}-{version}/` component.
- [x] Add a smoke test asserting both artifacts were produced, both member sets are non-empty,
      and `model_checker/__init__.py` appears in the wheel.
- [x] Confirm `code/tests/conftest.py`'s autouse `test_isolation` fixture composes cleanly with
      the subprocess build (run the smoke test twice in one session and confirm no cwd or
      `sys.path` leakage). Verified via `test_isolation_fixture_composes_with_build`, which reads
      the session-scoped `built_artifacts`-derived fixture a second time and confirms cwd/sys.path
      are unchanged from the autouse `test_isolation` snapshot.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: This phase assumes exactly two new files under `code/tests/packaging/`
plus one edit to `code/pyproject.toml`'s markers list. Confirm at implementation time by listing
the phase's actual diff; if the fixture needs a third module (e.g. a shared `helpers.py`), record
the addition rather than silently absorbing it.

**Files to modify**:
- `code/pyproject.toml` - add `packaging` marker to `[tool.pytest.ini_options] markers`
- `code/tests/packaging/__init__.py` - new, empty package marker
- `code/tests/packaging/conftest.py` - new; toolchain + build fixtures and member helpers
- `code/tests/packaging/test_build_smoke.py` - new; fixture smoke test

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/packaging/ -v -m packaging` builds both artifacts and
  passes.
- `cd code && PYTHONPATH=src pytest tests/ -m "not packaging" --collect-only` still collects the
  existing suite without error (marker addition breaks no existing selection).
- `git status` shows no new files under `code/dist/` or `code/build/`.

---

### Phase 2: Exclusion Assertions [COMPLETED]

**Goal**: Both artifacts are proven free of every excluded path class named in the task
description.

**Tasks**:
- [x] Create `code/tests/packaging/test_exclusions.py`.
- [x] Define the exclusion predicates as a module-level table so each class is a separately
      named, separately failing test: `oracle/` (any path component), `TODO.md` (any location),
      `theory_lib/*/history/`, `theory_lib/*/reports/`, `theory_lib/*/examples_refactored/`,
      `__pycache__/` and `*.pyc`.
- [x] Parametrize each exclusion over both artifacts (wheel and normalized sdist) so a failure
      names both the class and the artifact.
- [x] On failure, include the offending member paths in the assertion message (not just a
      boolean) so drift is diagnosable from CI logs alone.
- [x] Mark the module `@pytest.mark.packaging` and `@pytest.mark.slow`.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: Six exclusion classes are asserted, per the task description. Confirm at
implementation time that the enumerated set in `test_exclusions.py` matches the six named in the
task and in `MANIFEST.in`'s `prune`/`global-exclude` lines; if `MANIFEST.in` names a class the
task omits (or vice versa), record the discrepancy rather than quietly picking one list.

**Files to modify**:
- `code/tests/packaging/test_exclusions.py` - new

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/packaging/test_exclusions.py -v` passes for both
  artifacts across all exclusion classes.
- Negative check: temporarily add an assertion for a path known to be present (e.g.
  `model_checker/__init__.py`) and confirm the failure message lists it; revert.

---

### Phase 3: Registry-Driven Inclusion Assertions [NOT STARTED]

**Goal**: Every registered theory is proven to ship its contract-required metadata, docs, and
notebooks in both artifacts, with the theory list driven off the registry.

**Tasks**:
- [ ] Create `code/tests/packaging/test_inclusions.py`.
- [ ] Bind `AVAILABLE_THEORIES = registry.get_registered()` at module level and parametrize with
      `@pytest.mark.parametrize('theory', AVAILABLE_THEORIES)`, mirroring
      `theory_lib/tests/test_theory_conformance.py`. Do not hardcode theory names or counts.
- [ ] Define `REQUIRED_ROOT_FILES = ['README.md', 'CITATION.md', 'LICENSE.md', 'VERSION']` and
      `REQUIRED_DOCS_FILES = ['README.md', 'API_REFERENCE.md', 'ARCHITECTURE.md', 'ITERATE.md',
      'SETTINGS.md', 'USER_GUIDE.md']`, sourced from `THEORY_ARCHITECTURE.md`'s Theory Contract.
- [ ] Assert per theory, per artifact, that `model_checker/theory_lib/{theory}/{f}` is a member
      for each `REQUIRED_ROOT_FILES` entry.
- [ ] Assert per theory, per artifact, that `model_checker/theory_lib/{theory}/docs/{f}` is a
      member for each `REQUIRED_DOCS_FILES` entry — **minimum-set semantics**: extras such as
      exclusion's `docs/DATA.md` are tolerated and must not fail the test.
- [ ] Assert notebooks conditionally: for each `*.ipynb` present on disk under
      `theory_lib/{theory}/notebooks/`, assert the corresponding member exists in both
      artifacts. A theory with no notebooks directory yields no assertions, not a failure.
- [ ] Mark the module `@pytest.mark.packaging` and `@pytest.mark.slow`.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: The registry is expected to resolve to four theories (`bimodal`,
`exclusion`, `imposition`, `logos`) with a six-file canonical docs set, and exclusion is expected
to carry an extra `docs/DATA.md`. These are hypotheses from research, not facts to encode:
confirm by printing `registry.get_registered()` and the on-disk `docs/` listing at implementation
time. The test itself must assert nothing about the theory count.

**Files to modify**:
- `code/tests/packaging/test_inclusions.py` - new

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/packaging/test_inclusions.py -v` passes for every
  registered theory in the wheel.
- Sdist inclusion results are recorded (they feed Phase 4's `docs/*.md` question); a sdist docs
  failure here is an expected possible outcome, not a blocker — hand it to Phase 4.
- Confirm the parametrize IDs in `-v` output list the theories the registry actually returned.

---

### Phase 4: Wheel/Sdist Parity and MANIFEST.in Remediation [NOT STARTED]

**Goal**: The parity invariant both allowlists' comments assert is executable, and the
`docs/*.md` sdist question is settled empirically — with `MANIFEST.in` fixed if it is real drift.

**Tasks**:
- [ ] Create `code/tests/packaging/test_parity.py`.
- [ ] Define the comparison set precisely before asserting. Normalize the sdist by stripping the
      `{name}-{version}/src/` prefix; restrict both sides to members under `model_checker/`;
      exclude `*.dist-info/*`, `*.egg-info/*`, and sdist-only root metadata
      (`PKG-INFO`, `setup.py`, `pyproject.toml`, `MANIFEST.in`, `README.md`, `LICENSE`).
      Record this definition as a module docstring so a future reader can see what parity means
      here rather than re-deriving it.
- [ ] Assert set equality of the `.py` module paths under `model_checker/` between the two
      artifacts.
- [ ] Assert set equality of the packaged **data** paths (the `README.md`/`CITATION.md`/
      `LICENSE.md`/`VERSION`/`docs/*.md`/`notebooks/*.ipynb` classes) under `model_checker/`.
      Report symmetric difference in the failure message, split into wheel-only and sdist-only.
- [ ] Run the parity test and record the concrete outcome for `docs/*.md`: present in both,
      wheel-only, or sdist-only.
- [ ] If (and only if) `docs/*.md` is confirmed wheel-only, add the mirroring rule to
      `code/MANIFEST.in` (a `recursive-include src/model_checker/theory_lib */docs/*.md`-shaped
      rule consistent with the file's existing style), rebuild, and re-run Phases 2-4 to confirm
      the fix introduces no new exclusion violation.
- [ ] If `docs/*.md` is already present in both, leave `MANIFEST.in` unchanged and record in the
      test docstring that setuptools' `include-package-data` auto-fold is what makes it hold —
      so a future reader does not "fix" a non-bug.
- [ ] Mark the module `@pytest.mark.packaging` and `@pytest.mark.slow`.

**Timing**: 1.25 hours

**Depends on**: 1, 3

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: Research flags `docs/*.md` as a *candidate* drift with no MANIFEST.in
mirror rule, but notes `include-package-data = true` may auto-fold package-data into
`SOURCES.txt`. Confirm by inspecting the built sdist's member list directly — never by reasoning
about setuptools internals. The `MANIFEST.in` edit is conditional on that observation and must
not be made pre-emptively.

**Files to modify**:
- `code/tests/packaging/test_parity.py` - new
- `code/MANIFEST.in` - conditional; only if the built sdist proves real drift

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/packaging/ -v` fully green.
- If `MANIFEST.in` changed: rebuild and re-run the whole packaging suite, and confirm the
  `git diff` on `MANIFEST.in` is limited to added rules (no removals, no reordering).
- Full gate: `PYTHONPATH=code/src pytest code/tests/ -v` and the in-package suite both green.

---

### Phase 5: Console-Script Entry-Point Assertion [NOT STARTED]

**Goal**: The `model-checker` console script is proven to install from the built wheel and run.

**Tasks**:
- [ ] Create `code/tests/packaging/test_entry_point.py`.
- [ ] Add a session-scoped fixture that creates a fresh venv under a pytest temp dir and installs
      the built wheel into it with `PIP_USER=0` in the subprocess env and `--no-user` on the pip
      invocation.
- [ ] Assert the `model-checker` script exists at the venv's `bin/` (POSIX) or `Scripts/`
      (Windows) path and is executable.
- [ ] Run `model-checker --version` (falling back to `--help` if `--version` is not a supported
      flag — confirm which at implementation time) via subprocess and assert exit code 0.
- [ ] Assert the declared entry point resolves: `model_checker.__main__:run` is importable in the
      installed venv.
- [ ] Keep the scope minimal — no assertions about CLI output content beyond a non-empty stdout.
- [ ] Mark the module `@pytest.mark.packaging` and `@pytest.mark.slow`.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: This phase assumes installing the wheel pulls `z3-solver` and `networkx`
from the network. Confirm at implementation time; if the install is prohibitively slow or offline,
apply the same CI-gated skip/fail policy established in Phase 1 rather than weakening the
assertion.

**Files to modify**:
- `code/tests/packaging/test_entry_point.py` - new

**Verification**:
- `cd code && PYTHONPATH=src pytest tests/packaging/test_entry_point.py -v` passes.
- The venv is created under a pytest temp dir; confirm nothing is written to the repo tree.

---

### Phase 6: CI Wiring [NOT STARTED]

**Goal**: A CI job actually runs the packaging tests on every push and pull request, and
release-time builds are contents-checked rather than only metadata-checked.

**Tasks**:
- [ ] Create `.github/workflows/packaging.yml`: triggered on `push` and `pull_request`, checks
      out, sets up a supported Python (match the version already used in `release.yml`), installs
      the package's test dependencies plus `build`, and runs
      `cd code && python -m pytest tests/packaging/ -v -m packaging`.
- [ ] Scope the workflow narrowly — packaging tests only. Do not add a general full-suite job.
- [ ] Add one additive step to `release.yml`'s existing `build` job that runs the packaging tests
      against the artifacts it already builds. Do not change triggers, the matrix, or any publish
      step.
- [ ] Confirm the new workflow's YAML parses and its job/step names are distinct from existing
      workflows.
- [ ] Update `.github/workflows/README.md` to describe the new workflow alongside the existing
      two.

**Timing**: 0.75 hours

**Depends on**: 2, 3, 4, 5

**Verification Tier**: interface

**Scope Hypothesis**: This phase asserts exactly three touched files
(`.github/workflows/packaging.yml`, `.github/workflows/release.yml`,
`.github/workflows/README.md`). Confirm against the actual diff; `release.yml`'s existing `build`
job structure must be read before editing, since the plan's description of it is from research,
not from the file.

**Files to modify**:
- `.github/workflows/packaging.yml` - new; push/PR-triggered packaging test job
- `.github/workflows/release.yml` - additive packaging-test step in the `build` job
- `.github/workflows/README.md` - document the new workflow

**Verification**:
- `python -c "import yaml,sys; [yaml.safe_load(open(f)) for f in sys.argv[1:]]" .github/workflows/*.yml`
  parses cleanly.
- `git diff .github/workflows/release.yml` shows only added lines within the `build` job.
- The `release.yml` trigger block is byte-identical to its pre-edit state.

**Note on `file_scope`**: this phase touches `.github/workflows/`, which is outside the task's
declared `file_scope` (`code/pyproject.toml`, `code/MANIFEST.in`, `code/tests/packaging/`). The
expansion is deliberate and required by the task description's own instruction to "ensure whatever
CI job runs them actually does run them" — research confirmed no existing job runs the general
suite, so satisfying that instruction cannot be done within the declared scope. The expansion is
held to the minimum that satisfies it.

---

## Testing & Validation

- [ ] `cd code && PYTHONPATH=src pytest tests/packaging/ -v -m packaging` — full packaging suite
      green.
- [ ] `cd code && PYTHONPATH=src pytest tests/ -m "not packaging" -q` — existing top-level suite
      unaffected by the marker addition, and the packaging tests are genuinely deselectable.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` — full top-level suite green.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/ -q` — in-package suite green.
- [ ] Confirm no test reads `code/dist/` or `code/build/`:
      `grep -rn "dist/\|build/" code/tests/packaging/` returns only `--outdir` temp-dir usage.
- [ ] Confirm the working tree is clean of build byproducts after a full run
      (`git status --short` shows no new untracked artifacts inside the repo).
- [ ] Deliberate-drift smoke check: temporarily remove one `docs/*.md` entry from
      `pyproject.toml`'s package-data list, rebuild, confirm Phase 3 or Phase 4 goes red, then
      revert. This proves the suite actually detects drift rather than trivially passing.

## Artifacts & Outputs

- `code/tests/packaging/__init__.py`
- `code/tests/packaging/conftest.py`
- `code/tests/packaging/test_build_smoke.py`
- `code/tests/packaging/test_exclusions.py`
- `code/tests/packaging/test_inclusions.py`
- `code/tests/packaging/test_parity.py`
- `code/tests/packaging/test_entry_point.py`
- `code/pyproject.toml` (marker registration)
- `code/MANIFEST.in` (conditional remediation)
- `.github/workflows/packaging.yml`
- `.github/workflows/release.yml` (additive step)
- `.github/workflows/README.md`
- `specs/149_wheel_and_sdist_packaging_contract_tests/summaries/01_packaging-contract-tests-summary.md`

## Rollback/Contingency

Every phase is additive except the conditional `MANIFEST.in` edit and the `release.yml` step.

- Test files and the new workflow: delete `code/tests/packaging/`, delete
  `.github/workflows/packaging.yml`, and revert the `code/pyproject.toml` marker line. Nothing
  else in the repository depends on them.
- `MANIFEST.in`: revert the added rules and rebuild; the pre-existing sdist contents are restored
  exactly, since the edit only adds `recursive-include` rules.
- `release.yml`: revert the single added step. The release pipeline is unchanged in every other
  respect, so a revert cannot leave it in a half-modified state.
- If the build fixture proves unworkable in CI (Phase 1 blocked), mark Phase 1 `[BLOCKED]`, keep
  the test modules uncommitted, and escalate — the remaining phases have no value without a
  working build fixture and must not be worked around by inspecting stale `code/dist/` artifacts.
