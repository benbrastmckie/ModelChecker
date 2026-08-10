# Research Report: Task #117

**Task**: Review and stabilize the repo after recent revisions: verify the CLI works, audit discrepancies with the model-checker package on PyPI, build a Nix flake for testing on NixOS, complete full testing, and prepare a top-quality release to push to PyPI
**Date**: 2026-07-23
**Mode**: Team Research (4 teammates)
**Session**: sess_1784826587_e0b65c

## Summary

All four teammates independently converged on one central, high-confidence conclusion: **this
repository currently contains two incompatible product identities, and the release task cannot
proceed until the owner explicitly chooses between them.**

1. **The historic `model-checker` identity** — the package on PyPI (v1.2.12, 172 published
   versions, deps: `z3-solver`, `networkx`, jupyter extras), a general multi-theory
   hyperintensional framework. Its CLI in this repo is **verifiably broken right now**:
   `python -m model_checker`, `dev_cli.py`, and the CLAUDE.md-canonical
   `pytest code/tests/` all fail with `ModuleNotFoundError: No module named
   'model_checker.builder'` (and `model_checker.output.manager`).
2. **The new `bimodal-logic` identity** — `code/pyproject.toml` now declares
   `name = "bimodal-logic"`, `version = "0.1.0"`, deps: only `z3-solver`. This was a
   deliberate, ADR-backed pivot (archived task 106 ADR, status ACCEPTED: refactor into a
   focused bimodal Z3 oracle for the external BimodalHarness ecosystem). Its thin CLI
   (`bimodal-logic check`) **works** (verified). It has never been published.

The breakage is the collision of these two identities: an earlier cleanup task deleted
`model_checker/builder/` (67 files) and much of `output/` on the premise the repo was
bimodal-only, while later work (including a commit that unintentionally reintroduced ~24k
lines of `theory_lib/logos/`) restored multi-theory code that still imports the deleted
modules. Building today produces a `bimodal_logic-0.1.0` wheel that could not update the PyPI
`model-checker` project at all.

**Primary recommendation**: surface the package-identity decision to the user before planning.
Everything else — which CLI to fix, what dependencies belong in `pyproject.toml`, what "PyPI
parity" means, what the Nix flake must provide — is downstream of that single decision.

## Key Findings

### Primary Approach (from Teammate A — hands-on state assessment)

- **`model-checker` CLI broken, `bimodal-logic` CLI works** — both verified by direct
  execution. The broken `model-checker` entry point is still declared in `pyproject.toml`
  (ships a script that raises `ModuleNotFoundError` on first run).
- **`theory_lib/logos/` is half-resurrected dead code**: deleted by archived task 100,
  reintroduced by commit `feff3cbe` ("removed claude", 504 files / +24,043 lines — apparently
  an unintended side effect), and now receiving new commits (`e9734a27` first-order removal).
  It is unregistered (`AVAILABLE_THEORIES = ['bimodal']`) and internally broken (imports the
  deleted `model_checker.iterate`). `MANIFEST.in` would bundle it verbatim into any sdist.
- **Canonical test command fails**: `PYTHONPATH=code/src pytest code/tests/` hits 2 collection
  errors from stale top-level tests referencing deleted modules.
- **Bimodal suite is the one live test tree**: mostly passes but is very slow (est. 15–20+ min
  serial); `unit/test_cross_oracle_differential.py` showed 2–4 consistent, un-root-caused
  failures across two partial runs — must be investigated before any "full testing complete"
  claim.
- **PyPI parity**: local tree cannot build a successor to `model-checker` 1.2.12 without
  restoring the deleted general-theory infrastructure (`builder/`, `iterate/`, `jupyter/`,
  `networkx` dep, extras).

### Alternative Approaches (from Teammate B — prior art and tooling)

- **Nix packaging**: two drifted Nix files exist (root `flake.nix`: devShell-only, hardcoded
  `x86_64-linux`, no `networkx`, assumes sibling `../BimodalHarness/src`; older
  `code/shell.nix`: includes `networkx`, predates the pivot). Neither offers a
  `packages`/`checks` output, so there is no `nix build` or `nix flake check`.
  **Best fit**: extend the existing flake with nixpkgs-native
  `buildPythonPackage { pyproject = true; }` + `python3Packages.z3` (already correctly used;
  do NOT vendor PyPI's `z3-solver` wheel). poetry2nix/uv2nix/dream2nix are all poor fits — no
  lockfile, ~one dependency, nothing for them to solve. Retire `code/shell.nix` once the flake
  subsumes it.
- **Release workflow bugs found**: `.github/workflows/release.yml` and its README `cd Code`
  (capital C) but the directory is lowercase `code/` — fails on case-sensitive ubuntu runners.
  `RELEASE_SETUP.md` describes a two-workflow setup that doesn't match the single
  `release.yml` present.
- **2026 best practices**: migrate publishing to PyPI Trusted Publishing (OIDC) via
  `pypa/gh-action-pypi-publish` in a separate, environment-gated job (drop the long-lived
  `PYPI_API_TOKEN`); `twine check --strict`; TestPyPI rehearsal;
  `build-and-inspect-python-package` and `check-wheel-contents` for reproducible-build CI.
- **NixOS-safe parity verification**: `pip download --no-deps model-checker==1.2.12` + local
  `python -m build` + wheel content/hash diff; PyPI JSON API for cheap dependency-drift
  checks. All workable inside `nix develop`/venv without system pip.

### Gaps and Shortcomings (from Critic)

- **The CLI breakage was known and accepted at the time**: the builder-deletion task's own
  summary says "No stale imports to deleted modules (except `__main__.py` builder import,
  expected)" — the assumption that `__main__.py` was dead code was invalidated when logos
  came back, and nobody reconciled the two.
- **Testing scope is misleadingly narrow**: `pyproject.toml` pins
  `testpaths = ["src/model_checker/theory_lib/bimodal/tests"]`, so bare `pytest` structurally
  cannot detect the CLI/builder/output breakage. Any clean-baseline claim must widen the
  test scope first.
- **Versioning/changelog entirely unaddressed**: local version reads `0.0.0-dev`/`0.1.0` vs
  PyPI 1.2.12; PyPI uploads are irreversible per filename — name + version + deps must be
  right before the first upload attempt (rehearse on TestPyPI).
- **Doc drift**: root README instructs `pip install model-checker[jupyter]` and links to a
  deleted `jupyter/README.md`; `code/README.md` still says `cd ModelChecker/Code`;
  bounded follow-ups: check `docs/usage/SEMANTICS.md` for stale first-order references and
  `code/scripts/README.md` for a link to the deleted `docs/theory/QUANTIFIER_SOLVERS.md`.

### Strategic Horizons (from Teammate D)

- **The pivot was deliberate and documented** (archived ADR, ACCEPTED: three-repo
  architecture — BimodalLogic Lean spec → ModelChecker Z3 oracle → BimodalHarness bridge),
  but README/CLAUDE.md/docs/CHANGELOG were never updated to reflect it.
- **The owner's own contemporaneous framing contradicts HEAD**: the task-116 email (this
  week) tells a third party the PyPI `model-checker` package is "in good shape," GitHub is
  "mid-refactor," and describes a four-theory framework — while HEAD has only
  `bimodal/` + (broken) `logos/`; `exclusion/` and `imposition/` are gone.
- **Release risk**: publishing from HEAD either ships unrequested `bimodal-logic` noise, or —
  if someone reverts the name — silently breaks real `model-checker` users by dropping most
  of the framework. Outward-facing and hard to reverse; requires explicit user confirmation.
- **Positive-sum moves regardless of the decision**: seed the empty `specs/ROADMAP.md` with
  the identity decision once made; extend `flake.nix` with `packages.default` + `flake.lock`
  + `nix flake check` in CI (decoupled from the private BimodalHarness sibling path); migrate
  to Trusted Publishing; write an honest CHANGELOG entry.

## Synthesis

### Conflicts Resolved

1. **"Deliberate pivot" (D) vs. "accidental resurrection" (A)** — both are true at different
   layers. The bimodal-oracle pivot itself was deliberate (ADR-backed, tasks 100/101/104/106).
   The *current tree state* is accidental: commit `feff3cbe` reintroduced `theory_lib/logos/`
   as a side effect of stripping `.claude/`, and later commits kept building on it. Resolution:
   the pivot was intentional; the present hybrid state is not — which is precisely why neither
   identity currently works end-to-end.
2. **"Is the CLI broken?" (task description's uncertainty) vs. teammate findings** — resolved
   definitively: the `model-checker` CLI is broken (A, C independently reproduced); the
   `bimodal-logic check` CLI works (A verified; C had flagged it as unverified — A's direct
   execution settles it).
3. **Does `networkx` belong in the flake?** — B noted the flake omits it while `shell.nix` has
   it. Resolution: contingent on the identity decision — required if `model-checker` 1.2.x
   line continues; unnecessary for `bimodal-logic`.

### Gaps Identified

- Full bimodal test suite has never been run to completion in this research round (15–20+ min
  serial); the 2–4 `test_cross_oracle_differential.py` failures remain un-root-caused.
- `docs/usage/SEMANTICS.md` first-order staleness check (bounded follow-up from Critic).
- Whether the task-116 email's "four theories" claim obligates restoring `exclusion/` and
  `imposition/` (removed before the pivot) is unknown — only the user can say.

### Recommendations

1. **DECISION GATE (blocks planning)**: Ask the user which identity this release targets:
   - **(a) Continue `model-checker` 1.2.x** — restore `builder/`/`iterate/` (or rebuild the
     CLI on the current architecture), revert `pyproject.toml` name/version/deps, decide the
     fate of missing `exclusion`/`imposition` theories, fix logos imports, then audit parity
     against 1.2.12.
   - **(b) Formalize `bimodal-logic`** — finish deleting logos and stale tests, remove the
     broken `model-checker` entry point, rewrite README/docs/CLAUDE.md honestly, and treat
     PyPI `model-checker` as a legacy line (possibly with a final "moved/renamed" note).
   - **(c) Dual-track** — separate the oracle work (branch/repo) from the `model-checker`
     line. Highest effort; matches the ADR's three-repo intent.
   The user's task description and task-116 email both lean toward (a), but the ADR and ~15
   tasks of engineering lean toward (b) — do not let a plan silently pick one.
2. Regardless of direction: remove or repair the broken `model-checker` entry point; resolve
   the half-resurrected `logos/`; fix/delete stale `code/tests/` files so the canonical test
   command collects; widen `testpaths`; refresh README/MANIFEST.in/CLAUDE.md/CHANGELOG.
3. Nix: extend the existing root flake (multi-system, `packages.default` via nixpkgs-native
   `buildPythonPackage`, `checks.default` running the canonical suite, `flake.lock`
   committed, BimodalHarness path optional), then retire `code/shell.nix`.
4. Release engineering: fix `cd Code` casing in `release.yml`, reconcile `RELEASE_SETUP.md`,
   migrate to PyPI Trusted Publishing behind a protected environment, add TestPyPI rehearsal
   and wheel-content parity checks.
5. Testing: root-cause the cross-oracle differential failures; budget for the long suite
   runtime (or add `pytest-xdist`); only then claim a clean baseline.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (hands-on state assessment) | completed | high (medium on full-suite tally) |
| B | Alternatives (Nix/packaging/release prior art) | completed | high (low on pip-wheel-diff maturity) |
| C | Critic (gaps, blind spots) | completed | high |
| D | Horizons (strategy, roadmap) | completed | high (medium on go/no-go judgment) |

## References

- Teammate findings: `01_teammate-a-findings.md`, `01_teammate-b-findings.md`,
  `01_teammate-c-findings.md`, `01_teammate-d-findings.md` (this directory)
- PyPI JSON API: https://pypi.org/pypi/model-checker/json (v1.2.12, requires_dist)
- Archived ADR: `specs/archive/106_architecture_review_refactor/reports/04_architectural-decisions.md`
- Archived summaries: `specs/archive/100_strip_non_bimodal_code/`, `specs/archive/104_programmatic_api_cleanup/`
- Repo evidence: `code/pyproject.toml`, `flake.nix`, `code/shell.nix`, `.github/workflows/release.yml`,
  `code/MANIFEST.in`, `specs/116_draft_email_modelchecker_architecture/email-draft.md`
- External docs: PyPI Trusted Publishers, nixpkgs Python packaging docs, pyproject-nix,
  check-wheel-contents (full source list in teammate B findings)
