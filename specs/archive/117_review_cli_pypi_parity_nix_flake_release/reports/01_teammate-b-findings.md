# Teammate B Findings: Nix Packaging Prior Art, Release Workflow Patterns, PyPI Parity Verification

## Critical Cross-Cutting Issue (flag for synthesis, not just alternatives)

**`code/pyproject.toml` currently declares the wrong package identity.** Its `[project]` table
reads `name = "bimodal-logic"`, `version = "0.1.0"`, with `description`/`keywords` about a
"bimodal logic oracle" — not `model-checker`. It still ships `model-checker =
"model_checker.__main__:run"` as a console-script entry point and includes
`src/model_checker/**` via `[tool.setuptools.packages.find]`, so a build today produces a wheel
named `bimodal_logic-0.1.0-*.whl` that happens to *also* install the `model_checker` package and
CLI as a side effect — not a `model_checker-X.Y.Z` artifact at all. Any `/pypi audit` or parity
check against the real `model-checker` PyPI project must start here: this is very likely the
single largest discrepancy in scope, not an edge case. This intersects Teammate A's
current-state assessment directly — worth confirming whether this is a recent regression (git
blame the `[project]` table) before deciding remediation.

**`.github/workflows/release.yml` and `.github/workflows/README.md` both `cd Code`** (capital
C), but the actual directory is `code/` (lowercase). The `test-and-release` job's matrix
includes `ubuntu-latest`, which is case-sensitive — this step should fail there today. Combined
with the `bimodal-logic` name bug above, the release pipeline as checked in is very unlikely to
have produced a correct `model-checker` publish recently. `.github/RELEASE_SETUP.md` also
describes a two-workflow setup (`test-package.yml` + `pypi-release.yml`) that doesn't match the
single `release.yml` actually present — doc/workflow drift worth reconciling either direction.

## Key Findings

### 1. Existing Nix support is real but partial — devShell only, no package output

Two Nix files already exist, and they've drifted from each other:

- `code/shell.nix` (classic non-flake `mkShell`): `python3`, `python3Packages.z3`,
  `python3Packages.setuptools`, `python3Packages.pip`, `python3Packages.networkx`. Sets
  `PYTHONPATH`/`PATH` for in-place dev.
- `/flake.nix` (repo root): `devShells.${system}.default` only, hardcoded to
  `system = "x86_64-linux"`, `python312.withPackages` with `z3-solver`, `pytest`,
  `pytest-cov` — **missing `networkx` and `setuptools`** relative to `shell.nix`, and its
  shellHook is oriented around a sibling `BimodalHarness` checkout
  (`BIMODAL_HARNESS_SRC_DEFAULT = "../BimodalHarness/src"`), not a self-contained
  `model_checker` dev/test/build flow.

Neither file has a `packages.<system>.default` output, so there is no `nix build` artifact and
no `nix flake check`. "pip install is impractical on NixOS" is only half-solved today: you get a
shell with `z3` bindings and can `pip install -e code/` inside it (editable installs into a venv
work fine even on NixOS — the FHS problem is specifically about *system* `pip install` fighting
non-FHS shared-library paths for C-extension deps like Z3's), but there's no reproducible,
CI-checkable Nix package for `model_checker` itself.

A sibling project by the same author, `/home/benjamin/Projects/TenseModality/flake.nix`, uses
the same minimal pattern (`python311Packages.z3`, `setuptools`, devShell-only) — confirms this
is the author's established default, not a one-off, and that the gap (no package output, no
`nix flake check`) is consistent across their repos.

### 2. Nixpkgs already ships Z3's Python bindings — no need to vendor `z3-solver` from PyPI

Both existing Nix files correctly use `python3Packages.z3` (built from the `z3` C++ project's
own Python bindings), not a `fetchPypi`-wrapped `z3-solver` wheel. This is the right call:
packaging PyPI's `z3-solver` wheel for Nix requires manual wheel-format `fetchPypi` args
(`format = "wheel"`, platform tags) or a from-source rebuild anyway, while
`python3Packages.z3` is already maintained upstream in nixpkgs and importable as `z3` — matching
what `code/pyproject.toml`'s `z3-solver>=4.8.0` dependency actually needs at the API level.
Keep using `python3Packages.z3`, not a `z3-solver` derivation, in any packaged flake output.

### 3. Nix packaging tool landscape — lockfile-driven tools are overkill here

`code/pyproject.toml` has exactly one runtime dependency (`z3-solver`), a plain
`setuptools.build_meta` backend, and **no lockfile** (`poetry.lock`/`uv.lock`/`pdm.lock` do not
exist anywhere in the repo).

| Tool | Fit for this repo | Why |
|---|---|---|
| **Plain flake + `mkShell` + venv** (current) | Partial — dev only | Works today for interactive dev; no reproducible build artifact, no CI-checkable output |
| **Native nixpkgs `buildPythonPackage { pyproject = true; }`** | **Best fit** | Nixpkgs' built-in PEP 621/setuptools pyproject support handles this exact shape (single simple dep, setuptools backend) with no extra tooling; gives `nix build`, `nix develop`, and a `checks` output for `nix flake check` |
| **pyproject-nix** (lower-level library) | Fallback | Useful if hand-rolling more control over metadata parsing than `buildPythonPackage`'s `pyproject = true` gives, but adds an extra flake input for no real benefit at this dependency count |
| **poetry2nix** | Poor fit | Solves *Poetry* lockfile → Nix derivation conversion; project doesn't use Poetry, adds an unneeded flake input and Poetry-specific metadata assumptions |
| **uv2nix** | Poor fit (today) | Solves `uv.lock` → Nix derivation graph generation for many transitive deps; project has no `uv.lock` and one dependency — no resolution problem to solve. Worth reconsidering only if the project later adopts `uv` for dependency management generally |
| **dream2nix** | Poor fit | General multi-ecosystem lockfile-to-Nix framework; same "no lockfile, one dep" mismatch as above, plus more moving parts/newer, less stable tooling for this use case |

### 4. PyPI release workflow best practices (2026)

- **Trusted Publishing (OIDC) is now the recommended default**, replacing long-lived
  `PYPI_API_TOKEN` secrets. `pypa/gh-action-pypi-publish@release/v1` supports it natively: give
  the publish job `permissions: id-token: write`, omit username/password, and configure the
  trusted publisher on PyPI's project settings pointing at this repo/workflow/environment. PyPI
  docs and GitHub docs both currently push this as the security-preferred path over API tokens
  (current `release.yml` uses a `PYPI_API_TOKEN` secret + `twine upload`, which trusted
  publishing would eliminate).
- Run the publish step in a **separate job** from build/test, gated by a dedicated GitHub
  **Environment** (e.g. `pypi`) with required reviewers — limits OIDC token exposure to the
  minimum steps, and gives a manual-approval gate before anything reaches PyPI.
- Keep `twine check --strict` (current workflow already runs `twine check dist/*`, though not
  `--strict`) and a TestPyPI dry-run before the real upload — `RELEASE_SETUP.md` documents a
  `TEST_PYPI_API_TOKEN` as optional but `release.yml` doesn't actually implement a TestPyPI step.
- Version single-sourcing: `model_checker/__init__.py:24` already does
  `__version__ = get_model_checker_version()` (a function call, not a hardcoded literal) — the
  right pattern in principle. Whatever that function reads from needs to be the *same* source
  `pyproject.toml`'s `version` field is validated against, and must not be shadowed by the
  `bimodal-logic` `[project]` table currently in place (see Critical Issue above).
- Optional 2026-era hardening: `actions/attest-build-provenance` for SLSA build provenance
  attestation on the built wheel/sdist, and `pypa/build-and-inspect-python-package` as a CI
  action that builds with `SOURCE_DATE_EPOCH` pinned to the last commit (reproducible builds)
  and runs `check-wheel-contents` automatically.

### 5. Parity verification (repo vs. published PyPI artifact) — workable on NixOS

None of these require a system-wide `pip install`, so they're NixOS-safe when run inside
`nix develop` (or any venv):

- **`pip download --no-deps model-checker==X.Y.Z -d /tmp/pypi-dl`** then compare against a local
  `python -m build` of the repo at the matching tag — diff file listings (`unzip -l`) and
  content hashes (`RECORD` file in the wheel) between the two artifacts.
- **`check-wheel-contents`** (PyPI tool): lints wheel structure/file-path conventions on both the
  locally-built and PyPI-downloaded wheels; catches missing package-data, stray files, wrong
  top-level layout.
- **`pip-wheel-diff`**: takes two pip requirements, downloads/builds both, unzips, and diffs
  directly — a more turnkey version of the manual `pip download` + `unzip -l` approach above.
  Note there is a separate, differently-scoped `pip-wheel-diff` on PyPI worth double-checking
  before adopting (verify it's still maintained; it's a small niche tool).
  \[low confidence on current maintenance status — verify before relying on it in CI]
- **PyPI JSON API** (`https://pypi.org/pypi/model-checker/json`): cheap way to pull the
  currently-published `version`, `requires_dist`, and file hashes without downloading anything,
  for a fast dependency-drift check (e.g., "does published `requires_dist` match
  `pyproject.toml` dependencies right now") before doing the heavier wheel diff.
- **`build-and-inspect-python-package`** GitHub Action: good CI-time replacement for a manual
  build+lint step; produces the same reproducible build + `check-wheel-contents` combo as a
  reusable Action rather than hand-rolled shell.

## Recommended Approach

1. **Fix the `code/pyproject.toml` identity bug first** (name/version/description all wrong) —
   this blocks any meaningful "PyPI parity" audit until corrected, since right now the local
   build doesn't even produce a `model-checker`-named artifact.
2. **Nix**: extend the existing root `flake.nix` (don't introduce poetry2nix/uv2nix/dream2nix —
   no lockfile, one dependency, not the problem those tools solve) with a real
   `packages.<system>.default` using nixpkgs' native `buildPythonPackage { pyproject = true; }`
   against `python3Packages.z3` (already correctly used in both existing Nix files), add
   multi-system support (flake-utils or an explicit system list, replacing the hardcoded
   `x86_64-linux`), and wire a `checks` output that runs the pytest suite via `nix flake check`.
   Once the flake devShell folds in what `code/shell.nix` provides (plus the missing `networkx`),
   retire `code/shell.nix` per the project's "No Backwards Compatibility" principle rather than
   maintaining two drifting Nix entry points.
3. **Release workflow**: fix the `cd Code` → `cd code` casing bug, reconcile
   `RELEASE_SETUP.md`'s two-workflow description with the actual single `release.yml`, and
   migrate the publish job to PyPI Trusted Publishing (OIDC) behind a protected GitHub
   Environment, dropping the long-lived `PYPI_API_TOKEN` secret.
4. **Parity checks**: add a lightweight post-build CI (and ad hoc local, NixOS-safe) step
   combining `pip download --no-deps` + wheel content/hash diff + `check-wheel-contents`,
   informed by a cheap PyPI JSON API pre-check for dependency drift.

## Confidence Level

- Nix tool landscape and z3 bindings recommendation: **high** (directly verified nixpkgs
  attribute usage in this repo and a sibling repo; current PyPA/PyPI trusted-publishing guidance
  corroborated by both pypi.org and GitHub docs in search results).
- `pyproject.toml` name/version bug and `cd Code` casing bug: **high** (read directly from repo
  files, not inferred).
- `pip-wheel-diff` maturity/maintenance: **low** — flagged explicitly above, verify before
  depending on it.
- Everything else (best-practice recommendations, tool trade-off table): **medium-high**, based
  on 2026-current web search results plus direct repo inspection.

Sources:
- [Pyproject.nix — pyproject.toml use case](https://pyproject-nix.github.io/pyproject.nix/use-cases/pyproject.html)
- [Pyproject.nix — Builders](https://pyproject-nix.github.io/pyproject.nix/build.html)
- [nixpkgs python.section.md](https://github.com/NixOS/nixpkgs/blob/master/doc/languages-frameworks/python.section.md)
- [Packaging/Python — NixOS Wiki](https://wiki.nixos.org/wiki/Packaging/Python)
- [uv2nix Introduction](https://pyproject-nix.github.io/uv2nix/introduction.html)
- [poetry2nix — GitHub](https://github.com/nix-community/poetry2nix)
- [Uv2nix announcement — NixOS Discourse](https://discourse.nixos.org/t/uv2nix-build-develop-python-projects-using-uv-with-nix/58563)
- [Can't add dependency on Z3 python wrapper — NixOS Discourse](https://discourse.nixos.org/t/cant-add-dependency-on-z3-python-wrapper/1396)
- [z3-solver · PyPI](https://pypi.org/project/z3-solver/)
- [pypa/gh-action-pypi-publish](https://github.com/pypa/gh-action-pypi-publish)
- [PyPI Trusted Publishers — Security Model](https://docs.pypi.org/trusted-publishers/security-model/)
- [PyPI Trusted Publishers — Publishing with a Trusted Publisher](https://docs.pypi.org/trusted-publishers/using-a-publisher/)
- [GitHub Docs — Configuring OpenID Connect in PyPI](https://docs.github.com/en/actions/how-tos/secure-your-work/security-harden-deployments/oidc-in-pypi)
- [check-wheel-contents · PyPI](https://pypi.org/project/check-wheel-contents/)
- [pip-wheel-diff · PyPI](https://pypi.org/project/pip-wheel-diff/)
- [build-and-inspect-python-package — GitHub](https://github.com/brettcannon/build-and-inspect-python-package)
