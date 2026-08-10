# Implementation Summary: Task #123

**Completed**: 2026-07-24
**Duration**: ~1 hour

## Overview

Rewrote the root `flake.nix` from a single-system (`x86_64-linux`-hardcoded), devShell-only flake
into a multi-system flake (`flake-utils.lib.eachDefaultSystem`) exposing `packages.default` (a
nixpkgs-native `buildPythonPackage` build rooted at `./code`), `devShells.default` (subsuming
`code/shell.nix`), and `checks.default` (a hermetic pytest gate scoped to the known-green
in-package bimodal suite). `code/shell.nix` was deleted with no backwards-compatibility layer.

## What Changed

- `flake.nix` — full rewrite: `flake-utils` input added, `eachDefaultSystem` scaffold replacing
  the hardcoded `system = "x86_64-linux"`; `description` updated to the restored `model-checker`
  identity; `packages.default` via `buildPythonPackage { pyproject = true; src = ./code; }` with
  `propagatedBuildInputs = [ python.pkgs.z3-solver python.pkgs.networkx ]` (the nixpkgs-native,
  source-built Z3 Python bindings — see Decisions) and `pythonRemoveDeps = [ "z3-solver" ]` +
  `pythonRelaxDepsHook` to drop the unsatisfiable PyPI `z3-solver` runtime-dep check;
  `devShells.default` with `z3`/`setuptools`/`pip`/`networkx`/`pytest`/`pytest-xdist` and a
  `shellHook` setting `PYTHONPATH` to `code/src`, with the sibling `../BimodalHarness/src` path
  strictly optional (no warning branch); `checks.default` running
  `pytest src/model_checker/theory_lib/bimodal/tests -n 6` inside a hermetic `stdenv.mkDerivation`,
  with an inline comment documenting the scope decision against the task-122 release baseline.
- `flake.lock` — regenerated to lock the new `flake-utils` (and its `systems`) input alongside the
  existing `nixpkgs` pin.
- `code/shell.nix` — deleted (fully subsumed by `devShells.default`; no compatibility shim per
  project policy).

## Decisions

- **`z3` attribute naming**: the plan referenced `python3Packages.z3` as "the nixpkgs-native Z3
  Python bindings, import name `z3`". In the currently-pinned nixpkgs revision
  (`331800de5053fcebacf6813adb5db9c9dca22a0c`, `nixos-unstable`), that attribute has been renamed
  to `python3Packages.z3-solver` — a naming collision with the PyPI wheel `code/pyproject.toml`
  declares, but functionally the same thing the plan intended: nixpkgs builds it from the
  `Z3Prover/z3` GitHub source (verified via `src.url`), installs a bare `z3/` module directory with
  no PyPI dist-info, and its `meta.description` confirms it as "High-performance theorem prover and
  SMT solver". Used `python.pkgs.z3-solver` (aliased to `nixZ3` in `flake.nix` with an inline
  comment) as this pin's correct spelling of the plan's intent.
- **`pythonRemoveDeps` over `pythonRelaxDeps`**: since nixpkgs' `z3-solver` derivation ships no
  dist-info under any name, `pythonRuntimeDepsCheckHook` cannot be satisfied by relaxing the
  version constraint alone (`pythonRelaxDeps` failed with `z3-solver not installed`); the
  requirement had to be stripped from the built wheel's metadata entirely via `pythonRemoveDeps`.
- **`checks.default` implementation**: used a plain `stdenv.mkDerivation` with `nativeBuildInputs`
  providing a `python.withPackages` closure and a `checkPhase` invoking pytest directly, rather than
  wrapping `buildPythonPackage`'s own `doCheck`/`pytestCheckHook` machinery — this keeps the check
  fully decoupled from the package build (matching the plan's "separate hermetic gate" framing) and
  avoids re-running package-build steps just to execute tests.

## Plan Deviations

- None (implementation followed plan; the `z3` vs `z3-solver` attribute-name difference from the
  plan's wording is a nixpkgs-pin naming detail, not a scope or approach deviation — the actual
  nixpkgs-native, source-built Z3 bindings intended by the plan are what's used).

## Verification

- Build: Success — `nix build .#default` produces a `result` symlink; `pythonImportsCheck =
  [ "model_checker" "z3" ]` passes.
- Tests: Passed — `nix flake check`: `286 passed in 42.56s`, `all checks passed!`, matching the
  task-122 `RELEASE-BASELINE.md` bimodal-suite baseline (286/286, 43.4s) almost exactly.
- Dev shell: Verified `nix develop -c python -c "import model_checker"` succeeds both with a real
  `../BimodalHarness` sibling present and with `BIMODAL_HARNESS_SRC` pointed at a nonexistent path
  (simulating a standalone checkout) — neither branch emits a warning. `pytest --version` and
  `import xdist` both succeed inside the shell.
- `nix flake show`: lists `packages.default`, `devShells.default`, `checks.default` for all 4
  default systems (`x86_64-linux`, `aarch64-linux`, `x86_64-darwin`, `aarch64-darwin`), confirming
  multi-system evaluation succeeds.
- Files verified: `code/shell.nix` no longer exists; `flake.lock` present, updated, staged.

## Notes

- Developers should now use `nix develop` in place of the deleted `code/shell.nix`
  (`nix-shell code/shell.nix`); this is a clean break per the project's no-backwards-compatibility
  policy.
- `checks.default` intentionally targets only the in-package `theory_lib/bimodal` suite
  (286/286 green per the task-122 baseline). The top-level `oracle/` tree (2656s, separate,
  unpackaged per task 118) and the "everything else" suite (28 documented pre-existing failures,
  unrelated to this task) are both out of scope for this hermetic reproducibility gate — see
  `specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/RELEASE-BASELINE.md`.
