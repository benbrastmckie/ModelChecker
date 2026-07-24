# Implementation Plan: Nix Flake Multi-System Rewrite

- **Task**: 123 - rewrite_the_nix_flake_for_multisystem_build_and_te
- **Status**: [COMPLETED]
- **Effort**: 2.5 hours
- **Dependencies**: Green test gate established (task 122 RELEASE-BASELINE.md); final package identity in `code/pyproject.toml` (task 121)
- **Research Inputs**: specs/117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md; parent plan phase 11 (specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md)
- **Artifacts**: plans/01_nix-flake-multisystem-rewrite.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-format-enforcement.md
- **Type**: nix

## Overview

Rewrite the root `flake.nix` from a single-system (`x86_64-linux`-hardcoded), devShell-only flake
into a multi-system flake that exposes a nixpkgs-native `packages.default` build, a `checks.default`
pytest gate, and a `devShell` that subsumes the legacy `code/shell.nix`. The Python package lives
under `code/` (its `pyproject.toml` and `src/` are one directory below the flake at repo root), so
the build derivation must root at `./code`. Per phase 11 the package is built against
`python3Packages.z3` (the nixpkgs-native Z3 Python bindings, import name `z3`) rather than the PyPI
`z3-solver` wheel `pyproject.toml` declares, and `networkx` is included. Definition of done: `nix
build` and `nix flake check` both succeed locally against a multi-system flake, `flake.lock` is
committed, and `code/shell.nix` is deleted with no backwards-compatibility layer.

### Research Integration

The spawn analysis (`reports/02_spawn-analysis.md`, New Task 6) confirms this task covers plan
phase 11 only, is gated on the task-122 green gate (now satisfied), and is independent of the
documentation task (New Task 7). The task-122 `RELEASE-BASELINE.md` is the authoritative source
for what "green" means and directly shapes the `checks.default` scope decision (see Risks): the
FULL suite carries 28 documented pre-existing failures plus xdist CPU-contention flakes at
`-n auto`, so the flake check must target a reliably-green scope at `-n 6`, not the entire tree.

### Prior Plan Reference

No prior plan for task 123. The parent plan phase 11 (task 117) is the authoritative requirements
reference and is treated as such, not copied.

### Roadmap Alignment

No `roadmap_flag` set for this dispatch; no ROADMAP.md phases added. This task advances the parent
task-117 release effort's infrastructure/reproducibility milestone (phase 11 of its plan).

## Goals & Non-Goals

**Goals**:
- Multi-system `flake.nix` (flake-utils `eachDefaultSystem` or explicit system list) replacing the
  hardcoded `x86_64-linux`.
- `packages.default` via nixpkgs-native `buildPythonPackage { pyproject = true; }`, source rooted at
  `./code`, built against `python3Packages.z3` (not the PyPI `z3-solver` wheel) with `networkx`.
- `checks.default` running a known-green pytest scope so `nix flake check` is a real reproducibility
  gate rather than a rediscovery of pre-existing failures.
- A `devShell` that subsumes `code/shell.nix` (z3, setuptools, pip, networkx, pytest, pytest-xdist),
  with the `../BimodalHarness` sibling path strictly optional and no failure/warning path in a
  standalone checkout.
- Committed `flake.lock`; deleted `code/shell.nix`.
- Verified `nix build` and `nix flake check` locally.

**Non-Goals**:
- No changes to `code/pyproject.toml`, `code/MANIFEST.in`, or package identity (owned by task 121/124).
- No fixing of the 28 documented pre-existing "rest" suite failures (out of scope; owned by a
  separate follow-up per the baseline).
- No CI/release-workflow edits (`.github/`), documentation, or PyPI work (phases 12-13, other tasks).
- No packaging of the `oracle/` tree (intentionally unpacked/PYTHONPATH-only per task 118).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `buildPythonPackage` fails runtime-dep check because `pyproject.toml` pins `z3-solver` but the Nix env provides `python3Packages.z3` (import name `z3`, no `z3-solver` dist) | H | H | Use `pythonRelaxDeps = [ "z3-solver" ]` / `pythonRemoveDeps` (or `dontCheckRuntimeDeps = true`) plus `nativeBuildInputs = [ pythonRelaxDepsHook ]`; supply `python3Packages.z3` in `propagatedBuildInputs`. Confirm `import z3` works in the built output. |
| Flake at repo root but package under `code/` — wrong `src` root breaks the build | H | M | Set the derivation `src = ./code;` (or `./.` with `pyproject.toml` path pointing into `code/`); verify `pyproject = true;` locates `code/pyproject.toml` and `code/src`. |
| `checks.default` run against the full suite fails on the 28 documented pre-existing failures / xdist contention flakes, making `nix flake check` permanently red | H | H | Scope the check to the reliably-green in-package `theory_lib/bimodal` suite (286/286 green per baseline) at `-n 6`; explicitly exclude the `oracle/` tree (2656s, separate) and, if a wider scope is chosen, deselect the baseline's documented failures. Document the scope decision inline in `flake.nix`. |
| Sandboxed Nix check has no network / long Z3 wall-clock exceeds builder limits | M | M | Prefer the fast in-package bimodal scope; keep the check hermetic (all deps from nixpkgs, no PyPI fetch); avoid the multi-hour oracle suite in the check. |
| Multi-system evaluation references Linux-only or unfree attrs, breaking `nix flake check` on other systems | M | L | Keep the derivation system-agnostic via `flake-utils.lib.eachDefaultSystem`; only reference portable nixpkgs Python attrs. |
| `code/shell.nix` deletion breaks a developer's muscle-memory workflow | L | M | The new `devShell` fully subsumes it; document `nix develop` as the replacement in the plan/summary; clean break per no-backwards-compat policy. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel in principle; here Phases 2 and 3 both edit the
single `flake.nix` file, so a single implementer serializes them on that file (the wave grouping
reflects their shared logical dependency on Phase 1, not independent file ownership).

### Phase 1: Multi-System Scaffold and `packages.default` [COMPLETED]

- **Goal:** Replace the hardcoded-system devShell-only flake with a multi-system scaffold exposing a
  working nixpkgs-native package build rooted at `./code`.
- **Tasks:**
  - [x] Add a `flake-utils` input (or an explicit `systems` list) and wrap outputs in
        `eachDefaultSystem`, removing the hardcoded `system = "x86_64-linux"`. *(completed)*
  - [x] Update the stale `description` (currently "Z3-based bimodal logic oracle") to reflect the
        restored `model-checker` package identity. *(completed)*
  - [x] Define `packages.default` = `python3Packages.buildPythonPackage { pyproject = true; src = ./code; ... }`. *(completed)*
  - [x] Wire `propagatedBuildInputs = [ python3Packages.z3 python3Packages.networkx ]` (NOT the PyPI
        `z3-solver` wheel). *(completed: current nixpkgs pin exposes the nixpkgs-native build under
        the attribute name `python3Packages.z3-solver`, not `z3`, per-file comment in flake.nix
        documents the naming collision — it is still the source-built nixpkgs derivation, not the
        PyPI wheel)*
  - [x] Relax/remove the `z3-solver` runtime-dep constraint (`pythonRelaxDepsHook` +
        `pythonRelaxDeps`/`pythonRemoveDeps`, or `dontCheckRuntimeDeps`) so the build accepts the
        nixpkgs `z3` bindings in place of the pinned `z3-solver`. *(completed: `pythonRemoveDeps`
        required — `pythonRelaxDeps` alone left `pythonRuntimeDepsCheckHook` failing since nixpkgs'
        z3-solver build ships no dist-info under any name)*
  - [x] Run `nix build .#default` (or `nix build`) and confirm the result contains an importable
        `model_checker` package with `import z3` working. *(completed: build succeeds,
        `pythonImportsCheck = [ "model_checker" "z3" ]` passes)*
- **Timing:** 1 hour
- **Depends on:** none
- **Files to modify:**
  - `flake.nix` - full rewrite of inputs/outputs; add multi-system scaffold and `packages.default`.
- **Verification:**
  - `nix build` exits 0 and produces a `result` symlink.
  - `nix run nixpkgs#...` not needed; instead `result/bin/model-checker --help` (or a Python
    `-c "import model_checker, z3"` against the built env) succeeds.

### Phase 2: Dev Shell Subsuming `code/shell.nix` [COMPLETED]

- **Goal:** Provide a `devShell` that fully replaces `code/shell.nix` with the `../BimodalHarness`
  path strictly optional.
- **Tasks:**
  - [x] Define `devShells.default` = `mkShell` including a Python env with `z3`, `setuptools`, `pip`,
        `networkx`, `pytest`, and `pytest-xdist`. *(completed)*
  - [x] Set `PYTHONPATH` to `code/src` in the `shellHook` (matching the package's `package-dir`). *(completed)*
  - [x] Make the sibling `../BimodalHarness/src` path strictly optional: add it to `PYTHONPATH` only
        when present, with NO warning/failure branch for a standalone checkout (drop the current
        `shell.nix`/`flake.nix` WARNING path). *(completed: verified both branches emit no warning)*
  - [x] Preserve any still-relevant convenience from `code/shell.nix` (dev CLI usability) without
        re-introducing a backwards-compat shim. *(completed: setuptools/pip retained for pkg_resources
        parity; `code/shell.nix`'s script-chmod/PATH additions were dev-CLI-specific niceties not
        needed once `model-checker` is a proper installed console-script entry point)*
- **Timing:** 0.5 hours
- **Depends on:** 1
- **Files to modify:**
  - `flake.nix` - add `devShells.default` within the `eachDefaultSystem` scaffold.
- **Verification:**
  - `nix develop -c python -c "import model_checker"` succeeds in a standalone checkout (no
    BimodalHarness present) with no warning emitted.
  - `nix develop -c pytest --version` and `python -c "import pytest_xdist"`-equivalent (`pytest -p xdist --help`) succeed.

### Phase 3: `checks.default` Green Gate [COMPLETED]

- **Goal:** Add a hermetic `checks.default` that runs a known-green pytest scope so `nix flake check`
  is a real reproducibility gate.
- **Tasks:**
  - [ ] Define `checks.default` running pytest over the reliably-green in-package
        `theory_lib/bimodal` suite (286/286 green per task-122 baseline) with `-n 6` (avoid `-n auto`
        contention flakes documented in the baseline). *(completed)*
  - [x] Explicitly exclude the `oracle/` tree from the check (separate 2656s suite, not part of the
        shipped package). *(completed: checkPhase's pytest invocation targets only
        `src/model_checker/theory_lib/bimodal/tests`, `oracle/` is never referenced)*
  - [x] Add an inline comment in `flake.nix` documenting the scope decision and citing the task-122
        green baseline as the rationale (why the check is scoped rather than whole-tree). *(completed)*
  - [x] Ensure the check is hermetic: all Python deps from nixpkgs, no PyPI/network fetch inside the
        Nix sandbox. *(completed: devPython is a pure nixpkgs python.withPackages closure, no pip
        install step in checkPhase)*
  - [x] Run `nix flake check` and confirm the check passes. *(completed: "all checks passed!",
        286 passed in 42.30s, matching the task-122 baseline's 286/286 in 43.4s)*
- **Timing:** 0.5 hours
- **Depends on:** 1
- **Files to modify:**
  - `flake.nix` - add `checks.default` within the `eachDefaultSystem` scaffold.
- **Verification:**
  - `nix flake check` exits 0.
  - The check's pytest scope matches a green subset of the task-122 baseline (no reliance on the 28
    documented pre-existing failures being absent).

### Phase 4: Retire `shell.nix`, Commit `flake.lock`, Final Verification [COMPLETED]

- **Goal:** Remove the legacy dev shell, lock and commit inputs, and verify the full multi-system
  flake end to end.
- **Tasks:**
  - [x] Delete `code/shell.nix` (no backwards-compat layer, per project policy). *(completed)*
  - [x] Regenerate `flake.lock` (`nix flake lock`) so it reflects the new inputs (e.g. `flake-utils`);
        stage it for commit. *(completed: flake.lock already reflected flake-utils/systems from
        Phase 1's build; `nix flake lock` confirmed idempotent)*
  - [x] Run `nix build` and `nix flake check` a final time to confirm both succeed against the
        committed lock. *(completed: build succeeds; check reports 286 passed in 42.56s, all checks
        passed)*
  - [x] Confirm `nix flake show` lists `packages.default`, `devShells.default`, and `checks.default`
        for the default systems. *(completed: all three listed for all 4 default systems)*
- **Timing:** 0.5 hours
- **Depends on:** 2, 3
- **Files to modify:**
  - `code/shell.nix` - delete.
  - `flake.lock` - regenerate and commit.
  - `flake.nix` - final consistency pass if needed.
- **Verification:**
  - `code/shell.nix` no longer exists.
  - `flake.lock` is present, updated, and committed.
  - `nix build` and `nix flake check` both exit 0.

## Testing & Validation

- [x] `nix build` succeeds and the built output exposes an importable `model_checker` with a working
      `import z3` (nixpkgs `python3Packages.z3`, not `z3-solver`). *(completed: current nixpkgs pin
      exposes this as attribute `python3Packages.z3-solver`, see Phase 1 note)*
- [x] `nix flake check` exits 0 with the scoped, known-green pytest check. *(completed: 286 passed
      in 42.56s)*
- [x] `nix develop` enters a shell with `pytest`/`pytest-xdist`/`networkx`/`z3` available and
      `import model_checker` working, in a standalone checkout with no BimodalHarness present and no
      warning emitted. *(completed, verified both with and without a BimodalHarness sibling)*
- [x] `nix flake show` lists `packages.default`, `devShells.default`, `checks.default` for the
      default systems (multi-system evaluation succeeds). *(completed)*
- [x] `code/shell.nix` is deleted; `flake.lock` is committed. *(completed)*

## Artifacts & Outputs

- plans/01_nix-flake-multisystem-rewrite.md (this file)
- summaries/01_nix-flake-multisystem-rewrite-summary.md (on completion)
- Rewritten `flake.nix` (multi-system, `packages.default` + `devShells.default` + `checks.default`).
- Regenerated and committed `flake.lock`.
- Deleted `code/shell.nix`.

## Rollback/Contingency

- All work occurs on the existing task branch; the flake rewrite touches only `flake.nix`,
  `flake.lock`, and deletes `code/shell.nix`, so `git revert` of this task's commits fully restores
  the prior single-system flake and `code/shell.nix` without affecting restored source modules.
- If the nixpkgs-native `python3Packages.z3` build proves intractable within budget (e.g. an
  unresolvable dependency-check conflict), fall back to keeping `packages.default` building against
  the pinned `z3-solver` via an override while still delivering the multi-system scaffold,
  `devShell`, and `checks.default`; document the deviation in the summary. This is a fallback, not
  the plan.
- If `nix flake check` cannot be made green within the Nix sandbox's wall-clock/network limits even
  at the in-package bimodal scope, narrow the check to a fast collection-only or smoke subset and
  record the limitation, rather than shipping a permanently-red check.
