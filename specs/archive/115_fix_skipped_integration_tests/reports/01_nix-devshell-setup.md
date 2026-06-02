# Research Report: Fix Skipped Integration Tests

**Task**: 115 — Fix skipped integration tests via Nix devShell
**Date**: 2026-06-02

## Executive Summary

The 3 skipped tests do NOT require a full Nix devShell rebuild. The BimodalHarness
`protocol.py` and `registry.py` modules have zero heavy dependencies (no torch, numpy,
wandb, or datasets). Adding BimodalHarness's `src/` to `PYTHONPATH` is sufficient for
imports. Entry points are already registered via the existing `bimodal_logic.egg-info/entry_points.txt`
when `code/src` is on `PYTHONPATH`.

## Findings

### 1. BimodalHarness Import Analysis

The test file imports exactly 3 things from BimodalHarness:
- `bimodal_harness.oracle.protocol.OracleProvider` — pure Protocol class, only imports `typing`
- `bimodal_harness.oracle.registry.OracleRegistry` — imports `protocol` + stdlib only
- `bimodal_harness.oracle._mock.SPOT_CHECK_FORMULAS` — pure data, no heavy deps

The top-level `bimodal_harness/__init__.py` only sets `__version__`. The
`bimodal_harness/oracle/__init__.py` eagerly imports heavy modules (gateway, z3_provider, etc.)
BUT the tests import specific submodules directly, bypassing `__init__.py`.

**Verified**: All 3 imports succeed with just `PYTHONPATH` pointing to BimodalHarness `src/`.

### 2. Entry-Point Registration

The `code/src/bimodal_logic.egg-info/entry_points.txt` already contains:
```
[bimodal_harness.oracle_providers]
z3_base = bimodal_logic.provider:Z3OracleProvider
```

When `code/src` is on `PYTHONPATH`, `importlib.metadata` finds this `.egg-info` and
resolves the entry point. No pip install or Nix package build is needed.

### 3. Test Results with Combined PYTHONPATH

Running with `PYTHONPATH="/home/benjamin/Projects/BimodalHarness/src:code/src"`:
- **0 skipped** (all 108 tests run)
- **3 failed** (2 test bugs + 1 semantic issue)

### 4. Test Bugs Found

**Bug 1**: `test_oracle_registry_discover` and `test_discovered_provider_is_correct_type`
call `registry.list_providers()` which returns a list of **strings** (provider IDs), then
try to access `.provider_id` on those strings. Fix: use `registry.get(pid)` to retrieve
actual provider objects.

**Bug 2**: `test_enriched_vs_primitive_sat_agreement[next]` — SAT/UNSAT mismatch. The
enriched `next(A)` returns None (valid) while primitive `untl(A, bot)` finds a countermodel.
This indicates either: (a) the enriched `next` tag handler in the oracle doesn't correctly
expand to `untl(A, bot)`, or (b) the test formula needs a wrapper to ensure satisfiability
(like the `all_future`/`all_past` tests use `imp(all_future(A), B)`).

## Recommended Approach

### Phase 1: Fix PYTHONPATH in pytest config (no Nix needed)

Add BimodalHarness src to `pytest.ini_options.pythonpath` in `code/pyproject.toml`:
```toml
[tool.pytest.ini_options]
pythonpath = ["src", "/home/benjamin/Projects/BimodalHarness/src"]
```

**Problem**: Hardcoded absolute path is not portable.

**Better**: Use a `conftest.py` that conditionally adds the path, or use an environment
variable like `BIMODAL_HARNESS_SRC`.

**Best for Nix**: Create a minimal `flake.nix` with a devShell that sets `PYTHONPATH`
to include both source trees, plus provides pytest and z3. This is reproducible and
portable — other developers clone both repos and run `nix develop`.

### Phase 2: Remove pytest.skip() guards

Replace all `try/except ImportError: pytest.skip()` patterns with direct imports.
Tests fail hard if the environment is not configured correctly.

### Phase 3: Fix the 2 test bugs

1. Fix `list_providers()` usage — it returns strings, not objects
2. Fix the `next` enriched operator test — either fix the formula or the oracle handler

## Nix devShell Design

```nix
# flake.nix (minimal)
{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }: let
    system = "x86_64-linux";
    pkgs = nixpkgs.legacyPackages.${system};
    python = pkgs.python312;
  in {
    devShells.${system}.default = pkgs.mkShell {
      packages = [
        (python.withPackages (ps: with ps; [
          z3-solver
          pytest
          pytest-cov
        ]))
      ];
      shellHook = ''
        export PYTHONPATH="${toString ./code/src}:${toString ../BimodalHarness/src}:$PYTHONPATH"
      '';
    };
  };
}
```

**Portability**: The `../BimodalHarness` relative path assumes sibling checkout. Document
this in README. Alternative: use a flake input with `path:../BimodalHarness` (requires
the path to exist at eval time).

## Risks

1. **Relative path to BimodalHarness**: Fragile if repos are not siblings. Mitigated by
   documentation and optional env var override.
2. **egg-info freshness**: If `pyproject.toml` entry points change, `egg-info` must be
   regenerated (run `pip install -e .` in a venv or rebuild). The Nix approach avoids
   this by using PYTHONPATH directly.
