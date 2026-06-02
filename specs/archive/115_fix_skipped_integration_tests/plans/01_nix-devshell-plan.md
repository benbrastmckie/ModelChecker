# Implementation Plan: Fix Skipped Integration Tests

**Task**: 115
**Date**: 2026-06-02
**Complexity**: small (3 phases, ~1 hour)

## Overview

Fix 3 skipped tests and 2 test bugs in `test_oracle_interface.py` by:
1. Creating a `flake.nix` devShell that sets PYTHONPATH to include both source trees
2. Removing all `pytest.skip()` import guards
3. Fixing 2 test bugs (list_providers returns strings; next enriched operator mismatch)

## Dependency Wave

```
Phase 1 (flake.nix) → Phase 2 (remove skips) → Phase 3 (fix test bugs)
```

## Phase 1: Create flake.nix devShell [NOT STARTED]

Create a minimal `flake.nix` that provides a Python environment with z3-solver and pytest,
plus PYTHONPATH set to include both ModelChecker and BimodalHarness source trees.

- [ ] Create `flake.nix` at project root with:
  - nixpkgs input (nixos-unstable)
  - Python 3.12 with z3-solver, pytest, pytest-cov
  - `shellHook` that exports `PYTHONPATH` with `./code/src` and `../BimodalHarness/src`
  - `BIMODAL_HARNESS_SRC` env var override for non-sibling layouts
- [ ] Add `.envrc` with `use flake` for direnv integration
- [ ] Verify: `nix develop --command python3 -c "from bimodal_harness.oracle.protocol import OracleProvider; print('OK')"`
- [ ] Verify: `nix develop --command python3 -c "import importlib.metadata; eps = list(importlib.metadata.entry_points(group='bimodal_harness.oracle_providers')); assert len(eps) >= 1"`

## Phase 2: Remove pytest.skip() guards [NOT STARTED]

Replace all conditional import + skip patterns with direct imports at module level or
unconditional assertions.

- [ ] In `test_oracle_interface.py`, `TestOracleProtocolCompliance.test_provider_implements_protocol` (line ~494): Remove try/except, import `OracleProvider` at module top, assert isinstance directly
- [ ] In `TestEntryPointDiscovery.test_entry_point_registered` (line ~1138): Remove generic `except Exception: pytest.skip()`, let failures propagate
- [ ] In `TestEntryPointDiscovery.test_entry_point_loads_correct_class` (line ~1152): Remove `pytest.skip("z3_base entry point not found")` and `except Exception: pytest.skip()`
- [ ] In `TestEntryPointDiscovery.test_oracle_registry_discover` (line ~1169): Remove try/except ImportError pattern
- [ ] In `TestEntryPointDiscovery.test_discovered_provider_is_correct_type` (line ~1183): Remove try/except ImportError pattern
- [ ] Add top-of-file imports for `OracleProvider` and `OracleRegistry` from `bimodal_harness`
- [ ] Run tests with PYTHONPATH to verify no skips remain

## Phase 3: Fix test bugs [NOT STARTED]

### Bug 1: list_providers() returns strings, not objects

`OracleRegistry.list_providers()` returns `list[str]` (sorted provider IDs).
Tests on lines 1176 and 1190 call `.provider_id` on these strings.

- [ ] Fix `test_oracle_registry_discover` (line ~1176): Change `provider_ids = [p.provider_id for p in providers]` to just `provider_ids = providers` (already strings)
- [ ] Fix `test_discovered_provider_is_correct_type` (line ~1190): Change `z3_providers = [p for p in providers if p.provider_id == ...]` to use `registry.get("bmlogic_z3_base_v1")` instead

### Bug 2: next enriched operator SAT/UNSAT mismatch

`_next(A)` (enriched, `{"tag": "next", "arg": A}`) returns None (valid) while
`_untl(A, BOT)` (primitive) returns a countermodel (SAT). The enriched tag handler
may be treating `next` differently, or the bare formula `next(A)` / `untl(A, bot)` needs
a wrapper for satisfiability (like `all_future`/`all_past` use `imp(all_future(A), B)`).

- [ ] Investigate: run `find_countermodel` on both forms with debug output to understand the divergence
- [ ] Fix: either wrap in `imp(next(A), B)` / `imp(untl(A, bot), B)` for both forms (consistent with all_future/all_past pattern), or fix the enriched tag handler if it's genuinely wrong
- [ ] Verify the `prev` operator doesn't have the same issue (it passed — check why)

## Gate

```bash
nix develop --command bash -c 'PYTHONPATH="code/src:$PYTHONPATH" pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_interface.py -v'
```

Expected: 108 passed, 0 skipped, 0 failed.
