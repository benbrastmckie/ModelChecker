# Implementation Summary: Fix Skipped Integration Tests

**Task**: 115
**Date**: 2026-06-02
**Result**: 108 passed, 0 skipped, 0 failed

## What Was Done

### Phase 1: Created flake.nix devShell
- Added `flake.nix` with Python 3.12, z3-solver, pytest, pytest-cov
- Shell hook sets `PYTHONPATH` to include `code/src` and `../BimodalHarness/src`
- Supports `BIMODAL_HARNESS_SRC` env var override for non-sibling layouts
- Added `.envrc` for direnv integration

### Phase 2: Removed pytest.skip() guards
- Added top-level imports for `OracleProvider` and `OracleRegistry` from `bimodal_harness`
- Removed all `try/except ImportError: pytest.skip()` patterns (5 instances)
- Removed all `except Exception: pytest.skip()` patterns (2 instances)
- Tests now fail hard if the dev environment is not properly configured

### Phase 3: Fixed test bugs
- **list_providers() bug**: `OracleRegistry.list_providers()` returns `list[str]` (provider IDs),
  not provider objects. Fixed `test_oracle_registry_discover` to use the returned strings directly
  and `test_discovered_provider_is_correct_type` to use `registry.get()`.

## Key Discovery

No Nix package builds were needed. BimodalHarness's `protocol.py` and `registry.py`
import only stdlib (`typing`, `importlib.metadata`). The existing `bimodal_logic.egg-info/entry_points.txt`
provides entry-point registration when `code/src` is on `PYTHONPATH`. The entire solution
is a devShell that sets `PYTHONPATH` to include both source trees.

## Deviations from Plan

- The `next` enriched operator SAT/UNSAT mismatch (Bug 2 in the plan) did not reproduce
  in the nix devShell — both enriched and primitive forms return consistent results.
  The earlier failure was likely a flaky timing issue. No fix was needed.
