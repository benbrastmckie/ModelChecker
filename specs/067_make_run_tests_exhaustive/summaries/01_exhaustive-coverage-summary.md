# Implementation Summary: Make run_tests.py Exhaustive

## Task 67 | Session: sess_1774916194_468554

## Changes Made

All changes in a single file: `code/run_tests.py`

### 1. Removed Bimodal Exclusion (Phase 1)

Removed the hardcoded `item.name != 'bimodal'` filter from `_discover_theories()`. The bimodal theory now appears in discovery alongside logos, making its 98 tests reachable.

### 2. Dynamic Subtheory Discovery (Phase 2)

Replaced the hardcoded 5-element subtheory list in `_discover_subtheories()` with filesystem-based scanning of `theory_lib/logos/subtheories/`. Any subdirectory containing a `tests/` directory is now automatically discovered. This adds `first_order` (53 tests) and will automatically pick up future subtheories.

Also added a `'first_order': '(first_order or FO_)'` filter pattern in `_run_logos_unit_tests()` so targeted subtheory filtering works for first_order tests.

### 3. Nested Component Discovery (Phase 3)

Extended `_discover_components()` to scan one level deeper within each top-level component directory, discovering sub-components with their own `tests/` directories. These are registered with dotted names (e.g., `output.notebook`).

Updated `PackageTestRunner.run_component_tests()` to resolve dotted component names by splitting on `.` and constructing the correct path (e.g., `output.notebook` -> `src/model_checker/output/notebook/tests/`). This makes the 14 notebook tests reachable.

### 4. Added --list Flag (Phase 4)

Added a `--list` argument to the CLI that prints all discovered theories, subtheories, and components, then exits without running tests. This provides a quick way to verify discovery.

## Verification

```
$ python run_tests.py --list
Discovered theories: bimodal, logos
Discovered components: builder, iterate, jupyter, models, output, output.notebook, settings, solver, syntactic, theory_lib, utils
Discovered subtheories (logos): constitutive, counterfactual, extensional, first_order, modal, relevance
```

All three gaps confirmed resolved:
- `bimodal` present in theories
- `first_order` present in subtheories
- `output.notebook` present in components

## Test Impact

| Gap | Tests Added | Status |
|-----|------------|--------|
| Bimodal theory | 98 | Discoverable |
| first_order subtheory | 53 | Discoverable |
| output/notebook | 14 | Discoverable |
| **Total** | **165** | **All reachable** |
