# Implementation Plan: Make run_tests.py Exhaustive

## Task 67 | Session: sess_1774916194_468554

## Overview

Three gaps in test discovery leave 165 tests unreachable. All fixes are localized to `code/run_tests.py` discovery methods and the `PackageTestRunner.run_component_tests()` method.

## Phase 1: Remove Bimodal Exclusion [COMPLETED]

**File**: `code/run_tests.py`
**Method**: `_discover_theories()` (line 662)

Remove the hardcoded `item.name != 'bimodal'` filter so that the bimodal theory is discovered like any other theory with `tests/` and `examples.py`.

**Change**: Delete the line `item.name != 'bimodal' and  # Exclude bimodal theory (not finished)`.

## Phase 2: Make Subtheory Discovery Dynamic [COMPLETED]

**File**: `code/run_tests.py`
**Method**: `_discover_subtheories()` (line 691-696)

Replace the hardcoded subtheory list with filesystem-based discovery. This automatically includes `first_order` and any future subtheories.

**Change**: Scan `theory_lib/logos/subtheories/` for directories containing `tests/`.

Also add a filter pattern for `first_order` in `_run_logos_unit_tests()` (line 500-505) so that targeted subtheory filtering works.

## Phase 3: Support Nested Component Discovery [COMPLETED]

**File**: `code/run_tests.py`
**Methods**: `_discover_components()` (line 669) and `PackageTestRunner.run_component_tests()` (line 572)

Extend component discovery to find sub-components one level deep (e.g., `output.notebook`). Update `run_component_tests()` to resolve dotted component names to the correct test directory path.

## Phase 4: Add --list Flag [COMPLETED]

**File**: `code/run_tests.py`
**Functions**: `create_argument_parser()` and `main()`

Add a `--list` flag that prints discovered theories, subtheories, and components, then exits without running tests.

## Phase 5: Verification [COMPLETED]

Run `python run_tests.py --list` (or equivalent) to confirm bimodal, first_order, and output.notebook appear in discovery output.
