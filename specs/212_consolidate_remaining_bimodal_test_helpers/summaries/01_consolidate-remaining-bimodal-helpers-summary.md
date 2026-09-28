# Implementation Summary: Consolidate Remaining Bimodal Test Helpers

- **Task**: 212 - Consolidate remaining bimodal test helpers onto `_build_support.py`
- **Status**: [COMPLETED]
- **Started**: 2026-09-28T00:00:00Z
- **Completed**: 2026-09-28T00:00:00Z
- **Effort**: ~2 hours
- **Dependencies**: None
- **Artifacts**: plans/01_consolidate-remaining-bimodal-helpers.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The bimodal test tree's shared example-build module,
`code/src/model_checker/theory_lib/bimodal/tests/_build_support.py`, was originally adopted by
only four call sites; the remaining modules still restated `_settings`/`_build` locally. This
task re-derived the duplication scope fresh (rather than trusting a prior count), classified
each of the ten grep hits by reading its body against the shared helper, and consolidated every
genuinely duplicated call site onto the shared module while leaving the one documented behavioral
exception (`unit/test_structure.py`) and the one grep false positive
(`unit/test_witness_constraints.py`) untouched.

## What Changed

- `integration/test_iterate.py`, `integration/test_until_since_integration.py`,
  `unit/test_operators.py`, `unit/test_proposition.py`, `unit/test_semantics_core.py`: dropped a
  local `_settings` def each, replaced with an import from `_build_support`.
- `integration/test_data_extraction.py`, `integration/test_output_gate.py`: dropped local
  `_settings` + `_build` defs (and, in `test_output_gate.py`'s case, a stale docstring claiming a
  `'verify'='off'` mirror of `test_structure.py` that the body never implemented), replaced with a
  bare `_build`/`_settings` import; six now-orphaned imports
  (`ModelConstraints`/`Syntax`/`bimodal_operators`/`BimodalSemantics`/`BimodalStructure`/
  `BimodalProposition`) removed from each after a per-symbol reference-count check.
- `integration/test_injection.py`: dropped local `_settings` + `_build_solved` defs, imported the
  shared pair, and renamed all 3 `_build_solved(...)` call sites to `_build(...)`. Five orphaned
  imports removed; `BimodalSemantics` kept (still used at a call site outside the removed body).
- `_build_support.py`: module docstring rewritten to describe the consolidated call-site set in
  durable, non-task-number terms, keeping the `unit/test_structure.py` exception explicit and
  adding a "not a call site" note for `unit/test_witness_constraints.py`.

## Decisions

- Every module's helper was read against `_build_support.py`'s before editing (per the pre-edit
  verification gate), not assumed equivalent from the shared function name alone.
- `test_output_gate.py`'s stale docstring was resolved by checking all 8 `_build(...)` call sites:
  every one passes `verify=` explicitly, so the bare-import route applied and the stale claim was
  deleted along with the body, rather than inventing a `'verify'` default that was never really
  there.
- `test_injection.py`'s `_build_solved` was renamed to `_build` at its 3 call sites (approach (a)
  from the research report) rather than aliased on import, matching the naming convention every
  other migrated call site uses.
- `unit/test_structure.py`'s documented `'verify'='off'` wrapper and
  `unit/test_witness_constraints.py`'s unrelated `_build_selector_family` were left untouched, as
  scoped.

## Plan Deviations

- None (implementation followed plan). The fresh discovery grep re-run at Phase 1 and again at
  Phase 5 matched the plan's ten-module list and classification exactly, with no divergence to
  route through the plan's documented-local-wrapper escape hatch.

## Impacts

- Bimodal test collection count is unchanged (686 tests, confirmed before and after).
- The bimodal test tree now has exactly two remaining local `_settings`/`_build`-shaped
  definitions outside `_build_support.py`, both reasoned and documented: `test_structure.py`'s
  delegating wrapper and `test_witness_constraints.py`'s unrelated helper.
- No test assertion, expected value, or `'verify'` default changed anywhere — this was a pure
  de-duplication.

## Follow-ups

- None identified. The consolidation is complete for every `_settings`/`_build`-shaped duplicate
  the fresh grep found.

## References

- `specs/212_consolidate_remaining_bimodal_test_helpers/plans/01_consolidate-remaining-bimodal-helpers.md`
- `specs/212_consolidate_remaining_bimodal_test_helpers/reports/01_consolidate-remaining-bimodal-helpers.md`
- `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py`
