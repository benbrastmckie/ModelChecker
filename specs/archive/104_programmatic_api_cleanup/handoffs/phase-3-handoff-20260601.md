# Phase 3 Handoff: Remove other dead code

**Phase**: 3 of 5
**Status**: COMPLETED
**Timestamp**: 2026-06-01

## What Was Done

- Deleted `code/src/model_checker/cli.py` (debug artifact with unconditional print() calls)
- Deleted `code/src/model_checker/theory_lib/bimodal/profile_abundance.py` (profiling script, not imported)
- Deleted `code/src/model_checker/theory_lib/bimodal/tests/e2e/test_cli_execution.py` (tested old multi-theory CLI)
- Cleaned up `__main__.py`: removed unreachable logos --subtheory block (lines 303-313), updated epilog example from "-l logos" to "-l bimodal"

## Verification

- All smoke tests pass (model_checker, output, oracle)
- 118 bimodal unit tests pass (fold_unfold, frame_constraints, witness_registry)
- __main__.py still present but will fail at runtime (expected, builder/ deleted)

## State for Phase 4

- No more CLI-only dead code
- bimodal_logic package has no CLI entry point yet
- Next: create bimodal_logic/cli.py (TDD: tests first), add pyproject.toml entry point
