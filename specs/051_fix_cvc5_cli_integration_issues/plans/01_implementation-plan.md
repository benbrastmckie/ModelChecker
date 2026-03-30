# Implementation Plan: Task #51

- **Task**: 51 - fix_cvc5_cli_integration_issues
- **Status**: [IMPLEMENTING]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/051_fix_cvc5_cli_integration_issues/reports/01_team-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

This plan addresses three cvc5 CLI integration issues: (1) spurious "Flag doesn't correspond to any known setting" warnings for z3/cvc5/subtheory flags, (2) hardcoded "Z3 Run Time" label in user output that should be backend-neutral, and (3) documentation updates for the solver backend selection feature. The research report confirms these are straightforward fixes with no test breakage expected.

### Research Integration

Key findings from team research (01_team-research.md):
- Root cause identified: `z3`, `cvc5`, and `subtheory` flags missing from `standard_args` set in settings.py line 233
- Hardcoded label at structure.py line 840 (`_print_runtime_footer`) and line 505 (template string)
- `get_active_backend()` from registry.py already available for backend detection
- No tests assert the literal "Z3 Run Time" string - safe to change
- Recommendation: Use neutral "Solver Run Time" label (simpler, future-proof)

## Goals & Non-Goals

**Goals**:
- Eliminate spurious CLI warning for z3/cvc5/subtheory flags
- Make runtime footer label backend-neutral
- Update template string for generated test files
- Update docstring to match new behavior
- Document solver backend selection in appropriate README files
- Ensure documentation is complete but not redundant

**Non-Goals**:
- Changing internal attribute names (z3_model_runtime, z3_model_status) - these are implementation details
- Making low-priority error messages backend-aware (builder/example.py, iterate/models.py) - future work
- Over-representing the cvc5 feature in documentation

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Breaking existing tests | Medium | Low | Research confirms no tests assert "Z3 Run Time" literal |
| Missing other hardcoded Z3 references | Low | Low | Comprehensive audit completed in research |
| Documentation becoming redundant | Low | Medium | Carefully review existing docs before adding content |

## Implementation Phases

### Phase 1: Fix standard_args in settings.py [COMPLETED]

**Goal**: Eliminate spurious warning for z3/cvc5/subtheory CLI flags

**Tasks**:
- [ ] Open `code/src/model_checker/settings/settings.py`
- [ ] Locate `standard_args` set definition (line 233)
- [ ] Add `'z3'`, `'cvc5'`, and `'subtheory'` to the set
- [ ] Verify no other CLI flags are missing from standard_args

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/settings/settings.py` - Add missing flags to standard_args

**Verification**:
- Run `model-checker --cvc5 examples/test.py` and confirm no warning appears
- Run `model-checker --z3 examples/test.py` and confirm no warning appears

---

### Phase 2: Update runtime footer label [COMPLETED]

**Goal**: Make runtime footer backend-neutral

**Tasks**:
- [ ] Open `code/src/model_checker/models/structure.py`
- [ ] Locate `_print_runtime_footer` method (line 838-840)
- [ ] Update docstring from "Print Z3 runtime" to "Print solver runtime"
- [ ] Change label from `"Z3 Run Time:"` to `"Solver Run Time:"`
- [ ] Locate template string (line 505)
- [ ] Change `Z3 run time:` to `Solver run time:` in template

**Timing**: 20 minutes

**Files to modify**:
- `code/src/model_checker/models/structure.py` - Update label and docstring

**Verification**:
- Run model checker and verify output shows "Solver Run Time" instead of "Z3 Run Time"
- Verify with both `--z3` and `--cvc5` flags

---

### Phase 3: Update Settings README documentation [COMPLETED]

**Goal**: Document solver backend selection in settings README

**Tasks**:
- [ ] Open `code/src/model_checker/settings/README.md`
- [ ] Add solver backend selection to "Available Command-Line Flags" section
- [ ] Add `--z3` and `--cvc5` flags under "Solver Backend Selection" subsection
- [ ] Cross-reference the solver/ README for detailed backend information
- [ ] Keep documentation concise - avoid duplicating solver/ README content

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/settings/README.md` - Add backend selection flags

**Verification**:
- Review that flags are documented consistently with other CLI flags
- Verify cross-reference to solver/ README is clear

---

### Phase 4: Update Solver README documentation [COMPLETED]

**Goal**: Ensure solver README has complete backend selection documentation

**Tasks**:
- [ ] Open `code/src/model_checker/solver/README.md`
- [ ] Review existing "Backend Selection" section for completeness
- [ ] Add `--subtheory` flag documentation if relevant to solver selection
- [ ] Ensure CLI flag examples are consistent with settings README
- [ ] Add any missing edge cases or common usage patterns
- [ ] Verify no redundancy with settings README

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/solver/README.md` - Update if needed

**Verification**:
- Review that backend selection documentation is complete
- Verify examples work as documented

---

### Phase 5: Run tests and final verification [COMPLETED]

**Goal**: Ensure all changes work correctly and no regressions

**Tasks**:
- [ ] Run full test suite: `pytest code/src/model_checker/`
- [ ] Run settings-specific tests: `pytest code/src/model_checker/settings/tests/`
- [ ] Run solver-specific tests: `pytest code/src/model_checker/solver/tests/`
- [ ] Test CLI with `--z3` flag end-to-end
- [ ] Test CLI with `--cvc5` flag end-to-end (if cvc5 installed)
- [ ] Verify no warnings appear for z3/cvc5/subtheory flags
- [ ] Verify runtime label shows "Solver Run Time"

**Timing**: 30 minutes

**Files to modify**:
- None (verification only)

**Verification**:
- All tests pass
- CLI flags work without warnings
- Output label is correct

## Testing & Validation

- [ ] Run `pytest code/src/model_checker/settings/tests/` - Settings tests
- [ ] Run `pytest code/src/model_checker/solver/tests/` - Solver tests
- [ ] Run `pytest code/src/model_checker/models/tests/` - Model tests
- [ ] Run `model-checker --cvc5 examples/modal.py` - No warning, correct output
- [ ] Run `model-checker --z3 examples/modal.py` - No warning, correct output
- [ ] Verify "Solver Run Time:" appears in output

## Artifacts & Outputs

- `code/src/model_checker/settings/settings.py` - Updated standard_args
- `code/src/model_checker/models/structure.py` - Updated labels
- `code/src/model_checker/settings/README.md` - Updated documentation
- `code/src/model_checker/solver/README.md` - Updated documentation (if needed)
- `specs/051_fix_cvc5_cli_integration_issues/summaries/01_execution-summary.md` - Implementation summary

## Rollback/Contingency

If changes cause unexpected test failures:
1. Revert changes to settings.py and structure.py
2. Use `git checkout -- code/src/model_checker/settings/settings.py code/src/model_checker/models/structure.py`
3. Investigate test failures before re-applying fixes
4. Documentation changes are low-risk and unlikely to require rollback
