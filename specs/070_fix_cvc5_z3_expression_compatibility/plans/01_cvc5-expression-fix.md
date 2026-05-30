# Implementation Plan: Fix cvc5 "Z3 expression expected" Compatibility Errors

- **Task**: 70 - Fix cvc5 "Z3 expression expected" compatibility errors
- **Status**: [IMPLEMENTING]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/070_fix_cvc5_z3_expression_compatibility/reports/01_cvc5-expression-errors.md
- **Artifacts**: plans/01_cvc5-expression-fix.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-formats.md, tasks.md
- **Type**: z3

## Overview

Fix the static binding issue in `semantic.py` that causes cvc5 compatibility errors. The `simplify` function is imported from `z3_shim` at module load time, binding to z3's implementation. When the backend switches to cvc5, this static binding persists, causing z3's simplify to receive cvc5 expressions. The fix uses the established dynamic lookup pattern (`z3.simplify()`) already present elsewhere in the file.

### Research Integration

- Root cause: Line 13 `from model_checker.z3_shim import simplify` creates static binding
- Problem location: Line 539 `simplify(bit_a | bit_b)` uses static binding
- Working pattern: Lines 1320 and 1524 use `z3.simplify()` with dynamic lookup
- Affected examples: 13 total (EXT_CM_2, MOD_CM_3, MOD_CM_4, CL_CM_4-14)

## Goals & Non-Goals

**Goals**:
- Fix all cvc5 "Z3 expression expected" errors in comparison.py examples
- Maintain z3 backward compatibility
- Follow established dynamic lookup pattern

**Non-Goals**:
- Refactoring other static imports (audit only)
- Performance optimization
- Adding new tests (existing comparison.py serves as validation)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Regression in z3 mode | H | L | Pattern already used in same file; run comparison.py with z3 |
| Other static imports exist | M | L | Audit during Phase 1; research found no others affecting cvc5 |

## Implementation Phases

### Phase 1: Apply Fix [COMPLETED]

**Goal**: Remove static import and update usage to dynamic lookup

**Tasks**:
- [ ] Remove line 13: `from model_checker.z3_shim import simplify`
- [ ] Change line 539 from `simplify(bit_a | bit_b)` to `z3.simplify(bit_a | bit_b)`
- [ ] Verify no other usages of the static `simplify` import exist

**Timing**: 10 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/semantic.py` - Remove static import, update usage

**Verification**:
- Run `grep -n "^simplify\|[^z3\.]simplify(" semantic.py` to confirm no other static usages

---

### Phase 2: Verify Fix [COMPLETED]

**Goal**: Confirm all affected examples now pass with cvc5 backend

**Tasks**:
- [ ] Run comparison.py with cvc5 backend
- [ ] Verify EXT_CM_2 passes
- [ ] Verify MOD_CM_3, MOD_CM_4 pass
- [ ] Verify CL_CM_4 through CL_CM_14 pass
- [ ] Run comparison.py with z3 backend (regression test)

**Timing**: 15 minutes

**Verification**:
- All 13 previously failing examples pass with cvc5
- All examples continue to pass with z3

## Testing & Validation

- [ ] Run `python comparison.py -s cvc5` and verify no "Z3 expression expected" errors
- [ ] Run `python comparison.py -s z3` and verify no regressions
- [ ] Optionally run the full test suite with both backends

## Artifacts & Outputs

- plans/01_cvc5-expression-fix.md (this file)
- summaries/01_cvc5-expression-fix-summary.md (after implementation)

## Rollback/Contingency

If the fix causes unexpected issues:
1. Restore line 13: `from model_checker.z3_shim import simplify`
2. Restore line 539: `simplify(bit_a | bit_b)`
3. Investigate alternative approach (e.g., using `solver.expressions.simplify`)
