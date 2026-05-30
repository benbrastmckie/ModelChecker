# Implementation Plan: Task #72

- **Task**: 72 - Fix CVC5 constraint compatibility with Z3 expression types
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_cvc5-z3-compatibility.md
- **Artifacts**: plans/01_cvc5-expression-conversion.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3

## Overview

The CVC5 solver adapter receives Z3 expressions (z3.BoolRef, z3.BitVecRef) from the constraint building pipeline but cannot process them directly. The fix implements expression reconstruction in the CVC5 adapter that converts Z3 expression trees to equivalent CVC5 expressions at the solver boundary. This approach is localized to the adapter layer and transparent to the rest of the codebase.

### Research Integration

Key findings from the research report:
- Z3 and CVC5 expressions are type-incompatible (different Python objects)
- Expression reconstruction is the recommended approach (Option A)
- Four expression categories need conversion: Boolean, BitVector, Functions, Quantifiers
- Performance overhead is acceptable since conversion happens at solver add time

## Goals & Non-Goals

**Goals**:
- Convert Z3 expressions to CVC5 expressions transparently in the adapter
- Support all expression types used by the model checker (And, Or, Not, Implies, BitVec, ForAll, Exists, Functions)
- Maintain existing API compatibility
- Add comprehensive test coverage

**Non-Goals**:
- Modifying the constraint building pipeline to use backend-agnostic expressions
- Supporting expression types not used by the model checker
- Optimizing conversion performance (correctness first)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Incomplete expression type coverage | High | Medium | Audit all expression types in codebase, add fallback error handling |
| Function declaration mismatch | High | Medium | Maintain z3-to-cvc5 function registry, recreate declarations |
| Variable binding differences | Medium | Low | Track variable mappings explicitly |
| Quantifier handling complexity | High | Medium | Special case ForAll/Exists with bound variable reconstruction |
| Performance degradation | Low | Low | Cache converted expressions if needed |

## Implementation Phases

### Phase 1: Core Boolean Conversion [NOT STARTED]

**Goal**: Convert basic boolean operations (And, Or, Not, Implies, BoolVal) and boolean constants/variables.

**Tasks**:
- [ ] Add `_is_z3_expr()` helper to detect Z3 expressions
- [ ] Add `_convert_z3_to_cvc5()` method with dispatch on expression type
- [ ] Implement boolean operation handlers: `is_and`, `is_or`, `is_not`, `is_implies`
- [ ] Implement boolean constant handlers: `is_true`, `is_false`
- [ ] Implement boolean variable handler using `is_const` with BoolSort check
- [ ] Wrap `add()` and `assert_tracked()` to call conversion
- [ ] Add unit tests for each boolean operation

**Timing**: 1.5 hours

**Files to modify**:
- `code/src/model_checker/solver/cvc5_adapter.py` - Add conversion logic

**Verification**:
- Unit tests pass for And, Or, Not, Implies, BoolVal conversion
- Simple boolean constraint can be added and checked with CVC5

---

### Phase 2: BitVector Conversion [NOT STARTED]

**Goal**: Convert bitvector expressions (BitVec variables, BitVecVal constants, operations).

**Tasks**:
- [ ] Implement bitvector variable handler (`is_const` with BitVecSort)
- [ ] Implement bitvector constant handler (`is_bv_value`)
- [ ] Implement bitvector operation handlers: comparison (==, <, <=, etc.), arithmetic (+, -, &, |)
- [ ] Handle bitvector sort extraction and recreation
- [ ] Add unit tests for bitvector expressions

**Timing**: 1.5 hours

**Files to modify**:
- `code/src/model_checker/solver/cvc5_adapter.py` - Add bitvector conversion

**Verification**:
- Unit tests pass for BitVec, BitVecVal conversion
- Bitvector constraints with operations work correctly

---

### Phase 3: Function Declarations and Applications [NOT STARTED]

**Goal**: Convert uninterpreted function declarations and their applications (verify, falsify functions).

**Tasks**:
- [ ] Add `_func_registry: Dict[str, Any]` to track converted function declarations
- [ ] Implement function declaration handler (`is_func_decl` check)
- [ ] Implement function application handler (`is_app` with function application)
- [ ] Handle function sort conversion (domain and range sorts)
- [ ] Register converted functions by name for reuse
- [ ] Add unit tests for function declarations and applications

**Timing**: 1.5 hours

**Files to modify**:
- `code/src/model_checker/solver/cvc5_adapter.py` - Add function conversion and registry

**Verification**:
- Unit tests pass for Function declarations
- Function application constraints work correctly
- Same function used multiple times maps to same CVC5 declaration

---

### Phase 4: Quantifiers and Integration Testing [NOT STARTED]

**Goal**: Convert quantified expressions (ForAll, Exists) and run full integration tests.

**Tasks**:
- [ ] Implement quantifier detection (`is_quantifier`)
- [ ] Implement ForAll handler with bound variable reconstruction
- [ ] Implement Exists handler with bound variable reconstruction
- [ ] Handle quantifier variable sorts correctly
- [ ] Add variable substitution for de Bruijn indices
- [ ] Run integration tests with actual model checker examples
- [ ] Fix any edge cases discovered in integration

**Timing**: 1.5 hours

**Files to modify**:
- `code/src/model_checker/solver/cvc5_adapter.py` - Add quantifier conversion
- `code/src/model_checker/solver/tests/unit/test_equivalence.py` - Add CVC5 integration tests

**Verification**:
- Unit tests pass for ForAll, Exists conversion
- Integration tests run with CVC5 backend
- Model checker examples that crashed now work with CVC5

---

## Testing & Validation

- [ ] Unit tests for each expression type conversion
- [ ] Integration test running existing examples with CVC5
- [ ] Comparison test: Z3 and CVC5 produce same results on sample problems
- [ ] Edge case tests: empty And/Or, deeply nested expressions, complex quantifiers
- [ ] Run `test_solver_comparison.py` with CVC5 enabled

## Artifacts & Outputs

- `code/src/model_checker/solver/cvc5_adapter.py` - Updated with expression conversion
- `code/src/model_checker/solver/tests/unit/test_cvc5_conversion.py` - New unit tests (optional, can add to existing)
- `specs/072_fix_cvc5_constraint_compatibility/summaries/01_cvc5-expression-conversion-summary.md` - Execution summary

## Rollback/Contingency

If expression conversion proves too complex or introduces regressions:
1. Revert changes to `cvc5_adapter.py`
2. Document unsupported expression types
3. Consider Option B (consistent backend usage) as fallback approach
4. Add runtime check to warn users when Z3 expressions are passed to CVC5
