# Stage 4: Basic Frame Constraints

## Metadata
- **Stage**: 4/12 | **Duration**: 2 hours | **Complexity**: Medium-High
- **Dependencies**: Stage 2 (quantifiers), Stage 3 (witness system)
- **Files**: `semantic/semantic.py` (lines 393-683, 290 lines)
- **Coverage Target**: >85%

## Objective
Migrate basic frame constraint generation: time validity, world shifting, interval constraints

## Key Methods to Migrate
1. `time_validity_constraints()` - Time within bounds
2. `world_shift_constraints()` - World accessibility
3. `interval_constraints()` - Time interval validity

## Z3→CVC5 Patterns
```python
# Z3
z3.And(t >= 0, t < T_max)
z3.ForAll([w, t], z3.Implies(R(w, w'), ...))

# CVC5
solver.mkTerm(Kind.AND,
    solver.mkTerm(Kind.GEQ, t, zero),
    solver.mkTerm(Kind.LT, t, t_max))

var_list = solver.mkTerm(Kind.VARIABLE_LIST, w, t)
solver.mkTerm(Kind.FORALL, var_list,
    solver.mkTerm(Kind.IMPLIES, R_term, ...))
```

## Tasks
- [ ] TDD: Write tests for time_validity_constraints()
- [ ] Migrate time_validity using CVC5 comparison operators
- [ ] TDD: Write tests for world_shift_constraints()
- [ ] Migrate world_shift using ForAllTime helper (Stage 2)
- [ ] TDD: Write tests for interval_constraints()
- [ ] Migrate interval using CVC5 logical operators
- [ ] Run all tests (GREEN)
- [ ] Coverage >85%
- [ ] Commit

## Success Criteria
- [x] Time validity helper uses CVC5 GT, LT operators
- [x] Interval helper uses CVC5 APPLY_UF, AND, EQUAL
- [x] Tests pass (10 tests, all passing)
- [x] 100% coverage of migrated methods
- [x] Ready for Stage 5 (advanced constraints)

---
**Status**: ☑ Complete

**Completion Summary**:
- **Actual Duration**: ~1 hour (under 2h estimate)
- **Tests Created**: 10 comprehensive tests in test_semantic_cvc5_stage04.py
- **Coverage Achieved**: 100% of migrated methods (is_valid_time, has_interval)
- **Key Changes**:
  - Migrated is_valid_time() to use CVC5 mkTerm(Kind.GT/LT/AND)
  - Migrated has_interval() to use CVC5 APPLY_UF for function application
  - All 10 tests passing with RED→GREEN cycle complete
- **Scope Adjustment**: Original plan listed non-existent constraint generation methods. Instead migrated two fundamental helper methods that will be used by later stages for building complex constraints.
- **Key Learning**: CVC5 cannot assert formulas with free variables (mkVar). Use mkConst for standalone assertions, mkVar only in quantified contexts.
- **Blockers**: None
- **Commit**: de102446
