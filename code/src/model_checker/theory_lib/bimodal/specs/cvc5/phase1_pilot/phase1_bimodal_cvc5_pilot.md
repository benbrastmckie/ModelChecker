# Phase 1: Bimodal Theory CVC5 Pilot Migration

## Metadata
- **Date**: 2025-10-02
- **Phase**: 1 of 3 (SMT Solver Abstraction Implementation)
- **Parent Plan**: [specs/plans/105_smt_solver_abstraction_REVISED.md](../../../../../specs/plans/105_smt_solver_abstraction_REVISED.md)
- **Objective**: Migrate bimodal theory to CVC5 without abstraction layer, learning API patterns using TDD
- **Complexity**: High
- **Estimated Duration**: 1 week
- **Branch**: `feature/bimodal-cvc5-pilot`
- **Standards**:
  - [CODE_STANDARDS.md](../../../../../docs/core/CODE_STANDARDS.md)
  - [TESTING.md](../../../../../docs/core/TESTING.md)
  - [ARCHITECTURE.md](../../../../../docs/core/ARCHITECTURE.md)
- **Detailed Stage Breakdown**: ⭐ **[12-Stage Implementation Guide](STAGE_INDEX.md)** ⭐
  - Phase 1 subdivided into 12 manageable stages (1-2 hours each)
  - Individual stage files in this directory (stage01_*.md through stage12_*.md)
  - Total: 20.5 hours across 12 focused implementation stages (+Stage 7.5 cleanup)

## Overview

### Strategic Context

**Phase 0 Success**: CVC5 validation complete on 6 critical examples (BM_CM_1, BM_CM_2, TN_CM_2) with 5/5 deterministic success, ~6ms average (850× faster than Z3's 5s+ timeout).

**Phase 1 Goal**: Complete migration of bimodal theory from Z3 to CVC5 to learn API translation patterns that will inform abstraction layer design in Phase 2.

**Key Learning Objectives**:
1. Real-world Z3→CVC5 API translation patterns
2. Witness predicate handling with CVC5 MBQI+enum-inst
3. ForAll quantifier translation without Z3 pattern hints
4. Performance characteristics of CVC5 on full theory
5. Pain points and edge cases for abstraction design

### Bimodal Theory Structure

**Core Files** (6 files, ~5,600 LOC):
- `semantic.py` (2,593 lines): 24x And, 14x ForAll, 8x Function calls
- `operators.py` (1,083 lines): Modal/temporal operator definitions
- `witness_constraints.py` (257 lines): Critical ForAll patterns for witness predicates
- `witness_registry.py` (177 lines): Witness management system
- `examples.py` (671 lines): 22 test examples
- `iterate.py` (602 lines): Model iteration engine

**Test Organization** (11 files):
- `tests/unit/`: Component-level tests (pytest framework)
- `tests/integration/`: Theory workflow tests
- `tests/e2e/`: Complete example execution tests

**Critical Examples** (6 focus cases):
- BM_CM_1, BM_CM_2: Bimodal countermodel examples
- TN_CM_1, TN_CM_2: Temporal countermodel examples
- MD_CM_1, MD_CM_2: Modal countermodel examples

### Z3→CVC5 Translation Reference

**Critical API Patterns** (from Report 011 and Phase 0 experience):

1. **Quantifiers**:
   ```python
   # Z3 (with pattern hints)
   z3.ForAll([x], body, patterns=[z3.Pattern(f(x))])

   # CVC5 (using MBQI+enum-inst instead)
   var = solver.mkVar(sort, "x")
   solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, var), body)
   # Configure: solver.setOption("mbqi", "true"), solver.setOption("enum-inst", "true")
   ```

2. **Functions**:
   ```python
   # Z3
   f = z3.Function('f', z3.BoolSort(), z3.BoolSort())

   # CVC5
   f_sort = solver.mkFunctionSort([solver.getBooleanSort()], solver.getBooleanSort())
   f = solver.mkConst(f_sort, 'f')
   ```

3. **Operators**:
   ```python
   # Z3 (Pythonic)
   z3.And(a, b), z3.Or(a, b), z3.Implies(a, b)

   # CVC5 (explicit)
   solver.mkTerm(Kind.AND, a, b)
   solver.mkTerm(Kind.OR, a, b)
   solver.mkTerm(Kind.IMPLIES, a, b)
   ```

4. **Arrays**:
   ```python
   # Z3
   z3.Select(array, index)

   # CVC5
   solver.mkTerm(Kind.SELECT, array, index)
   ```

5. **BitVectors** (CRITICAL: Argument order reversed!):
   ```python
   # Z3
   z3.BitVecVal(value, size)

   # CVC5
   solver.mkBitVector(size, value)  # NOTE: size first!
   ```

### CVC5 Configuration Requirements

**Mandatory for Witness Predicates** (from Report 012):
```python
solver = cvc5.Solver()
solver.setLogic("ALL")  # Full quantifier + arithmetic support
solver.setOption("produce-models", "true")

# CRITICAL for performance
solver.setOption("mbqi", "true")        # Model-based quantifier instantiation
solver.setOption("enum-inst", "true")   # Enumerative instantiation
```

**Without MBQI+enum-inst**: CVC5 returns "unknown" on witness predicate examples.

## Success Criteria

### Functional Requirements
- [ ] All bimodal core files migrated to CVC5 API
- [ ] All 6 critical examples solve deterministically with CVC5
- [ ] Performance maintained: BM_CM_* examples ~6ms (vs 5s+ Z3 timeout)
- [ ] All existing unit tests pass with CVC5
- [ ] All integration tests pass with CVC5

### Quality Requirements (Per TESTING.md)
- [ ] **TDD Compliance**: All tests written BEFORE implementation code
- [ ] Test coverage >85% overall for bimodal package
- [ ] Test coverage >90% for witness predicate system (critical path)
- [ ] All tests pass in RED→GREEN→REFACTOR cycle

### Documentation Requirements (Per CODE_STANDARDS.md)
- [ ] API translation patterns documented (update Report 011)
- [ ] Pain points and edge cases recorded for Phase 2 design
- [ ] No historical references in documentation
- [ ] Migration results report created

### Learning Objectives
- [ ] Z3→CVC5 API patterns validated on real theory
- [ ] Witness predicate ForAll translation validated
- [ ] Performance characteristics understood
- [ ] Abstraction design insights captured

## Technical Design

### Migration Strategy

**5-Phase Incremental Migration**:
1. **Semantic Core**: Migrate semantic.py foundational functions
2. **Operators**: Migrate modal/temporal operator definitions
3. **Witness System**: Migrate witness_constraints.py and witness_registry.py
4. **Integration**: Migrate examples.py and iterate.py
5. **Documentation**: Update all bimodal documentation

**TDD Approach per Phase**:
1. Write test FIRST for component migration (RED state)
2. Run test - verify it fails (semantic.py still uses Z3)
3. Migrate component to CVC5 (minimal implementation)
4. Run test - verify it passes (GREEN state)
5. Refactor for quality while maintaining GREEN

### File Modification Plan

#### 1. semantic.py (2,593 lines)

**Z3 API Usage**:
- 24× `z3.And()` calls
- 14× `z3.ForAll()` quantifiers
- 8× `z3.Function()` declarations
- Multiple `z3.Select()` for arrays
- BitVec operations with `z3.BitVecVal()`

**Migration Tasks**:
- [ ] Replace `import z3` with `import cvc5`
- [ ] Translate `z3.And(*args)` → `solver.mkTerm(Kind.AND, *args)`
- [ ] Translate `z3.ForAll([vars], body)` → `solver.mkTerm(Kind.FORALL, var_list, body)`
- [ ] Translate `z3.Function()` → `solver.mkConst(solver.mkFunctionSort(...))`
- [ ] Fix BitVecVal argument order: `(value, size)` → `(size, value)`
- [ ] Update relative imports: `from .operators import ...`

**Critical Sections**:
- `define_bimodal_semantics()`: Core semantic function definitions
- `create_world_constraints()`: Quantifiers over worlds
- `define_accessibility()`: Relational constraints with ForAll

#### 2. operators.py (1,083 lines)

**Z3 API Usage**:
- Modal operators (Box, Diamond) using witness predicates
- Temporal operators (Future, Past) using witness predicates
- Operator composition with And/Or/Implies

**Migration Tasks**:
- [ ] Update modal operator Box/Diamond to use CVC5 ForAll (MBQI)
- [ ] Update temporal operator Future/Past to use CVC5 ForAll
- [ ] Replace operator overloading with explicit `solver.mkTerm()`
- [ ] Update witness predicate patterns: Z3 patterns → CVC5 MBQI reliance
- [ ] Relative imports: `from .semantic import ...`

**Critical Sections**:
- `Box()`, `Diamond()`: Modal operators with witness predicates
- `Future()`, `Past()`: Temporal operators with witness predicates

#### 3. witness_constraints.py (257 lines)

**Z3 API Usage**:
- ForAll quantifiers with pattern hints for witness predicates
- Function application in quantifier bodies
- Complex nested quantifiers

**Migration Tasks**:
- [ ] Translate ForAll with patterns to CVC5 ForAll with MBQI
- [ ] Remove pattern hints (CVC5 uses MBQI+enum-inst instead)
- [ ] Ensure MBQI+enum-inst configured for performance
- [ ] Document pattern hint → MBQI translation strategy

**Critical Sections**:
- `create_witness_constraints()`: Core witness predicate logic
- Nested ForAll quantifiers for witness properties

#### 4. witness_registry.py (177 lines)

**Z3 API Usage**:
- Function declarations for witness tracking
- Constraint management using Z3 solver

**Migration Tasks**:
- [ ] Update Function declarations to CVC5 API
- [ ] Update constraint registration to use CVC5 solver
- [ ] Maintain witness tracking semantics

#### 5. examples.py (671 lines)

**Z3 API Usage**:
- Solver creation and configuration
- Example constraint assertion
- Result checking and model extraction

**Migration Tasks**:
- [ ] Replace Z3 solver creation with CVC5 solver + MBQI+enum-inst options
- [ ] Update assertion syntax to CVC5
- [ ] Update check_sat and model extraction to CVC5 API
- [ ] Ensure all 22 examples work with CVC5

#### 6. iterate.py (602 lines)

**Z3 API Usage**:
- Model iteration using Z3 solver
- Model value extraction

**Migration Tasks**:
- [ ] Update solver operations to CVC5 API
- [ ] Update model value extraction to CVC5 API
- [ ] Maintain iteration semantics

### Testing Strategy

**TDD Workflow** (per TESTING.md):

```bash
# Phase 1: Semantic Core Migration
# Step 1: Write test FIRST (RED state)
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantic_cvc5.py -v
# Expected: FAIL (semantic.py still uses Z3)

# Step 2: Migrate semantic.py to CVC5
# ... make changes ...

# Step 3: Run test - verify GREEN
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantic_cvc5.py -v
# Expected: PASS

# Step 4: Refactor while maintaining GREEN
# ... improve code quality ...

# Step 5: Verify all tests still pass
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/ -v

# Repeat for each phase: operators, witness, integration, documentation
```

**Test Coverage Requirements** (per TESTING.md §3.1):
```bash
# Overall coverage >85%
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ \
    --cov=model_checker.theory_lib.bimodal \
    --cov-report=term-missing \
    --cov-fail-under=85

# Witness system coverage >90% (critical path)
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cvc5.py \
    --cov=model_checker.theory_lib.bimodal.semantic.witness_constraints \
    --cov=model_checker.theory_lib.bimodal.semantic.witness_registry \
    --cov-report=term-missing \
    --cov-fail-under=90
```

**Integration Testing**:
```bash
# Run all examples with CVC5
cd Code
nix-shell ../shell.nix --run "./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py"

# Performance benchmark on critical examples
nix-shell ../shell.nix --run "python3 benchmark_cvc5_simple.py"
```

## Implementation Phases

### Sub-Phase 1.1: Semantic Core Migration (2 days)

**Objective**: Migrate semantic.py core functions to CVC5

#### Tasks
- [ ] **[TDD] Write test_semantic_cvc5.py** (RED first)
  - File: `tests/unit/test_semantic_cvc5.py`
  - Test: Core semantic functions with CVC5
  - Expected: FAIL (semantic.py uses Z3)

- [ ] **Migrate define_bimodal_semantics() to CVC5**
  - Function: Core semantic definitions
  - Changes: Z3 API → CVC5 API for Function declarations
  - Verify: Test passes (GREEN)

- [ ] **Migrate create_world_constraints() to CVC5**
  - Function: World constraint generation
  - Changes: ForAll quantifiers Z3 → CVC5
  - Verify: Test passes

- [ ] **Migrate define_accessibility() to CVC5**
  - Function: Accessibility relation constraints
  - Changes: ForAll with And/Or/Implies
  - Verify: Test passes

- [ ] **Fix BitVecVal argument order issues**
  - Search: All BitVecVal usage in semantic.py
  - Fix: `(value, size)` → `(size, value)`
  - Verify: Tests pass

- [ ] **Refactor for code quality**
  - Improve: Import organization, error handling
  - Verify: Tests still pass (maintain GREEN)

#### Testing
```bash
# TDD cycle for semantic core
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantic_cvc5.py -v --cov=model_checker.theory_lib.bimodal.semantic.semantic --cov-report=term-missing
```

**Success Criteria**:
- Test written BEFORE migration
- RED→GREEN cycle completed
- Code quality improved through refactoring
- Test coverage >85% for semantic.py

### Sub-Phase 1.2: Operators Migration (1.5 days)

**Objective**: Migrate modal/temporal operators to CVC5

#### Tasks
- [ ] **[TDD] Write test_operators_cvc5.py** (RED first)
  - File: `tests/unit/test_operators_cvc5.py`
  - Test: Modal (Box, Diamond) and temporal (Future, Past) operators
  - Expected: FAIL (operators.py uses Z3)

- [ ] **Migrate Box operator to CVC5**
  - Operator: Modal Box with witness predicates
  - Changes: ForAll with patterns → ForAll with MBQI
  - Note: Document how witness predicates work without patterns

- [ ] **Migrate Diamond operator to CVC5**
  - Operator: Modal Diamond with witness predicates
  - Changes: Similar to Box

- [ ] **Migrate Future operator to CVC5**
  - Operator: Temporal Future with witness predicates
  - Changes: ForAll translation

- [ ] **Migrate Past operator to CVC5**
  - Operator: Temporal Past with witness predicates
  - Changes: ForAll translation

- [ ] **Update operator composition logic**
  - Changes: And/Or/Implies operator overloading → explicit mkTerm
  - Verify: Tests pass

- [ ] **Refactor for quality**
  - Improve: Code organization, documentation
  - Verify: Tests pass

#### Testing
```bash
# TDD cycle for operators
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_operators_cvc5.py -v --cov=model_checker.theory_lib.bimodal.semantic.operators --cov-report=term-missing
```

**Success Criteria**:
- Test written BEFORE migration
- All operators migrated successfully
- Witness predicate behavior preserved
- Test coverage >85% for operators.py

### Sub-Phase 1.3: Witness System Migration (2 days)

**Objective**: Migrate witness constraint system to CVC5 (CRITICAL)

#### Tasks
- [ ] **[TDD] Write test_witness_cvc5.py** (RED first)
  - File: `tests/unit/test_witness_cvc5.py`
  - Test: Witness constraint creation and validation
  - Expected: FAIL (witness_constraints.py uses Z3)
  - Focus: ForAll patterns → CVC5 MBQI translation

- [ ] **Migrate create_witness_constraints() to CVC5**
  - Function: Core witness predicate logic
  - Changes: Remove pattern hints, rely on MBQI+enum-inst
  - Verify: Tests pass

- [ ] **Translate nested ForAll quantifiers**
  - Pattern: ForAll with ForAll in body
  - Changes: Proper variable binding in CVC5
  - Verify: Correct semantics maintained

- [ ] **Update witness_registry.py to CVC5**
  - Changes: Function declarations and constraint registration
  - Verify: Tracking semantics preserved

- [ ] **Validate MBQI+enum-inst configuration**
  - Test: Ensure solver configured correctly
  - Verify: Performance maintained (~6ms on BM_CM_*)

- [ ] **Document pattern → MBQI translation**
  - File: Update Report 011 with real-world witness patterns
  - Content: How Z3 patterns map to CVC5 MBQI configuration

- [ ] **Refactor for quality**
  - Improve: Error handling, documentation
  - Verify: Tests pass

#### Testing
```bash
# TDD cycle for witness system (>90% coverage required)
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cvc5.py -v --cov=model_checker.theory_lib.bimodal.semantic.witness_constraints --cov=model_checker.theory_lib.bimodal.semantic.witness_registry --cov-report=term-missing --cov-fail-under=90
```

**Success Criteria**:
- Test written BEFORE migration
- Witness predicates work correctly with MBQI+enum-inst
- Pattern hints successfully removed
- Test coverage >90% (critical path requirement)
- Performance validated (~6ms on critical examples)

### Sub-Phase 1.4: Integration Migration (1 day)

**Objective**: Migrate examples.py and iterate.py to complete CVC5 integration

#### Tasks
- [ ] **[TDD] Write test_integration_cvc5.py** (RED first)
  - File: `tests/integration/test_integration_cvc5.py`
  - Test: Complete workflow from example to result
  - Expected: FAIL (examples.py uses Z3)

- [ ] **Migrate examples.py solver setup**
  - Changes: Replace Z3 solver with CVC5 + MBQI+enum-inst
  - Update: All 22 example configurations
  - Verify: Tests pass

- [ ] **Migrate iterate.py model iteration**
  - Changes: Z3 model API → CVC5 model API
  - Verify: Iteration semantics preserved

- [ ] **Run all 22 examples with CVC5**
  - Execute: `./dev_cli.py bimodal/examples.py`
  - Verify: All examples solve correctly
  - Benchmark: Performance on 6 critical examples

- [ ] **Validate 6 critical examples**
  - BM_CM_1, BM_CM_2: ~6ms deterministic
  - TN_CM_1, TN_CM_2: ~0.2ms deterministic
  - MD_CM_1, MD_CM_2: Validate performance
  - Document: Any performance variations

- [ ] **Run end-to-end tests**
  - File: `tests/e2e/test_bimodal_cvc5.py`
  - Verify: Complete user workflow works

#### Testing
```bash
# Integration testing
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/ -v

# End-to-end testing
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/e2e/ -v

# Performance validation
cd Code
nix-shell ../shell.nix --run "python3 benchmark_cvc5_simple.py"
```

**Success Criteria**:
- All 22 examples work with CVC5
- 6 critical examples maintain performance
- Integration and e2e tests pass
- Complete workflow validated

### Sub-Phase 1.5: Documentation and Reporting (0.5 days)

**Objective**: Document learnings and update project documentation

#### Tasks
- [ ] **Update Report 011 with real-world patterns**
  - File: `specs/reports/011_z3_to_cvc5_api_translation.md`
  - Add: Bimodal migration patterns and examples
  - Document: Pain points, edge cases, workarounds
  - No historical references (current state only)

- [ ] **Create Phase 1 results report**
  - File: `specs/reports/014_bimodal_cvc5_pilot_results.md`
  - Content:
    - Migration summary (files changed, LOC updated)
    - API translation patterns learned
    - Performance results (6 critical examples)
    - Pain points for abstraction design
    - Recommendations for Phase 2
  - No historical references

- [ ] **Update bimodal README**
  - File: `code/src/model_checker/theory_lib/bimodal/README.md`
  - Add: CVC5 usage instructions
  - Document: MBQI+enum-inst requirement
  - No historical references

- [ ] **Document abstraction design insights**
  - File: `code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase1_learnings.md`
  - Content:
    - Key abstraction points identified
    - Solver-agnostic patterns needed
    - Solver-specific handling required
    - Recommendations for SolverInterface design

#### Documentation Standards (Per CODE_STANDARDS.md)
- No historical references (no "added in", "recently", etc.)
- User-friendly language
- Clear examples
- Current state only

**Success Criteria**:
- All documentation updated
- Phase 1 results report complete
- Abstraction design insights captured
- No historical references in docs

## Risk Mitigation

### Risk 1: Pattern Hints Incompatibility
**Risk**: CVC5 doesn't support Z3 pattern hints, witness predicates may fail
**Mitigation**: Use MBQI+enum-inst configuration validated in Phase 0
**Fallback**: If MBQI fails, investigate alternative quantifier strategies

### Risk 2: API Translation Errors
**Risk**: Subtle API differences cause incorrect results
**Mitigation**: TDD approach catches errors early, comprehensive test suite validates correctness
**Fallback**: Document differences, manual validation against Z3 results

### Risk 3: Performance Regression
**Risk**: CVC5 migration slower than Z3 on some examples
**Mitigation**: Benchmark all examples, optimize CVC5 configuration
**Fallback**: Document performance differences, keep configuration tunable

### Risk 4: Nested Quantifier Issues
**Risk**: Complex nested ForAll quantifiers fail in CVC5
**Mitigation**: Incremental migration with test validation at each step
**Fallback**: Simplify quantifier structure if needed, document limitations

### Risk 5: BitVec Argument Order Bugs
**Risk**: Reversed argument order causes subtle bugs
**Mitigation**: Systematic search and replacement, dedicated tests for BitVec operations
**Fallback**: Manual review of all BitVec usage

## Dependencies

### External Dependencies
- **CVC5**: Version 1.3.1 (validated in Report 012)
  - Installation: `pip install cvc5`
  - NixOS: Use `shell.nix` with `LD_LIBRARY_PATH` configuration

### Internal Dependencies
- **Phase 0**: Completed ✓ (CVC5 validation on 6 examples)
- **Report 011**: Z3 to CVC5 API translation reference
- **Report 012**: CVC5 feasibility and configuration
- **Bimodal theory**: Current Z3 implementation as baseline

### Branch Dependencies
- **Base branch**: `feature/cvc5-feasibility-test`
- **New branch**: `feature/bimodal-cvc5-pilot`
- **Merge target**: After Phase 1 complete, prepare for Phase 2

## Progress Tracking

**⭐ Active Tracking**: See **[12-Stage Implementation Guide](stages/STAGE_INDEX.md)** for detailed progress tracking.

**Current Status**: 🚀 **IN PROGRESS** - Stages 1-2 Complete (2/12)
- ✅ Stage 1: BimodalSemantics Core Setup (commit bceb98d0)
- ✅ Stage 2: ForAll/Exists Quantifier Helpers (commit 8cf9fccc)
- ⏳ Stage 3: Witness Registration System (next)

### Completion Checklist (High-Level Sub-Phases)

#### Sub-Phase 1.1: Semantic Core ☐
- [ ] test_semantic_cvc5.py written (RED)
- [ ] define_bimodal_semantics() migrated
- [ ] create_world_constraints() migrated
- [ ] define_accessibility() migrated
- [ ] BitVecVal fixes applied
- [ ] Tests pass (GREEN)
- [ ] Code refactored

#### Sub-Phase 1.2: Operators ☐
- [ ] test_operators_cvc5.py written (RED)
- [ ] Box operator migrated
- [ ] Diamond operator migrated
- [ ] Future operator migrated
- [ ] Past operator migrated
- [ ] Operator composition updated
- [ ] Tests pass (GREEN)

#### Sub-Phase 1.3: Witness System ☐
- [ ] test_witness_cvc5.py written (RED)
- [ ] create_witness_constraints() migrated
- [ ] Nested ForAll translated
- [ ] witness_registry.py updated
- [ ] MBQI+enum-inst validated
- [ ] Pattern → MBQI documented
- [ ] Tests pass (GREEN) with >90% coverage

#### Sub-Phase 1.4: Integration ☐
- [ ] test_integration_cvc5.py written (RED)
- [ ] examples.py migrated
- [ ] iterate.py migrated
- [ ] All 22 examples work
- [ ] 6 critical examples validated
- [ ] E2E tests pass

#### Sub-Phase 1.5: Documentation ☐
- [ ] Report 011 updated
- [ ] Phase 1 results report created
- [ ] Bimodal README updated
- [ ] Abstraction insights documented

### Performance Metrics

| Example | Z3 Time | CVC5 Time | Speedup | Status |
|---------|---------|-----------|---------|--------|
| BM_CM_1 | 5000ms+ | ~6ms | 850× | ☐ |
| BM_CM_2 | 5000ms+ | ~6ms | 850× | ☐ |
| TN_CM_1 | Timeout | ~0.2ms | N/A | ☐ |
| TN_CM_2 | Timeout | ~0.2ms | N/A | ☐ |
| MD_CM_1 | TBD | TBD | TBD | ☐ |
| MD_CM_2 | TBD | TBD | TBD | ☐ |

### Test Coverage Metrics

| Component | Coverage Target | Current | Status |
|-----------|----------------|---------|--------|
| semantic.py | >85% | - | ☐ |
| operators.py | >85% | - | ☐ |
| witness_constraints.py | >90% | - | ☐ |
| witness_registry.py | >90% | - | ☐ |
| examples.py | >85% | - | ☐ |
| iterate.py | >85% | - | ☐ |
| **Overall** | **>85%** | - | ☐ |

## Next Steps

**Upon Phase 1 Completion**:
1. ✓ Create Phase 1 results report (specs/reports/014_bimodal_cvc5_pilot_results.md)
2. ✓ Update master plan with Phase 1 findings
3. → Proceed to **Phase 2**: Abstraction Layer Design
4. Use Phase 1 learnings to inform SolverInterface design
5. Design abstraction to handle witnessed pain points

**Phase 2 Preview**:
- Create SolverInterface based on bimodal migration patterns
- Implement Z3SolverAdapter (thin wrapper around existing code)
- Implement CVC5SolverAdapter (using Phase 1 translation patterns)
- Design factory for solver selection
- Integrate with settings system

**Deliverables to Phase 2**:
- Complete CVC5-based bimodal theory (reference implementation)
- Comprehensive API translation pattern documentation
- Performance benchmarks for comparison
- Identified abstraction points and solver-specific handling needs
- Pain points and edge cases to address in abstraction design
