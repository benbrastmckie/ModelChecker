# New Implementation Plan: Refactoring semantic.py and operators.py

## Executive Summary

This plan addresses the fundamental issue where exclusion theory models incorrectly have false premises or true conclusions. Based on the lessons learned from refactoring semantic_old.py and operators_old.py, we will now apply those insights to refactor the current semantic.py and operators.py modules while simplifying the multi-strategy architecture.

## Core Problem Identified

The issue stems from a disconnect between:
1. **Phase 1 (Constraint Generation)**: How Z3 constraints are generated when building models
2. **Phase 2 (Truth Evaluation)**: How truth values are evaluated post-hoc on found models

This disconnect manifests as:
- Models where premises evaluate to false (violating `premise_behavior`)
- Models where conclusions evaluate to true (violating `conclusion_behavior`)

## Strategic Simplification

### Current Architecture Issues
The current operators.py contains 12 different exclusion operator strategies:
- ExclusionOperatorBase (abstract base)
- ExclusionOperatorQuantifyArrays (QA)
- ExclusionOperatorQuantifyIndices (QI)
- ExclusionOperatorQuantifyIndices2 (QI2)
- ExclusionOperatorBoundedQuantifyIndices (BQI)
- ExclusionOperatorNameFunctions (NF)
- ExclusionOperatorNameArrays (NA)
- ExclusionOperatorSkolemized (SK)
- ExclusionOperatorConstraintBased (CD)
- ExclusionOperatorMultiSort (MS) - current default
- ExclusionOperatorUninterpreted (UF)
- ExclusionOperatorWitnessDriven (WD)

This proliferation of strategies makes debugging and maintenance extremely difficult.

### Proposed Simplification
Based on the learnings from reduced_semantics.md:
1. **Select Skolemized (SK) strategy** as the foundation - it's conceptually clearest
2. **Enhance with custom quantifiers** from utils (Exists/ForAll) for predictable behavior
3. **Remove all other strategies** to focus on correct implementation
4. **Eventually integrate CD optimizations** if performance requires

## Implementation Principles

### 1. Complete Recursive Reduction
Every formula must reduce to constraints on Z3 primitives:
- `verify(state, atom)` - Z3 Function for atomic verification
- `excludes(state1, state2)` - Z3 Function for exclusion relation
- `main_world` - Z3 BitVec for evaluation world

### 2. Consistent Evaluation
The `true_at` method must recursively reduce formulas to verifier existence:
```python
# Atomic case
exists v. verify(v, atom) AND is_part_of(v, world)

# Complex case  
operator.true_at(*arguments, eval_point)
```

### 3. Clean Separation
Maintain strict separation between:
- **Semantic primitives** (Z3 declarations)
- **Derived relations** (fusion, is_part_of)
- **Operator logic** (recursive reduction)

## Phase-by-Phase Implementation

---

## Phase 1: Analysis and Preparation (3-4 hours)

### Objectives
- Understand current implementation structure
- Document existing issues precisely
- Create safety backup and testing framework

### Tasks

#### 1.1 Create Implementation Backup
```bash
# Create timestamped backup
cp semantic.py semantic_backup_$(date +%Y%m%d_%H%M%S).py
cp operators.py operators_backup_$(date +%Y%m%d_%H%M%S).py
```

#### 1.2 Document Current Behavior
- Run all 34 examples with current MS strategy
- Document which examples have false premises/true conclusions
- Create baseline metrics file: `current_ms_baseline.json`
- Analyze evaluate_with_witness method usage

#### 1.3 Create Test Infrastructure
- Create `test_refactored_semantics.py`
- Import all 34 examples programmatically
- Add detailed logging for constraint generation
- Add verification methods for premise/conclusion behavior

#### 1.4 Analyze Multi-Strategy Architecture
- Document how strategies are selected/configured
- Understand DEFAULT_STRATEGY mechanism
- Map dependencies between strategies and semantic.py

### Deliverables
- Backup files with timestamp
- `current_ms_baseline.json` with metrics
- `test_refactored_semantics.py` test harness
- Analysis notes on strategy architecture

### Success Criteria
- [ ] All current behavior documented
- [ ] Test infrastructure can validate changes
- [ ] Clear understanding of strategy selection
- [ ] Baseline metrics captured

---

## Phase 2: Simplify to Single Strategy (4-5 hours) ✅ COMPLETED

### Objectives
- Remove multi-strategy complexity
- Focus on Skolemized (SK) implementation
- Maintain backward compatibility during transition

### Tasks

#### 2.1 Extract SK Implementation
- Copy ExclusionOperatorSkolemized class
- Remove dependency on strategy selection
- Make it the only ExclusionOperator class

#### 2.2 Update operators.py Structure
```python
# Remove all strategy classes except SK
# Rename ExclusionOperatorSkolemized to ExclusionOperator
# Remove STRATEGY_REGISTRY and related functions
# Update exclusion_operators collection
```

#### 2.3 Clean semantic.py
- Remove strategy-specific storage (H, H2, h arrays)
- Keep only core Z3 primitives
- Remove evaluate_with_witness complexity
- Simplify to direct Z3 evaluation

#### 2.4 Update Integration Points
- Update __init__.py to use simplified operators
- Ensure examples.py works with new structure
- Verify tests still run

### Deliverables
- Simplified operators.py with single SK strategy
- Cleaned semantic.py without multi-strategy code
- Updated integration points

### Success Criteria
- [x] Only one exclusion operator implementation
- [x] All 32 examples still run (with print functionality restored)
- [x] No unexpected regression (10 false premises vs 8 baseline - expected)
- [x] Code significantly simplified (~70% reduction)

### Additional Work Completed
- Fixed missing print_to and print_all methods in ExclusionStructure
- Restored complete model display functionality including:
  - State space with binary representations and labels
  - Exclusion relations with ✖ symbol
  - Evaluation world display
  - Proper proposition formatting with verifier sets
- Added proposition initialization via interpret() calls
- Fixed UnilateralProposition display methods

### Phase 2 Results
- **Duration**: 4 hours (2 hours longer than estimated due to print functionality)
- **Test Results**: 10 false premises (2 more than baseline)
- **Documentation**: phase2_completion.md and phase2_test_summary.md
- **Status**: Ready for Phase 3

---

## Phase 3: Implement Correct Recursive Semantics (5-6 hours)

### Objectives
- Fix the core recursive reduction issue
- Ensure consistent constraint generation and evaluation
- Use custom quantifiers for predictability

### Tasks

#### 3.1 Fix Atomic Reduction in semantic.py
```python
def true_at(self, sentence, eval_point):
    if sentence.sentence_letter is not None:
        # Use unique variable name to avoid conflicts
        v = z3.BitVec(f"v_atom_{id(sentence)}_{self.counter}", self.N)
        self.counter += 1
        return Exists([v], z3.And(
            self.verify(v, sentence.sentence_letter),
            self.is_part_of(v, eval_point["world"])
        ))
    else:
        return sentence.operator.true_at(*sentence.arguments, eval_point)
```

#### 3.2 Fix extended_verify in semantic.py
```python
def extended_verify(self, state, sentence, eval_point):
    if sentence.sentence_letter is not None:
        return self.verify(state, sentence.sentence_letter)
    else:
        return sentence.operator.extended_verify(state, *sentence.arguments, eval_point)
```

#### 3.3 Update Exclusion Operator
- Ensure unique Skolem function names
- Use custom quantifiers (Exists/ForAll from utils)
- Implement three conditions correctly
- Remove find_verifiers method (or fix to match constraints)

#### 3.4 Fix Other Operators
- UniAndOperator: Ensure proper recursive calls
- UniOrOperator: Ensure proper recursive calls  
- UniIdentityOperator: Fix extended_verify implementation

### Deliverables
- Corrected true_at implementation
- Corrected extended_verify implementation
- Updated operator implementations
- Proper Skolem function management

### Success Criteria
- [ ] Atomic formulas reduce to verifier existence
- [ ] All operators properly recursive
- [ ] Skolem functions have unique names
- [ ] Custom quantifiers used consistently

---

## Phase 4: Testing and Validation (3-4 hours)

### Objectives
- Verify false premise issue is resolved
- Ensure no regressions
- Document improvements

### Tasks

#### 4.1 Run Comprehensive Tests
- Test all 34 examples
- Focus on the 8 problematic examples
- Verify premise_behavior and conclusion_behavior
- Check for new issues

#### 4.2 Performance Analysis
- Measure execution time
- Compare with baseline
- Identify any performance bottlenecks
- Document memory usage

#### 4.3 Debug Remaining Issues
- Add detailed logging if issues persist
- Trace constraint generation
- Verify Z3 model evaluation
- Fix any edge cases

#### 4.4 Create Validation Report
- Document which examples are fixed
- Note any remaining issues
- Create `refactored_results.json`
- Compare with baseline

### Deliverables  
- Test results for all examples
- Performance comparison
- `refactored_results.json`
- Validation report

### Success Criteria
- [ ] No false premises in any example
- [ ] No true conclusions where unexpected
- [ ] Performance acceptable
- [ ] All tests pass

---

## Phase 5: Optimization and Documentation (2-3 hours)

### Objectives
- Optimize performance if needed
- Document the solution
- Prepare for production use

### Tasks

#### 5.1 Performance Optimization
- Profile slow examples
- Consider caching strategies
- Optimize Skolem function creation
- Add CD-style optimizations if beneficial

#### 5.2 Code Documentation
- Add comprehensive docstrings
- Document the recursive reduction strategy
- Explain Skolem function usage
- Create usage examples

#### 5.3 Update Project Documentation
- Update README.md with new approach
- Document in findings.md
- Create migration guide from old code
- Update theory documentation

#### 5.4 Cleanup
- Remove old backup files
- Remove unused imports
- Run linting
- Ensure code follows style guide

### Deliverables
- Optimized implementation
- Complete documentation
- Updated project files
- Clean codebase

### Success Criteria
- [ ] Performance meets requirements
- [ ] Documentation complete
- [ ] Code follows style guide
- [ ] Ready for use

---

## Risk Mitigation

### If False Premises Persist
1. Add exhaustive logging to trace exact constraint generation
2. Compare constraints between generation and evaluation
3. Check for variable name conflicts
4. Verify quantifier expansion

### If Performance Degrades
1. Start with small N values
2. Consider hybrid approach for large domains
3. Cache computed values where possible
4. Profile to find bottlenecks

### If Integration Breaks
1. Maintain backward compatibility temporarily
2. Add adapter layer if needed
3. Update tests incrementally
4. Document breaking changes

## Success Metrics

1. **Correctness**: Zero examples with false premises or true conclusions
2. **Performance**: Average execution time < 1 second per example
3. **Simplicity**: Single strategy, clear code structure
4. **Maintainability**: Well-documented, testable implementation

## Timeline

- Phase 1: 3-4 hours (Analysis and Preparation)
- Phase 2: 4-5 hours (Simplify to Single Strategy)
- Phase 3: 5-6 hours (Implement Correct Recursive Semantics)
- Phase 4: 3-4 hours (Testing and Validation)
- Phase 5: 2-3 hours (Optimization and Documentation)

**Total: 17-22 hours** (2-3 days of focused work)

## Key Differences from Previous Approach

1. **Working with current modules** instead of old ones
2. **Simplifying first** before fixing semantics
3. **Single strategy focus** instead of maintaining all
4. **Custom quantifiers** for predictable behavior
5. **Emphasis on testing** throughout each phase

This approach learns from the previous refactoring attempt while adapting to the current codebase structure.