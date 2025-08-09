# Implementation Plan: Iterator Refactor to Direct Constraint Approach

## Overview

This plan outlines the refactoring of the iterator subsystem to follow the successful approach used on the master branch, eliminating the problematic verify/falsify state transfer mechanism that causes empty MODEL 2s.

## Motivation

The current pattern-based iterator implementation fails because:
1. `_extract_verify_falsify_from_z3` tries to evaluate MODEL 1's Z3 expressions against MODEL 2's model
2. Cross-model Z3 variable references result in empty verifier/falsifier sets
3. The `initialize_with_state` mechanism violates Z3's variable namespace separation

The master branch approach succeeds by:
1. Never transferring verify/falsify state between models
2. Creating constraints using fresh Z3 variables for MODEL 2
3. Comparing against concrete boolean values from MODEL 1

## Success Criteria

1. All theories (logos, exclusion, imposition, bimodal) generate valid MODEL 2s with proper verifier/falsifier sets
2. No cross-model Z3 variable references
3. Clean separation between MODEL 1 and MODEL 2 contexts
4. Passing all existing iterator tests
5. **Dual testing validation** with both test runners and dev_cli.py
6. **No regressions** in constraint output or model generation

## Design Philosophy Alignment

Following [CLAUDE.md Core Development Principles](../CLAUDE.md#core-development-principles):
- **NO BACKWARDS COMPATIBILITY**: Remove old pattern approach completely
- **Fail Fast**: Let errors surface naturally, no masking with defaults
- **Test-Driven Development**: Write tests first for each phase
- **No Optional Parameters**: Update all call sites when changing interfaces

## Implementation Phases

### Phase 1: Remove State Transfer Mechanism (TDD)
**Goal**: Remove the problematic verify/falsify state transfer

**Test First**:
```python
# src/model_checker/iterate/tests/test_core_no_state_transfer.py
def test_build_model_without_state_transfer(self):
    """Test that MODEL 2 builds without verify/falsify state transfer."""
    # Create iterator with valid MODEL 1
    iterator = BaseModelIterator(self.valid_example)
    
    # Mock Z3 model for MODEL 2
    z3_model = Mock()
    
    # Build should succeed without calling initialize_with_state
    with patch.object(SemanticDefaults, 'initialize_with_state') as mock_init:
        new_structure = iterator._build_new_model_structure(z3_model)
        mock_init.assert_not_called()
    
    # Structure should be valid
    self.assertIsNotNone(new_structure)
    self.assertTrue(hasattr(new_structure, 'z3_model'))
```

**Implementation Tasks**:
1. Remove `_extract_verify_falsify_from_z3` from `core.py`
2. Remove `initialize_with_state` calls from `_build_new_model_structure`
3. Remove `initialize_with_state` and related methods from `SemanticDefaults`
4. Update `_build_new_model_structure` to build MODEL 2 without state transfer

**Validation**: 
- Run test to ensure it passes
- Use dev_cli.py to verify MODEL 2 builds (may have empty verifiers initially)

### Phase 2: Implement Abstract Constraint Methods (TDD)
**Goal**: Add abstract methods to BaseModelIterator for theory-specific constraints

**Test First**:
```python
# src/model_checker/iterate/tests/test_core_abstract_methods.py
def test_abstract_methods_required(self):
    """Test that BaseModelIterator requires theory-specific methods."""
    # Attempt to instantiate BaseModelIterator should fail
    with self.assertRaises(TypeError) as context:
        iterator = BaseModelIterator(self.valid_example)
    
    # Should indicate missing abstract methods
    error_msg = str(context.exception)
    self.assertIn("_create_difference_constraint", error_msg)
    self.assertIn("_create_non_isomorphic_constraint", error_msg)
    self.assertIn("_create_stronger_constraint", error_msg)

def test_constraint_methods_called_correctly(self):
    """Test that constraint methods are called with correct arguments."""
    # Create concrete implementation
    class TestIterator(BaseModelIterator):
        def _create_difference_constraint(self, previous_models):
            self.diff_called = True
            self.diff_args = previous_models
            return z3.BoolVal(True)
            
        def _create_non_isomorphic_constraint(self, z3_model):
            self.non_iso_called = True
            self.non_iso_args = z3_model
            return z3.BoolVal(True)
            
        def _create_stronger_constraint(self, isomorphic_model):
            self.stronger_called = True
            self.stronger_args = isomorphic_model
            return z3.BoolVal(True)
    
    iterator = TestIterator(self.valid_example)
    # Trigger constraint creation
    constraints = iterator._create_extended_constraints()
    
    # Verify methods were called
    self.assertTrue(iterator.diff_called)
    self.assertTrue(iterator.non_iso_called)
```

**Implementation Tasks**:
1. Add abstract method `_create_difference_constraint(previous_models)`
2. Add abstract method `_create_non_isomorphic_constraint(z3_model)`
3. Add abstract method `_create_stronger_constraint(isomorphic_model)`
4. Update `_create_extended_constraints` to use these methods

**Validation**:
- Run unit tests: `./run_tests.py --package --components iterate`
- Verify abstract class cannot be instantiated directly
- Check that all theory iterators must implement these methods

### Phase 3: Implement Theory-Specific Constraints (TDD)
**Goal**: Implement constraint methods for each theory

**Test First** (Example for Logos):
```python
# src/model_checker/theory_lib/logos/tests/test_iterate_constraints.py
def test_difference_constraint_creates_distinct_model(self):
    """Test that difference constraint produces structurally different MODEL 2."""
    # Build MODEL 1
    model1 = BuildExample("test", logos_theory)
    model1.premises = ["A", "(A \\rightarrow B)"]
    model1.conclusions = ["B"]
    model1.set_settings({'N': 3, 'expectation': False})
    result1 = model1.run_single_test()
    
    # Create iterator and generate MODEL 2
    iterator = LogosModelIterator(model1)
    model2_structure = iterator.generate_next_model()
    
    # MODEL 2 should be structurally different
    self.assertNotEqual(
        len(model1.structure.z3_world_states),
        len(model2_structure.z3_world_states),
        "MODEL 2 should have different world count"
    )

def test_verify_values_differ_between_models(self):
    """Test that verify values differ between MODEL 1 and MODEL 2."""
    # Create MODEL 1 with known verify pattern
    model1 = self._create_test_model()
    iterator = LogosModelIterator(model1)
    
    # Generate MODEL 2
    model2_structure = iterator.generate_next_model()
    
    # Check that at least one verify value differs
    differences = 0
    for state in model1.structure.world_states:
        for atom in ['A', 'B']:
            val1 = model1.structure.z3_model.eval(
                model1.semantics.verify(state, atom)
            )
            val2 = model2_structure.z3_model.eval(
                model2_structure.semantics.verify(state, atom)
            )
            if val1 != val2:
                differences += 1
    
    self.assertGreater(differences, 0, 
        "MODEL 2 should have different verify values")
```

**Implementation Tasks**:
1. **Logos** (`logos/iterate.py`):
   - Implement `_create_difference_constraint` with smart ordering
   - Add world count, letter value, and structural constraints
   - Use `semantics.verify()` for fresh variables

2. **Exclusion** (`exclusion/iterate.py`):
   - Implement unilateral semantics constraints
   - Use `semantics.verify()` only (no falsify)
   - Handle excludes relation

3. **Imposition** (`imposition/iterate.py`):
   - Implement imposition relation constraints
   - Handle constitutive operators

4. **Bimodal** (`bimodal/iterate.py`):
   - Implement temporal and modal constraints
   - Handle two-dimensional semantics

**Validation**: 
- Run theory-specific tests: `./run_tests.py logos exclusion imposition bimodal`
- Use dev_cli.py with iterations: `./dev_cli.py -i 2 src/model_checker/theory_lib/*/examples.py`
- Verify no empty MODEL 2 warnings

### Phase 4: Remove Pattern-Based Infrastructure (TDD)
**Goal**: Clean up unused pattern code

**Test First**:
```python
# src/model_checker/iterate/tests/test_no_pattern_dependency.py
def test_no_pattern_imports(self):
    """Test that iterate package has no pattern dependencies."""
    # Check core.py doesn't import patterns
    import inspect
    import model_checker.iterate.core as core_module
    
    source = inspect.getsource(core_module)
    self.assertNotIn('import patterns', source)
    self.assertNotIn('from .patterns', source)
    self.assertNotIn('StructuralPattern', source)

def test_no_pattern_attributes(self):
    """Test that BaseModelIterator has no pattern-related attributes."""
    from model_checker.iterate import BaseModelIterator
    
    # Check class doesn't have pattern attributes
    iterator_attrs = dir(BaseModelIterator)
    self.assertNotIn('found_patterns', iterator_attrs)
    self.assertNotIn('_extract_pattern', iterator_attrs)
    
def test_pattern_module_removed(self):
    """Test that patterns.py module doesn't exist."""
    with self.assertRaises(ImportError):
        from model_checker.iterate import patterns
```

**Implementation Tasks**:
1. Remove `patterns.py` module entirely
2. Remove pattern imports from `core.py`
3. Remove `found_patterns` tracking from BaseModelIterator
4. Update any remaining pattern references

**Validation**:
- Run cleanup verification: `find . -name "*pattern*" -path "*/iterate/*"`
- Ensure all tests pass: `./run_tests.py`
- Check no regression with dev_cli.py

### Phase 5: Optimize Constraint Generation (TDD)
**Goal**: Implement smart constraint ordering for performance

**Test First**:
```python
# src/model_checker/iterate/tests/test_constraint_optimization.py
def test_constraint_priority_ordering(self):
    """Test that constraints are generated in priority order."""
    class TestIterator(LogosModelIterator):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            self.generation_order = []
            
        def _create_world_count_constraint(self, previous_models):
            self.generation_order.append('world_count')
            return super()._create_world_count_constraint(previous_models)
            
        def _create_letter_value_constraint(self, previous_models):
            self.generation_order.append('letter_value')
            return super()._create_letter_value_constraint(previous_models)
            
        def _create_structural_constraint(self, previous_models):
            self.generation_order.append('structural')
            return super()._create_structural_constraint(previous_models)
    
    iterator = TestIterator(self.test_model)
    iterator._create_difference_constraint([self.test_model])
    
    # Verify priority order (world_count first, then letter_value, then structural)
    expected_order = ['world_count', 'letter_value', 'structural']
    self.assertEqual(iterator.generation_order[:3], expected_order)

def test_early_termination_with_constraint_limit(self):
    """Test that constraint generation stops at configured limit."""
    # Configure constraint limit
    settings = {'N': 3, 'max_constraints': 5}
    model = self._create_test_model_with_settings(settings)
    
    iterator = LogosModelIterator(model)
    constraints = iterator._create_difference_constraint([model])
    
    # Count actual constraints generated
    constraint_count = self._count_constraints(constraints)
    self.assertLessEqual(constraint_count, 5, 
        "Should not exceed max_constraints limit")
```

**Implementation Tasks**:
1. Add constraint generator priority system (as in master logos)
2. Implement early termination when enough constraints
3. Add configurable constraint limits via settings
4. Profile and optimize slow constraint generation

**Validation**:
- Run performance tests: `./run_tests.py --performance`
- Profile iteration time: `python -m cProfile dev_cli.py -i 3 examples.py`
- Compare with baseline performance

### Phase 6: Documentation and Testing (TDD)
**Goal**: Ensure comprehensive documentation and test coverage

**Test First**:
```python
# src/model_checker/iterate/tests/test_documentation.py
def test_iterator_docstrings_complete(self):
    """Test that all iterator classes have proper docstrings."""
    from model_checker.iterate import BaseModelIterator
    
    # Check base class documentation
    self.assertIsNotNone(BaseModelIterator.__doc__)
    self.assertIn("direct constraint", BaseModelIterator.__doc__.lower())
    self.assertIn("z3 variable", BaseModelIterator.__doc__.lower())
    
    # Check key methods documented
    methods = ['_create_difference_constraint', 
               '_create_non_isomorphic_constraint',
               '_create_stronger_constraint']
    
    for method_name in methods:
        method = getattr(BaseModelIterator, method_name, None)
        self.assertIsNotNone(method.__doc__, 
            f"{method_name} should have docstring")

# src/model_checker/iterate/tests/test_multi_model_iteration.py  
def test_three_model_iteration(self):
    """Test generating three distinct models in sequence."""
    # Create MODEL 1
    model1 = self._create_test_model()
    iterator = LogosModelIterator(model1)
    
    # Generate MODEL 2
    model2_structure = iterator.generate_next_model()
    self.assertIsNotNone(model2_structure)
    
    # Generate MODEL 3 (should differ from both MODEL 1 and MODEL 2)
    model3_structure = iterator.generate_next_model()
    self.assertIsNotNone(model3_structure)
    
    # Verify all three models are distinct
    self._assert_models_distinct([model1, model2_structure, model3_structure])
```

**Implementation Tasks**:
1. Update iterator docstrings explaining direct constraint approach
2. Add tests for each theory's constraint methods
3. Document Z3 variable namespace separation principle
4. Add integration tests for multi-model iteration

**Validation**:
- Documentation coverage: `grep -r "__doc__" src/model_checker/iterate/`
- Test coverage report: `pytest --cov=model_checker.iterate`
- Final regression test: `./scripts/dual_test_refactoring.sh`

## Technical Details

### Key Architectural Change

**Before** (Pattern-based):
```python
# Problematic: tries to evaluate MODEL 1's expressions in MODEL 2
verify_val = z3_model.eval(
    original_constraints.semantics.verify(state, letter_str),
    model_completion=True
)
```

**After** (Direct constraints):
```python
# Correct: fresh Z3 variable compared to concrete value
prev_verify = prev_model.eval(semantics.verify(state, atom), model_completion=True)
constraints.append(semantics.verify(state, atom) != prev_verify)
```

### Example Logos Implementation

```python
def _create_difference_constraint(self, previous_models):
    """Create constraints requiring difference from previous models."""
    constraint_generators = [
        (self._create_world_count_constraint, 1),
        (self._create_letter_value_constraint, 2),
        (self._create_structural_constraint, 3),
    ]
    
    all_constraints = []
    for generator, priority in sorted(constraint_generators, key=lambda x: x[1]):
        constraints = generator(previous_models)
        all_constraints.extend(constraints)
        if len(all_constraints) > 10:  # Early termination
            break
    
    return z3.And(*all_constraints) if all_constraints else z3.BoolVal(True)
```

## Migration Strategy

1. Create feature branch from release_refactor
2. Implement phases incrementally with tests
3. Test each theory individually after Phase 3
4. Run full test suite after each phase
5. Document breaking changes

## Risk Mitigation

1. **Risk**: Breaking existing functionality
   - **Mitigation**: Incremental implementation with tests after each phase

2. **Risk**: Performance regression
   - **Mitigation**: Profile constraint generation, implement smart ordering

3. **Risk**: Theory-specific edge cases
   - **Mitigation**: Extensive testing with known problematic examples

## Rollback Plan

If issues arise:
1. The pattern-based approach can be restored from git history
2. Each phase is atomic and can be reverted independently
3. Feature branch allows safe experimentation

## Success Metrics

1. All example files run successfully with `iterate: 2`
2. No "empty verifier/falsifier" warnings in MODEL 2
3. Performance comparable to master branch
4. Clean test suite with no regressions
5. **All tests written before implementation** (TDD)
6. **Dual validation passes** for all theories

## Timeline

- Phase 1-2: 2 hours (remove problematic code)
- Phase 3: 4 hours (implement theory constraints)
- Phase 4: 1 hour (cleanup)
- Phase 5: 2 hours (optimization)
- Phase 6: 2 hours (documentation/testing)

Total estimate: 11 hours of focused work

## Notes

This plan follows the proven approach from master branch while maintaining the cleaner architecture of the refactored codebase. The key insight is that MODEL 2 must be built with complete independence from MODEL 1's Z3 context, using only concrete values in constraints.

### TDD Workflow Summary

For each phase:
1. **Write tests first** that define the expected behavior
2. **Run tests to see them fail** (red phase)
3. **Implement minimal code** to make tests pass (green phase)
4. **Refactor if needed** while keeping tests green
5. **Validate with dual testing** (test runner + dev_cli.py)

This ensures:
- Clear specification of requirements before coding
- Immediate feedback on implementation correctness
- Comprehensive test coverage from the start
- No regressions during refactoring