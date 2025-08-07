# Implementation Plan 009: Fresh ModelConstraints for Iterator

[← Back to Specs](../README.md) | [Plans Index](README.md) | [Debug Analyses →](../debug/README.md) | [Findings →](../findings/README.md)

## Overview

This plan details the implementation of Approach 1 from the iterator fix research: creating fresh ModelConstraints for each iterated model. This ensures that constraints always match the model being evaluated, guaranteeing that premises remain true and conclusions remain false across all iterations.

### Context

**Problem**: The ModelIterator currently reuses ModelConstraints from MODEL 1 when generating MODEL 2+, causing constraint mismatches that lead to false premises and true conclusions in iterated models.

**Solution**: Create fresh ModelConstraints for each iteration, ensuring the verify/falsify functions used in constraint generation match the current model.

### Approach

Following the project's **Test-Driven Development** approach and **NO BACKWARDS COMPATIBILITY** principle, this implementation will break compatibility for cleaner architecture.

## Key Requirements

### Core Principles

1. **NO BACKWARDS COMPATIBILITY**: Remove all legacy code paths and update all call sites
2. **Test-Driven Development**: Write failing tests first that define desired behavior
3. **Fail Fast**: Explicit errors when requirements aren't met, no silent fallbacks
4. **Theory Agnostic**: Core framework changes must work with all semantic theories

## Objectives

1. **Primary**: Fix iterator constraint preservation issue where MODEL 2+ violate countermodel requirements
2. **Architecture**: Clean design with no optional parameters or compatibility layers
3. **Testing**: Write tests first that define desired behavior
4. **Performance**: Ensure iterator remains performant for typical use cases

## Technical Design

The implementation creates fresh ModelConstraints for each iterated model by extracting the verify/falsify function values from the current Z3 model and using them to initialize new semantics instances.

### Core Changes

#### 1. Extend ModelStructure Interface

Add methods to ModelStructure to support constraint regeneration:

```python
class ModelStructure:
    def get_verify_falsify_state(self):
        """Extract current verify/falsify function values for all sentence letters.
        
        Returns:
            dict: Mapping of (state, letter) -> (verify_value, falsify_value)
        """
        state_map = {}
        for letter in self.sentence_letters:
            for state in range(2**self.N):
                verify_val = self.z3_model.eval(
                    self.semantics.verify(state, letter.sentence_letter),
                    model_completion=True
                )
                falsify_val = self.z3_model.eval(
                    self.semantics.falsify(state, letter.sentence_letter),
                    model_completion=True
                )
                state_map[(state, letter.sentence_letter)] = (verify_val, falsify_val)
        return state_map
    
    def create_constrained_semantics(self, verify_falsify_state):
        """Create semantics instance with specific verify/falsify values.
        
        Args:
            verify_falsify_state: Dict from get_verify_falsify_state()
            
        Returns:
            Semantics instance with constrained functions
        """
        semantics = self.semantics.__class__(self.settings)
        # Initialize with specific verify/falsify values
        semantics.initialize_from_state(verify_falsify_state)
        return semantics
```

#### 2. Modify Iterator's _build_new_model_structure

Replace the current method with one that creates fresh constraints:

```python
def _build_new_model_structure(self, z3_model):
    """Build a new model structure with fresh constraints.
    
    This creates new ModelConstraints using the current model's verify/falsify
    functions, ensuring constraint consistency.
    """
    try:
        # Extract settings and theory components
        original_build = self.build_example
        settings = original_build.settings
        
        # Create fresh syntax (reuses sentence parsing)
        syntax = Syntax(
            list(original_build.syntax.premises_list),
            list(original_build.syntax.conclusions_list),
            original_build.semantic_theory.get("operators")
        )
        
        # Create new semantics with current model's functions
        semantics_class = original_build.semantic_theory["semantics"]
        semantics = semantics_class(settings)
        
        # CRITICAL: Initialize semantics with current model's verify/falsify
        if hasattr(original_build.model_structure, 'get_verify_falsify_state'):
            # For MODEL 2+, constrain to current model's functions
            verify_falsify_state = self._extract_verify_falsify_from_z3(z3_model)
            semantics.initialize_from_state(verify_falsify_state)
        
        # Create fresh ModelConstraints with current context
        proposition_class = original_build.semantic_theory["proposition"]
        model_constraints = ModelConstraints(
            settings,
            syntax,
            semantics,
            proposition_class
        )
        
        # Create new model structure
        model_class = original_build.semantic_theory["model"]
        new_structure = model_class(model_constraints, settings)
        
        # Set the Z3 model
        new_structure.z3_model = z3_model
        new_structure.z3_model_status = True
        new_structure.satisfiable = True
        new_structure.solved = True
        
        # Initialize Z3-dependent attributes
        self._initialize_z3_dependent_attributes(new_structure, z3_model)
        
        # Interpret sentences with fresh constraints
        new_structure.interpret(new_structure.premises + new_structure.conclusions)
        
        return new_structure
        
    except Exception as e:
        logger.error(f"Error building new model structure: {str(e)}")
        import traceback
        logger.error(f"Full traceback:\n{traceback.format_exc()}")
        return None

def _extract_verify_falsify_from_z3(self, z3_model):
    """Extract verify/falsify values from Z3 model.
    
    Returns:
        dict: Mapping of (state, letter) -> (verify_value, falsify_value)
    """
    state_map = {}
    original_constraints = self.build_example.model_constraints
    
    for letter in original_constraints.sentence_letters:
        for state in range(2**original_constraints.semantics.N):
            verify_val = z3_model.eval(
                original_constraints.semantics.verify(state, letter),
                model_completion=True
            )
            falsify_val = z3_model.eval(
                original_constraints.semantics.falsify(state, letter),
                model_completion=True
            )
            state_map[(state, letter)] = (
                z3.is_true(verify_val),
                z3.is_true(falsify_val)
            )
    
    return state_map
```

#### 3. Update Semantics Base Class

Add initialization method to SemanticDefaults:

```python
class SemanticDefaults:
    def initialize_from_state(self, verify_falsify_state):
        """Initialize verify/falsify functions from a saved state.
        
        This is used by the iterator to ensure MODEL 2+ use
        their own verify/falsify functions when building constraints.
        
        Args:
            verify_falsify_state: Dict mapping (state, letter) -> (verify, falsify)
        """
        # Store state for use in constraint generation
        self._verify_falsify_state = verify_falsify_state
        
        # Override verify/falsify to use stored values
        self._original_verify = self.verify
        self._original_falsify = self.falsify
        
        def constrained_verify(state, letter):
            key = (state, letter)
            if key in self._verify_falsify_state:
                return self._verify_falsify_state[key][0]
            return self._original_verify(state, letter)
        
        def constrained_falsify(state, letter):
            key = (state, letter)
            if key in self._verify_falsify_state:
                return self._verify_falsify_state[key][1]
            return self._original_falsify(state, letter)
        
        # Replace methods
        self.verify = constrained_verify
        self.falsify = constrained_falsify
```

#### 4. Modify Iterator Initialization

Update the iterator to track necessary components:

```python
def __init__(self, build_example, max_iterations=3):
    # ... existing initialization ...
    
    # Store theory components for model building
    self.semantic_theory = build_example.semantic_theory
    self.premises_list = list(build_example.syntax.premises_list)
    self.conclusions_list = list(build_example.syntax.conclusions_list)
    
    # Track whether we need fresh constraints
    self.use_fresh_constraints = build_example.settings.get(
        'iterator_fresh_constraints', True
    )
```

## Implementation Strategy

### Implementation Phases (TDD Approach)

#### Phase 1: Write Failing Tests (Day 1)

Following **Test-Driven Development**, we start by writing tests that define the desired behavior:

1. **Create test file**: `src/model_checker/iterate/tests/test_constraint_preservation.py`

```python
import unittest
from model_checker.iterate import ModelIterator
# Example: from model_checker.theory_lib.logos import logos_theory

class TestConstraintPreservation(unittest.TestCase):
    """Test that iterator preserves countermodel properties."""
    
    def test_premises_remain_true_in_all_models(self):
        """All MODEL 2+ must have true premises at evaluation world."""
        # This test should FAIL initially
        build_example = self._create_example(['A'], [], iterate=3)
        models = build_example.get_all_models()
        
        for i, model in enumerate(models):
            with self.subTest(model=i+1):
                # Check premise is true at evaluation world
                eval_world = model.main_point['world']
                premise_truth = model.evaluate_at_world('A', eval_world)
                self.assertTrue(premise_truth, 
                    f"Premise A should be true in MODEL {i+1}")
    
    def test_conclusions_remain_false_in_all_models(self):
        """All MODEL 2+ must have false conclusions at evaluation world."""
        build_example = self._create_example(['(A \\\\wedge B)'], ['C'], iterate=3)
        models = build_example.get_all_models()
        
        for i, model in enumerate(models):
            with self.subTest(model=i+1):
                eval_world = model.main_point['world']
                conclusion_truth = model.evaluate_at_world('C', eval_world)
                self.assertFalse(conclusion_truth, 
                    f"Conclusion C should be false in MODEL {i+1}")
```

2. **Create dual test validation script**: `test_iterator_fix.py`

```python
#!/usr/bin/env python3
"""Dual testing validation for iterator fix."""

import subprocess
import sys

def run_formal_tests():
    """Run formal test suite."""
    print("=== Running formal tests ===")
    result = subprocess.run([
        'python', '-m', 'pytest', 
        'src/model_checker/iterate/tests/test_constraint_preservation.py',
        '-v'
    ])
    return result.returncode == 0

def run_cli_tests():
    """Run dev_cli.py validation."""
    print("\n=== Running CLI validation ===")
    
    test_cases = [
        # Test with different iteration counts
        ('./dev_cli.py', '-i', '2', 'test_minimal_iterator.py'),
        ('./dev_cli.py', '-i', '3', 'test_minimal_iterator.py'),
        
        # Test all theories
        # Theory-specific examples would go here:
        # ('./dev_cli.py', '-i', '2', 'src/model_checker/theory_lib/[theory]/examples.py'),
    ]
    
    for cmd in test_cases:
        result = subprocess.run(cmd, capture_output=True, text=True)
        # Check for violations
        if 'False in' in result.stdout and 'premise' in result.stdout.lower():
            print(f"FAIL: {' '.join(cmd)} - Found false premise")
            return False
        if 'True in' in result.stdout and 'conclusion' in result.stdout.lower():
            print(f"FAIL: {' '.join(cmd)} - Found true conclusion")
            return False
    
    return True

if __name__ == '__main__':
    formal_ok = run_formal_tests()
    cli_ok = run_cli_tests()
    
    if formal_ok and cli_ok:
        print("\nAll tests passed")
        sys.exit(0)
    else:
        print("\nTests failed")
        sys.exit(1)
```

#### Phase 2: Core Infrastructure (Days 2-3)

**NO DECORATORS** - Following style guide, we use explicit methods:

1. **Extend ModelStructure** (fail fast, explicit parameters)

```python
class ModelStructure:
    def extract_verify_falsify_state(self):
        """Extract current verify/falsify function values.
        
        NO BACKWARDS COMPATIBILITY - This is a new required method.
        
        Returns:
            dict: Mapping of (state, letter) -> (verify_value, falsify_value)
            
        Raises:
            RuntimeError: If Z3 model not available
        """
        if not self.z3_model:
            raise RuntimeError("Cannot extract state without Z3 model")
            
        state_map = {}
        for letter in self.sentence_letters:
            for state in range(2**self.N):
                verify_val = self.z3_model.eval(
                    self.semantics.verify(state, letter.sentence_letter),
                    model_completion=True
                )
                falsify_val = self.z3_model.eval(
                    self.semantics.falsify(state, letter.sentence_letter),
                    model_completion=True
                )
                state_map[(state, letter.sentence_letter)] = (
                    z3.is_true(verify_val),
                    z3.is_true(falsify_val)
                )
        return state_map
```

2. **Extend SemanticDefaults** (no optional parameters)

```python
class SemanticDefaults:
    def initialize_with_state(self, verify_falsify_state, sentence_letters):
        """Initialize with specific verify/falsify values.
        
        Args:
            verify_falsify_state: Required dict from extract_verify_falsify_state
            sentence_letters: Required list of sentence letters
            
        NO OPTIONAL PARAMETERS - Both arguments are required.
        """
        self._constrained_state = verify_falsify_state
        self._sentence_letters = sentence_letters
        
        # Store original functions
        self._unconstrained_verify = self.verify
        self._unconstrained_falsify = self.falsify
        
        # Replace with constrained versions
        self.verify = self._make_constrained_verify()
        self.falsify = self._make_constrained_falsify()
```

#### Phase 3: Iterator Refactoring (Days 4-5)

**BREAK COMPATIBILITY** - Remove old behavior entirely:

1. **Replace `_build_new_model_structure`** completely:

```python
def _build_new_model_structure(self, z3_model):
    """Build model with fresh constraints.
    
    NO BACKWARDS COMPATIBILITY - Always uses fresh constraints.
    """
    # Extract current state
    state = self._extract_current_state(z3_model)
    
    # Create fresh components
    syntax = self._create_fresh_syntax()
    semantics = self._create_constrained_semantics(state)
    
    # Build fresh constraints
    model_constraints = ModelConstraints(
        self.settings,
        syntax,
        semantics,
        self.proposition_class
    )
    
    # Create model structure
    model_structure = self.model_class(model_constraints, self.settings)
    
    # Set Z3 model and initialize
    self._apply_z3_model(model_structure, z3_model)
    
    return model_structure
```

2. **Remove configuration options** - No `iterator_fresh_constraints` setting

#### Phase 4: Validation & Performance (Days 6-7)

1. **Run dual testing methodology**:

```bash
# Method 1: Formal tests
./run_tests.py --package --components iterate -v

# Method 2: CLI validation  
./scripts/test_iterator_fix.py
```

2. **Performance validation**:

```python
class TestIteratorPerformance(unittest.TestCase):
    """Ensure performance remains acceptable."""
    
    def test_iteration_time_reasonable(self):
        """Iterator should complete in reasonable time."""
        import time
        
        start = time.time()
        build_example = self._create_large_example(iterate=10)
        duration = time.time() - start
        
        # Should complete 10 iterations in under 30 seconds
        self.assertLess(duration, 30.0, 
            f"10 iterations took {duration:.1f}s (limit: 30s)")
```

#### Phase 5: Documentation & Cleanup (Day 8)

1. **Update documentation** (no mention of backwards compatibility):
   - Update iterate/README.md
   - Add to findings/020_iterator_fresh_constraints.md
   - Update CHANGELOG.md with breaking change

2. **Remove all old code paths** - No deprecated methods

## Testing Strategy

### Dual Testing Methodology

The project uses a dual testing approach to ensure correctness:

1. **Formal Unit Tests**: Traditional test suite with assertions
2. **CLI Validation**: Using dev_cli.py to verify real-world behavior

### Testing Strategy (Following Dual Testing Methodology)

### Required Test Files

1. **Unit Tests**: `src/model_checker/iterate/tests/`
   - `test_constraint_preservation.py` - Core functionality
   - `test_verify_falsify_extraction.py` - State extraction
   - `test_fresh_constraints.py` - Constraint generation
   - `test_performance.py` - Performance benchmarks

2. **Example Tests**: Update existing theory tests
   - Add iteration-specific test cases
   - Verify countermodel preservation

### Test Patterns (NO DECORATORS)

```python
class TestIteratorConstraints(unittest.TestCase):
    """Test iterator constraint handling."""
    
    def setUp(self):
        """Explicit setup - no decorators."""
        self.test_settings = {
            'N': 2,
            'contingent': False,
            'non_null': True,
            'non_empty': True,
            'max_time': 10
        }
        
    def test_verify_falsify_extraction(self):
        """Test extraction fails fast without Z3 model."""
        model_structure = ModelStructure()
        
        # Should raise RuntimeError - fail fast
        with self.assertRaises(RuntimeError) as context:
            model_structure.extract_verify_falsify_state()
            
        self.assertIn("Cannot extract state", str(context.exception))
```

### Dual Testing Validation

Following TESTS.md requirements:

```bash
# Before implementation - capture baseline
./dev_cli.py -i 3 src/model_checker/theory_lib/[theory]/examples.py > baseline.txt 2>&1

# After each phase - check for regressions
./dev_cli.py -i 3 src/model_checker/theory_lib/[theory]/examples.py > current.txt 2>&1
diff baseline.txt current.txt

# Check for new warnings/errors
grep -E "WARNING|Error|AttributeError" current.txt  # Should be empty
```

### Critical Testing Points

1. **Iterator functionality** - Test with `-i 1`, `-i 2`, `-i 3`
2. **Constraint generation** - Use `-p` flag to verify
3. **Cross-theory compatibility** - Test all theories
4. **No new warnings** - Any WARNING indicates regression

## Implementation Guidelines

### Design Principles

1. **Break Compatibility**: 
   - Remove ALL old code paths
   - No optional parameters
   - Update all call sites

2. **Fail Fast**:
   - Explicit errors for missing requirements
   - No silent fallbacks
   - Clear error messages

3. **Explicit Parameters**:
   - All methods require explicit arguments
   - No hidden state modifications
   - Clear data flow

### Code Style (Following STYLE_GUIDE.md)

```python
# Good - Explicit, no decorators
def extract_verify_falsify_state(self):
    if not self.z3_model:
        raise RuntimeError("Cannot extract state without Z3 model")
    return state_map

# Bad - Would use decorator
# @property
# def verify_falsify_state(self):
#     return self._state or self._compute_state()
```

### Error Handling

```python
# Good - Specific, actionable
if not self.sentence_letters:
    raise ValueError(
        "No sentence letters found. "
        "Ensure ModelConstraints was properly initialized with syntax."
    )

# Bad - Generic
if not self.sentence_letters:
    raise Exception("Invalid state")

## Validation and Success Metrics

### Success Metrics

1. **Bug Fix**: No MODEL 2+ with false premises or true conclusions
2. **Performance**: Iterator completes within 2x original time
3. **Compatibility**: All existing tests pass
4. **Code Quality**: Clean, documented implementation

## Timeline

- **Days 1-2**: Core infrastructure
- **Days 3-5**: Iterator refactoring
- **Days 6-7**: Testing and validation
- **Day 8**: Documentation and cleanup

Total estimated time: 8 days

## Future Enhancements

1. **Lazy Constraint Generation**: Build constraints only when needed
2. **Constraint Caching**: Reuse structural constraints across iterations
3. **Parallel Model Generation**: Use multiple Z3 instances
4. **Smart Function Detection**: Only regenerate affected constraints

## Conclusion

This implementation plan provides a systematic approach to fixing the iterator constraint preservation issue by creating fresh ModelConstraints for each iteration. The solution maintains theoretical correctness while minimizing performance impact through careful design and optimization.

---

[← Back to Specs](../README.md) | [Plans Index](README.md) | [Debug Analyses →](../debug/README.md) | [Findings →](../findings/README.md)