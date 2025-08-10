"""
Integration tests for iterator contracts.

These tests ensure that the iterator respects the defined interfaces
and maintains backward compatibility during refactoring.
"""

import pytest
import z3
from unittest.mock import MagicMock
from model_checker.interfaces import ModelAccessor, SolverManager, ConstraintBuilder
from model_checker.builder.module import BuildModule
from model_checker.builder.example import BuildExample
from model_checker.theory_lib.exclusion import get_theory
from model_checker.theory_lib.exclusion.iterate import ExclusionModelIterator


class TestIteratorContracts:
    """Test iterator compliance with interface contracts."""
    
    def test_model_accessor_compatibility(self):
        """Test that ModelAccessor works with existing model structures."""
        # Get exclusion theory
        exclusion_theory = get_theory()
        
        # Create a simple example
        example = BuildExample(
            name="test",
            semantic_theory=exclusion_theory,
            premises=["A"],
            conclusions=["\\neg A"],
            settings={'N': 2}
        )
        
        # Run to get model
        example.run_single_test()
        assert example.model_structure is not None
        
        # Wrap in accessor
        accessor = ModelAccessor(example.model_structure)
        
        # Test basic access methods
        worlds = accessor.get_worlds()
        assert isinstance(worlds, set)
        assert len(worlds) > 0
        
        possible = accessor.get_possible_worlds()
        assert isinstance(possible, set)
        
        verifiers = accessor.get_verifier_sets()
        assert isinstance(verifiers, dict)
        assert 'A' in verifiers
        
        falsifiers = accessor.get_falsifier_sets()
        assert isinstance(falsifiers, dict)
    
    def test_solver_manager_isolation(self):
        """Test that SolverManager properly isolates solver state."""
        # Create base constraints
        x = z3.Bool('x')
        y = z3.Bool('y')
        base_constraints = [x, z3.Not(y)]
        
        manager = SolverManager(base_constraints)
        
        # Check base state
        assert manager.check() == z3.sat
        model = manager.model()
        assert z3.is_true(model.eval(x))
        assert z3.is_false(model.eval(y))
        
        # Test isolated context
        with manager.isolated_context():
            # Add conflicting constraint
            manager.add(y)
            assert manager.check() == z3.unsat
        
        # Verify base state restored
        assert manager.check() == z3.sat
        assert manager.is_clean
    
    def test_constraint_builder_patterns(self):
        """Test common constraint building patterns."""
        builder = ConstraintBuilder("test")
        
        # Test state difference
        states1 = {'a', 'b', 'c'}
        states2 = {'b', 'c', 'd'}
        state_vars = {
            'a': z3.Bool('state_a'),
            'b': z3.Bool('state_b'),
            'c': z3.Bool('state_c'),
            'd': z3.Bool('state_d')
        }
        
        diff_constraint = builder.create_state_difference(states1, states2, state_vars)
        
        # Should require either NOT d or a
        solver = z3.Solver()
        solver.add(diff_constraint)
        assert solver.check() == z3.sat
        
        # If we force same membership, should be unsat
        solver.add(state_vars['a'])
        solver.add(z3.Not(state_vars['d']))
        assert solver.check() == z3.unsat
    
    def test_iterator_with_interfaces(self):
        """Test that iterator can work through interfaces."""
        # Get exclusion theory
        exclusion_theory = get_theory()
        
        # Create example with iteration
        example = BuildExample(
            name="test",
            semantic_theory=exclusion_theory,
            premises=["(A \\vee B)", "\\neg A"],
            conclusions=["B"],
            settings={'N': 3, 'iterate': 2}
        )
        
        # Run initial test
        example.run_single_test()
        assert example.model_structure is not None
        
        # Create iterator
        iterator = ExclusionModelIterator(example)
        
        # Verify iterator can access model through potential interfaces
        # (This tests that iterator doesn't break with our accessor)
        accessor = ModelAccessor(example.model_structure)
        worlds = accessor.get_worlds()
        
        # Run iteration
        models = iterator.iterate()
        assert len(models) == 2  # Should find 2 models
        
        # Verify second model is different
        assert models[1] != models[0]


class TestIteratorRegressions:
    """Regression tests for known iterator issues."""
    
    def test_no_z3_boolean_casting_errors(self):
        """Ensure no 'cannot cast to concrete Boolean' errors."""
        exclusion_theory = get_theory()
        
        example = BuildExample(
            name="test",
            semantic_theory=exclusion_theory,
            premises=["\\neg \\neg A"],
            conclusions=["A"],
            settings={'N': 3, 'iterate': 2}
        )
        
        example.run_single_test()
        iterator = ExclusionModelIterator(example)
        
        # This should not raise Z3 boolean casting errors
        models = iterator.iterate()
        assert len(models) >= 1
    
    def test_constraint_preservation(self):
        """Test that constraints are properly preserved during iteration."""
        exclusion_theory = get_theory()
        
        example = BuildExample(
            name="test",
            semantic_theory=exclusion_theory,
            premises=["A"],
            conclusions=["B"],
            settings={'N': 2, 'iterate': 2}
        )
        
        example.run_single_test()
        iterator = ExclusionModelIterator(example)
        
        # Check that iterator preserves original constraints
        original_constraint_count = len(iterator.original_constraints)
        assert original_constraint_count > 0
        
        # Run iteration
        models = iterator.iterate()
        
        # Solver should still have original constraints
        current_assertions = iterator.solver.assertions()
        assert len(current_assertions) >= original_constraint_count