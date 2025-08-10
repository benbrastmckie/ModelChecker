"""
Integration tests for interface compatibility.

These tests ensure that the new interfaces work correctly
with existing model structures.
"""

import pytest
import z3
from unittest.mock import MagicMock
from model_checker.interfaces import ModelAccessor, SolverManager, ConstraintBuilder


class TestModelAccessor:
    """Test ModelAccessor compatibility with existing structures."""
    
    def test_accessor_with_z3_attributes(self):
        """Test accessor with standard z3_ prefixed attributes."""
        # Create mock model with expected attributes
        mock_model = MagicMock()
        mock_model.z3_world_states = {
            'a': {'world': True, 'possible': True},
            'b': {'world': True, 'possible': False}
        }
        mock_model.z3_possible_states = {'a'}
        mock_model.z3_impossible_states = {'b'}
        mock_model.designated_world = '□'
        mock_model.z3_verify_sets = {'A': {'a'}, 'B': {'b'}}
        mock_model.z3_falsify_sets = {'A': {'b'}, 'B': {'a'}}
        mock_model.z3_model = MagicMock()
        mock_model.solver = z3.Solver()
        
        # Create accessor
        accessor = ModelAccessor(mock_model)
        
        # Test all methods
        assert accessor.get_worlds() == {'a', 'b'}
        assert accessor.get_possible_worlds() == {'a'}
        assert accessor.get_impossible_worlds() == {'b'}
        assert accessor.get_designated_world() == '□'
        assert accessor.get_verifier_sets() == {'A': {'a'}, 'B': {'b'}}
        assert accessor.get_falsifier_sets() == {'A': {'b'}, 'B': {'a'}}
        assert accessor.get_z3_model() is not None
        assert accessor.get_solver() is not None
    
    def test_accessor_fallbacks(self):
        """Test accessor fallback mechanisms."""
        # Create model with alternative attribute names
        mock_model = MagicMock()
        mock_model.world_states = {'x': {}, 'y': {}}
        mock_model.verify_sets = {'P': {'x'}}
        mock_model.falsify_sets = {'P': {'y'}}
        mock_model.stored_solver = z3.Solver()
        
        # Remove z3_ versions to test fallbacks
        del mock_model.z3_world_states
        del mock_model.z3_verify_sets
        del mock_model.z3_falsify_sets
        del mock_model.solver
        
        accessor = ModelAccessor(mock_model)
        
        # Should use fallback attributes
        assert accessor.get_worlds() == {'x', 'y'}
        assert accessor.get_verifier_sets() == {'P': {'x'}}
        assert accessor.get_falsifier_sets() == {'P': {'y'}}
        assert accessor.get_solver() is not None  # Uses stored_solver
    
    def test_accessor_relation_access(self):
        """Test accessing theory-specific relations."""
        # Create a simple class to simulate model
        class MockModel:
            def __init__(self):
                self.z3_part_of = {('a', 'b'), ('b', 'c')}
                self.z3_exclusion = {('x', 'y')}
                self.imposition_relation = {('p', 'q')}
                
            def __getattr__(self, name):
                # Simulate missing attributes
                if name in ['z3_imposition', 'imposition']:
                    raise AttributeError(name)
                raise AttributeError(name)
        
        mock_model = MockModel()
        accessor = ModelAccessor(mock_model)
        
        # Test different relation access patterns
        assert accessor.get_relation('part_of') == {('a', 'b'), ('b', 'c')}
        assert accessor.get_relation('exclusion') == {('x', 'y')}
        assert accessor.get_relation('imposition') == {('p', 'q')}
        assert accessor.get_relation('nonexistent') == set()


class TestSolverManager:
    """Test SolverManager for proper isolation."""
    
    def test_solver_isolation(self):
        """Test that solver operations are isolated."""
        # Create base constraints
        x, y = z3.Bool('x'), z3.Bool('y')
        base = [x, z3.Not(y)]
        
        manager = SolverManager(base)
        
        # Check initial state
        assert manager.check() == z3.sat
        model = manager.model()
        assert z3.is_true(model.eval(x))
        assert z3.is_false(model.eval(y))
        
        # Test isolation with context
        with manager.isolated_context():
            # Add conflicting constraint
            manager.add(y)
            assert manager.check() == z3.unsat
        
        # Should be back to original state
        assert manager.check() == z3.sat
        assert manager.is_clean
    
    def test_solver_fork(self):
        """Test forking solver for parallel exploration."""
        x = z3.Bool('x')
        manager1 = SolverManager([x])
        
        # Fork the solver
        manager2 = manager1.fork()
        
        # Add different constraints
        manager1.add(z3.Bool('y'))
        manager2.add(z3.Bool('z'))
        
        # They should have different assertions
        assert len(manager1.assertions()) == 2
        assert len(manager2.assertions()) == 2
        assert str(manager1.assertions()) != str(manager2.assertions())


class TestConstraintBuilder:
    """Test constraint building utilities."""
    
    def test_state_difference_constraints(self):
        """Test creating state difference constraints."""
        builder = ConstraintBuilder("test")
        
        # Create state variables
        state_vars = {
            'a': z3.Bool('state_a'),
            'b': z3.Bool('state_b'),
            'c': z3.Bool('state_c')
        }
        
        # Test difference constraint
        set1 = {'a', 'b'}
        set2 = {'b', 'c'}
        
        constraint = builder.create_state_difference(set1, set2, state_vars)
        
        # Constraint should require either NOT c or a
        solver = z3.Solver()
        solver.add(constraint)
        
        # Should be satisfiable
        assert solver.check() == z3.sat
        
        # If we force same membership, should be unsat
        solver.add(state_vars['a'])
        solver.add(z3.Not(state_vars['c']))
        assert solver.check() == z3.unsat
    
    def test_symmetry_breaking(self):
        """Test symmetry breaking constraints."""
        builder = ConstraintBuilder("test")
        
        # Create ordered states
        states = ['s1', 's2', 's3']
        state_vars = {s: z3.Bool(f'state_{s}') for s in states}
        
        constraint = builder.create_symmetry_breaking(states, state_vars)
        
        # Test that if s3 is included, s1 and s2 must be included
        solver = z3.Solver()
        solver.add(constraint)
        solver.add(state_vars['s3'])
        solver.add(z3.Not(state_vars['s1']))
        
        # Should be unsat due to symmetry breaking
        assert solver.check() == z3.unsat
    
    def test_combine_constraints(self):
        """Test safe constraint combination."""
        builder = ConstraintBuilder("test")
        
        x, y = z3.Bool('x'), z3.Bool('y')
        constraints = [x, z3.BoolVal(True), y, z3.BoolVal(True)]
        
        combined = builder.combine_constraints(constraints)
        
        # Should filter out trivial True constraints
        solver = z3.Solver()
        solver.add(combined)
        solver.add(z3.Not(x))
        
        # Should be unsat because x is required
        assert solver.check() == z3.unsat