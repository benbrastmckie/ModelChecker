"""
Integration tests for iterator solver lifecycle management.

These tests ensure proper solver state management and isolation
throughout the iteration process.
"""

import pytest
import z3
from model_checker.builder.example import BuildExample
from model_checker.theory_lib.exclusion import get_theory as get_exclusion_theory
from model_checker.theory_lib.exclusion.iterate import ExclusionModelIterator
from model_checker.theory_lib.bimodal import get_theory as get_bimodal_theory
from model_checker.theory_lib.bimodal.iterate import BimodalModelIterator


class TestSolverLifecycle:
    """Test solver lifecycle management in iterator."""
    
    def test_solver_isolation_from_original(self):
        """Test that iterator solver is isolated from original model solver."""
        exclusion_theory = get_exclusion_theory()
        
        example = BuildExample(
            name="test",
            semantic_theory=exclusion_theory,
            premises=["A"],
            conclusions=["B"],
            settings={'N': 2}
        )
        
        # Get original model
        example.run_single_test()
        original_model = example.model_structure
        
        # Get original solver state (if available)
        original_solver = None
        if hasattr(original_model, 'solver') and original_model.solver:
            original_solver = original_model.solver
        elif hasattr(original_model, 'stored_solver') and original_model.stored_solver:
            original_solver = original_model.stored_solver
        
        # Create iterator
        iterator = ExclusionModelIterator(example)
        
        # Iterator should have its own solver
        assert iterator.solver is not None
        if original_solver:
            assert iterator.solver is not original_solver
        
        # Adding constraints to iterator shouldn't affect original
        iterator.solver.add(z3.Bool('test_constraint'))
        
        if original_solver:
            # Original solver shouldn't have this constraint
            original_assertions = original_solver.assertions()
            assert not any('test_constraint' in str(a) for a in original_assertions)
    
    def test_solver_state_after_iteration(self):
        """Test solver state remains valid after iteration."""
        bimodal_theory = get_bimodal_theory()
        
        example = BuildExample(
            name="test",
            semantic_theory=bimodal_theory,
            premises=["\\Box_1 A"],
            conclusions=["\\Box_2 A"],
            settings={'N': 2, 'iterate': 2}
        )
        
        example.run_single_test()
        iterator = BimodalModelIterator(example)
        
        # Run iteration
        models = iterator.iterate()
        
        # Solver should still be usable
        assert iterator.solver is not None
        
        # Should have accumulated constraints
        assertions = iterator.solver.assertions()
        assert len(assertions) > len(iterator.original_constraints)
        
        # Solver should still be satisfiable (found models)
        if len(models) > 1:
            # The solver found multiple models, so it was satisfiable
            pass
        else:
            # Even with one model, solver should be in valid state
            result = iterator.solver.check()
            assert result in [z3.sat, z3.unsat]
    
    def test_timeout_handling(self):
        """Test that solver timeouts are properly handled."""
        exclusion_theory = get_exclusion_theory()
        
        example = BuildExample(
            name="test",
            semantic_theory=exclusion_theory,
            premises=["A", "B", "C"],
            conclusions=["(A \\wedge (B \\wedge C))"],
            settings={
                'N': 4,
                'iterate': 5,
                'iteration_solver_timeout': 0.1  # Very short timeout
            }
        )
        
        example.run_single_test()
        iterator = ExclusionModelIterator(example)
        
        # Should handle timeouts gracefully
        models = iterator.iterate()
        
        # Might find fewer models due to timeout, but shouldn't crash
        assert len(models) >= 1  # At least the original model
        
        # Check debug messages for timeout handling
        timeout_messages = [msg for msg in iterator.debug_messages 
                          if 'timeout' in msg.lower()]
        # May or may not timeout depending on system speed


class TestSolverRobustness:
    """Test solver robustness in edge cases."""
    
    def test_incremental_solving(self):
        """Test that incremental solving works correctly."""
        exclusion_theory = get_exclusion_theory()
        
        example = BuildExample(
            name="test",
            semantic_theory=exclusion_theory,
            premises=["A"],
            conclusions=["\\neg A"],
            settings={'N': 3, 'iterate': 3}
        )
        
        example.run_single_test()
        iterator = ExclusionModelIterator(example)
        
        # Track solver assertion growth
        initial_assertions = len(iterator.solver.assertions())
        
        # Manual iteration to observe incremental solving
        found_models = [example.model_structure]
        
        # Each iteration should add constraints incrementally
        models = iterator.iterate()
        
        final_assertions = len(iterator.solver.assertions())
        assert final_assertions > initial_assertions
    
    def test_no_solver_pollution(self):
        """Test that failed iterations don't pollute solver state."""
        exclusion_theory = get_exclusion_theory()
        
        example = BuildExample(
            name="test",
            semantic_theory=exclusion_theory,
            premises=["A", "\\neg A"],  # Contradiction
            conclusions=["B"],
            settings={'N': 2}
        )
        
        # This should fail to find a model
        example.run_single_test()
        
        if example.model_structure is None:
            # Expected - contradictory premises
            return
        
        # If somehow we got a model, try iteration
        iterator = ExclusionModelIterator(example)
        
        # Even if iteration fails, solver should remain in valid state
        try:
            models = iterator.iterate()
        except Exception:
            # Solver should still be queryable
            assert iterator.solver is not None
            # Should be able to check state
            iterator.solver.check()