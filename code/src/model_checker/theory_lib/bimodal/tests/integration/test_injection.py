"""Test Z3 injection for Bimodal theory.

Following TDD approach - written BEFORE implementing inject_z3_model_values.
Tests verify Bimodal-specific injection including temporal relations.
"""

import unittest
from unittest.mock import Mock
import z3
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics
from model_checker import syntactic
from model_checker.syntactic.atoms import get_atom_sort


class TestBimodalInjection(unittest.TestCase):
    """Test Bimodal theory Z3 injection functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.settings = {'N': 2, 'M': 3, 'contingent': False}
        self.semantics = BimodalSemantics(self.settings)
        
        # Create mock model constraints
        self.mock_constraints = Mock()
        self.mock_constraints.all_constraints = []
        self.mock_constraints.syntax = Mock()
        self.mock_constraints.syntax.sentence_letters = []
        self.mock_constraints.settings = {'N': 2}
    
    def test_inject_z3_model_values_exists(self):
        """Test that inject_z3_model_values method exists."""
        self.assertTrue(hasattr(self.semantics, 'inject_z3_model_values'))
        
    def test_inject_basic_constraints(self):
        """Test injection of basic constraints."""
        # Create a Z3 model
        solver = z3.Solver()
        solver.add(self.semantics.is_world(0))
        
        result = solver.check()
        self.assertEqual(result, z3.sat)
        z3_model = solver.model()
        
        # Inject values
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)
        
        # Check that constraints were added
        constraints = self.mock_constraints.all_constraints
        
        # Should have at least world and possible constraints
        self.assertGreater(len(constraints), 0)
    
    def test_inject_truth_condition_constraints(self):
        """Test injection of truth_condition constraints."""
        # Create mock sentence letters
        letter_a = Mock()
        letter_a.sentence_letter = z3.Const('A', get_atom_sort())
        self.mock_constraints.syntax.sentence_letters = [letter_a]
        
        # Create a Z3 model with truth_condition values
        solver = z3.Solver()
        atom_a = letter_a.sentence_letter
        
        # Set some truth condition values
        solver.add(self.semantics.truth_condition(0, atom_a))
        solver.add(z3.Not(self.semantics.truth_condition(1, atom_a)))
        solver.add(self.semantics.truth_condition(2, atom_a))
        solver.add(z3.Not(self.semantics.truth_condition(3, atom_a)))
        
        # Add world constraint
        solver.add(self.semantics.is_world(0))
        
        result = solver.check()
        self.assertEqual(result, z3.sat)
        z3_model = solver.model()
        
        # Inject values
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)
        
        # Check that constraints were added
        constraints = self.mock_constraints.all_constraints
        
        # Should have truth_condition constraints
        truth_constraints = [c for c in constraints if 'truth_condition' in str(c)]
        
        # 4 states * 1 letter = 4 truth_condition constraints
        self.assertEqual(len(truth_constraints), 4)
    
    def test_inject_task_constraints(self):
        """Test injection handles ternary task relations with duration.

        Task 91 Migration: task(w, u) -> task_rel(w, d, u)
        The old binary task relation has been replaced with a ternary
        task_rel that includes an explicit duration parameter.
        """
        # Bimodal now has ternary task_rel relation between states
        self.assertTrue(hasattr(self.semantics, 'task_rel'))
        self.assertFalse(hasattr(self.semantics, 'task'))  # Old API removed

        # Create a Z3 model with task_rel constraints (with explicit durations)
        solver = z3.Solver()

        # Set some task_rel values with explicit durations
        solver.add(self.semantics.task_rel(0, 1, 1))  # state 0 -> state 1 in duration 1
        solver.add(z3.Not(self.semantics.task_rel(0, 1, 2)))  # NOT state 0 -> state 2 in duration 1
        solver.add(self.semantics.task_rel(1, 1, 2))  # state 1 -> state 2 in duration 1
        solver.add(self.semantics.task_rel(0, 2, 2))  # state 0 -> state 2 in duration 2 (composition)

        # Add world constraint
        solver.add(self.semantics.is_world(0))

        result = solver.check()
        self.assertEqual(result, z3.sat)
        z3_model = solver.model()

        # Inject values
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)

        # Check that constraints were added
        constraints = self.mock_constraints.all_constraints

        # Should have task_rel constraints (note: TaskRel, not Task)
        task_constraints = [c for c in constraints if 'TaskRel(' in str(c)]

        # We inject task_rel for all state pairs and all durations:
        # 4 states * 3 durations (-1, 0, 1 for M=2) * 4 states = 48
        # But settings has M=3, so durations are (-2, -1, 0, 1, 2) = 5 durations
        # 4 states * 5 durations * 4 states = 80
        expected_count = 4 * (2 * self.settings['M'] - 1) * 4
        self.assertEqual(len(task_constraints), expected_count)
    
    def test_uses_model_validator(self):
        """Test that inject_z3_model_values works correctly."""
        # Create minimal Z3 model
        solver = z3.Solver()
        solver.add(self.semantics.is_world(0))
        solver.check()
        z3_model = solver.model()
        
        # Inject values
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)
        
        # Check that injection worked
        constraints = self.mock_constraints.all_constraints
        self.assertGreater(len(constraints), 0)


if __name__ == '__main__':
    import unittest
    unittest.main()
