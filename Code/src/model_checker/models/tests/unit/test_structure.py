"""Tests for structure.py module.

Tests for ModelDefaults core Z3 solving functionality after refactoring.
Following TDD approach - these tests are written BEFORE extracting the class.
"""

import unittest
from unittest.mock import Mock, MagicMock, patch
import time
from z3 import Solver, sat, unsat, unknown, Bool, And

from model_checker.models.structure import ModelDefaults


class TestModelDefaultsStructure(unittest.TestCase):
    """Test ModelDefaults core structure and solving functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Mock model_constraints with proper constraint group attributes
        self.model_constraints = Mock()
        self.model_constraints.all_constraints = [Bool('test_constraint')]
        self.model_constraints.frame_constraints = []
        self.model_constraints.model_constraints = [Bool('test_constraint')]
        self.model_constraints.premise_constraints = []
        self.model_constraints.conclusion_constraints = []
        
        self.model_constraints.semantics = Mock()
        self.model_constraints.semantics.N = 3
        self.model_constraints.semantics.main_point = {'world': 0}
        self.model_constraints.semantics.all_states = [0, 1, 2]
        
        self.model_constraints.syntax = Mock()
        self.model_constraints.syntax.start_time = time.time()
        self.model_constraints.syntax.premises = []
        self.model_constraints.syntax.conclusions = []
        self.model_constraints.syntax.sentence_letters = []
        
        self.model_constraints.proposition_class = Mock()
        self.model_constraints.settings = {
            'max_time': 10,
            'expectation': False,
            'N': 3
        }
        
        # Mock settings
        self.settings = {
            'max_time': 10,
            'expectation': False,
            'N': 3
        }
        
        # Create instance with proper mocks
        with patch('model_checker.utils.Z3ContextManager.reset_context'):
            self.model_defaults = ModelDefaults(self.model_constraints, self.settings)
    
    def test_initialization(self):
        """Test that ModelDefaults initializes correctly."""
        # Check basic attributes
        self.assertEqual(self.model_defaults.model_constraints, self.model_constraints)
        self.assertEqual(self.model_defaults.settings, self.settings)
        self.assertEqual(self.model_defaults.max_time, 10)
        self.assertEqual(self.model_defaults.expectation, False)
        self.assertEqual(self.model_defaults.semantics, self.model_constraints.semantics)
        
        # Check color definitions
        self.assertIn('default', self.model_defaults.COLORS)
        self.assertIn('world', self.model_defaults.COLORS)
        self.assertIsNotNone(self.model_defaults.RESET)
        
        # Check solver state - ModelDefaults solves immediately upon construction
        # So solved should be True, timeout should be False, result should exist
        self.assertTrue(self.model_defaults.solved)
        self.assertIsNotNone(self.model_defaults.result)
    
    def test_setup_solver(self):
        """Test solver setup functionality."""
        # Test solver creation and constraint addition
        solver = self.model_defaults._setup_solver(self.model_constraints)
        
        # Check solver was created and returned
        self.assertIsNotNone(solver)
        self.assertIsInstance(solver, Solver)
        
        # Check constraints were added (by checking solver assertions)
        assertions = solver.assertions()
        self.assertGreater(len(assertions), 0)
    
    @patch('time.time')
    def test_solve_satisfiable(self, mock_time):
        """Test solving with satisfiable constraints."""
        # Mock time progression
        mock_time.side_effect = [0.0, 1.0]  # Start and end times
        
        # Create a satisfiable constraint with proper structure
        sat_constraints = Mock()
        sat_constraints.all_constraints = [Bool('true')]
        sat_constraints.frame_constraints = []
        sat_constraints.model_constraints = [Bool('true')]
        sat_constraints.premise_constraints = []
        sat_constraints.conclusion_constraints = []
        sat_constraints.semantics = self.model_constraints.semantics
        sat_constraints.proposition_class = self.model_constraints.proposition_class
        
        # Test solving
        result = self.model_defaults.solve(sat_constraints, 10)
        
        # Check results
        self.assertFalse(result[0])  # not timeout
        self.assertIsNotNone(result[1])  # model found
        self.assertTrue(result[2])  # satisfiable
        self.assertIsInstance(result[3], float)  # runtime
    
    def test_solve_unsatisfiable(self):
        """Test solving with unsatisfiable constraints."""
        # Create unsatisfiable constraints
        unsat_constraint = And(Bool('A'), Bool('A') == False)  # A and not A
        unsat_constraints = Mock()
        unsat_constraints.all_constraints = [unsat_constraint]
        unsat_constraints.frame_constraints = []
        unsat_constraints.model_constraints = [unsat_constraint]
        unsat_constraints.premise_constraints = []
        unsat_constraints.conclusion_constraints = []
        unsat_constraints.semantics = self.model_constraints.semantics
        unsat_constraints.proposition_class = self.model_constraints.proposition_class
        
        # Test solving
        result = self.model_defaults.solve(unsat_constraints, 10)
        
        # Check results
        self.assertFalse(result[0])  # not timeout
        self.assertIsNotNone(result[1])  # unsat core returned
        self.assertFalse(result[2])  # not satisfiable
    
    def test_process_solver_results_sat(self):
        """Test processing satisfiable solver results."""
        # Create mock satisfiable result
        mock_result = (False, Mock(), True, 1.5)  # not timeout, model, satisfiable, runtime
        
        # Process results
        self.model_defaults._process_solver_results(mock_result)
        
        # Check state
        self.assertTrue(self.model_defaults.solved)
        self.assertFalse(self.model_defaults.timeout)
        self.assertTrue(self.model_defaults.satisfiable)
        self.assertIsNotNone(self.model_defaults.z3_model)
        self.assertEqual(self.model_defaults.result, mock_result)
    
    def test_process_solver_results_unsat(self):
        """Test processing unsatisfiable solver results."""
        # Create mock unsatisfiable result
        mock_unsat_core = []  # Empty list represents unsat core
        mock_result = (False, mock_unsat_core, False, 0.8)  # not timeout, unsat core, not satisfiable, runtime
        
        # Process results
        self.model_defaults._process_solver_results(mock_result)
        
        # Check state
        self.assertFalse(self.model_defaults.timeout)
        self.assertFalse(self.model_defaults.z3_model_status)
        self.assertEqual(self.model_defaults.unsat_core, mock_unsat_core)
        self.assertEqual(self.model_defaults.z3_model_runtime, 0.8)
    
    def test_process_solver_results_timeout(self):
        """Test processing timeout solver results."""
        # Create mock timeout result
        mock_result = (True, None, False, 10.0)  # timeout, no model, not satisfiable, max runtime
        
        # Clear any existing z3_model first (from initialization)
        self.model_defaults.z3_model = None
        
        # Process results
        self.model_defaults._process_solver_results(mock_result)
        
        # Check state
        self.assertTrue(self.model_defaults.timeout)
        # When timeout, z3_model should be None
        self.assertIsNone(self.model_defaults.z3_model)
        self.assertFalse(self.model_defaults.z3_model_status)
        self.assertEqual(self.model_defaults.z3_model_runtime, 10.0)
    
    def test_create_result(self):
        """Test result tuple creation."""
        start_time = time.time()
        
        # Test satisfiable result
        result = self.model_defaults._create_result(False, Mock(), True, start_time)
        self.assertEqual(len(result), 4)
        self.assertFalse(result[0])  # not timeout
        self.assertIsNotNone(result[1])  # model
        self.assertTrue(result[2])  # satisfiable
        self.assertIsInstance(result[3], float)  # runtime
        
        # Test timeout result  
        result = self.model_defaults._create_result(True, None, None, start_time)
        self.assertTrue(result[0])  # timeout
        self.assertIsNone(result[1])  # no model
        self.assertIsNone(result[2])  # no satisfiability info
    
    def test_cleanup_solver_resources(self):
        """Test solver cleanup functionality."""
        # Set up solver manually
        solver = self.model_defaults._setup_solver(self.model_constraints)
        self.model_defaults.solver = solver
        self.assertIsNotNone(self.model_defaults.solver)
        
        # Test cleanup
        self.model_defaults._cleanup_solver_resources()
        
        # Check solver is cleaned up
        self.assertIsNone(self.model_defaults.solver)
        self.assertIsNone(self.model_defaults.z3_model)
    
    def test_re_solve(self):
        """Test re-solving with existing constraints."""
        # Note: solve() cleans up solver at the end, so re_solve needs a solver
        # Test re_solve without solver - should raise AssertionError
        with self.assertRaises(AssertionError):
            self.model_defaults.re_solve()
    
    def test_check_result(self):
        """Test result checking functionality."""
        # Test before solving - check_result needs solved state
        self.model_defaults.solved = False
        result = self.model_defaults.check_result()
        self.assertIsNone(result)
        
        # Set up solved state
        self.model_defaults.solved = True
        self.model_defaults.z3_model_status = True
        self.settings["expectation"] = True
        
        # Test expectation matching
        result = self.model_defaults.check_result()
        self.assertTrue(result)
        
        # Test expectation mismatch
        self.settings["expectation"] = False
        result = self.model_defaults.check_result()
        self.assertFalse(result)
    
    def test_interpret_method(self):
        """Test sentence interpretation method."""
        # Mock sentences with arguments attribute
        sentences = [Mock(), Mock()]
        for sentence in sentences:
            sentence.arguments = []  # Empty list, not None
            sentence.update_proposition = Mock()  # The actual method name
        
        # Test without z3_model - should return early
        self.model_defaults.z3_model = None
        self.model_defaults.interpret(sentences)
        
        # Check that update_proposition was NOT called (no model)
        for sentence in sentences:
            sentence.update_proposition.assert_not_called()
        
        # Now set a valid z3_model to enable interpretation
        self.model_defaults.z3_model = Mock()
        
        # Test interpretation with model
        self.model_defaults.interpret(sentences)
        
        # Check that update_proposition was called on each sentence
        for sentence in sentences:
            sentence.update_proposition.assert_called_once_with(self.model_defaults)
    
    def test_solver_isolation(self):
        """Test that solving works correctly with different constraint sets."""
        # First solve
        result1 = self.model_defaults.solve(self.model_constraints, 10)
        self.assertIsNotNone(result1)
        
        # Second solve with different constraints
        new_constraints = Mock()
        new_constraints.all_constraints = [Bool('different_constraint')]
        new_constraints.frame_constraints = []
        new_constraints.model_constraints = [Bool('different_constraint')]
        new_constraints.premise_constraints = []
        new_constraints.conclusion_constraints = []
        new_constraints.semantics = self.model_constraints.semantics
        new_constraints.proposition_class = self.model_constraints.proposition_class
        
        result2 = self.model_defaults.solve(new_constraints, 10)
        self.assertIsNotNone(result2)
        
        # Results should be independent (not identical objects)
        self.assertIsNot(result1, result2)
    
    def test_attribute_initialization_order(self):
        """Test critical attribute initialization order for iterator compatibility."""
        # This is the critical test for iterator regression prevention
        with patch('z3.Solver'):  # Mock Z3 solver to avoid actual solving
            model_defaults = ModelDefaults(self.model_constraints, self.settings)
        
        # Check that all critical attributes are properly initialized
        self.assertIsNotNone(model_defaults.model_constraints)
        self.assertIsNotNone(model_defaults.settings)
        self.assertIsNotNone(model_defaults.semantics)
        self.assertIsNotNone(model_defaults.proposition_class)
        
        # Check solver state attributes exist and have correct values after construction solve
        self.assertTrue(model_defaults.solved)  # ModelDefaults solves during construction
        self.assertIsNotNone(model_defaults.result)  # Result should be available
        
        # Check attribute types are correct
        self.assertIsInstance(model_defaults.timeout, bool)
        self.assertIn(model_defaults.satisfiable, [True, False, None])  # Boolean or None
        
        # Check main_point is properly initialized
        self.assertIsNotNone(model_defaults.main_point)
        
        # Check COLORS dictionary is properly initialized
        self.assertIsInstance(model_defaults.COLORS, dict)
        self.assertIn('world', model_defaults.COLORS)
        self.assertIn('default', model_defaults.COLORS)
        
        # Check constraint_dict is properly initialized
        self.assertIsInstance(model_defaults.constraint_dict, dict)
        # constraint_dict has all_constraints after solving
        self.assertGreaterEqual(len(model_defaults.constraint_dict), 0)


if __name__ == '__main__':
    unittest.main()