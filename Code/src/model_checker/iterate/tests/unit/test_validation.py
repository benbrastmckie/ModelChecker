"""Tests for the validation module."""

import unittest
import z3
from unittest.mock import Mock, MagicMock

from model_checker.iterate.models import evaluate_z3_boolean, is_valid_model, validate_premises, validate_conclusions


class TestModelValidator(unittest.TestCase):
    """Test the ModelValidator class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.solver = z3.Solver()
        self.x = z3.Bool('x')
        self.y = z3.Bool('y')
        self.solver.add(self.x == True)
        self.solver.add(self.y == False)
        self.solver.check()
        self.model = self.solver.model()
    
    def test_evaluate_z3_boolean_direct_values(self):
        """Test evaluation of direct boolean values."""
        # Python booleans
        self.assertTrue(evaluate_z3_boolean(self.model, True))
        self.assertFalse(evaluate_z3_boolean(self.model, False))
        
        # None should be False
        self.assertFalse(evaluate_z3_boolean(self.model, None))
    
    def test_evaluate_z3_boolean_z3_expressions(self):
        """Test evaluation of Z3 boolean expressions."""
        # Simple variables
        self.assertTrue(evaluate_z3_boolean(self.model, self.x))
        self.assertFalse(evaluate_z3_boolean(self.model, self.y))
        
        # Compound expressions
        self.assertTrue(evaluate_z3_boolean(self.model, z3.And(self.x, z3.Not(self.y))))
        self.assertFalse(evaluate_z3_boolean(self.model, z3.And(self.x, self.y)))
    
    def test_evaluate_z3_boolean_numeric_values(self):
        """Test evaluation of numeric Z3 values."""
        # Integer values
        i = z3.Int('i')
        solver = z3.Solver()
        solver.add(i == 5)
        solver.check()
        model = solver.model()
        
        # Non-zero should be True
        self.assertTrue(evaluate_z3_boolean(model, i))
        
        # Zero should be False
        solver2 = z3.Solver()
        solver2.add(i == 0)
        solver2.check()
        model2 = solver2.model()
        self.assertFalse(evaluate_z3_boolean(model2, i))
    
    def test_is_valid_model_basic(self):
        """Test basic model validation."""
        # Mock model with required attributes
        model = Mock()
        model.z3_model = self.model
        model.premise_formulas = []
        model.conclusion_formulas = []
        
        settings = {}
        self.assertTrue(is_valid_model(model, settings))
        
        # Missing required attribute
        delattr(model, 'z3_model')
        self.assertFalse(is_valid_model(model, settings))
    
    def test_is_valid_model_non_empty(self):
        """Test non-empty model validation."""
        # Mock model with possible states
        model = Mock()
        model.z3_model = self.model
        model.premise_formulas = []
        model.conclusion_formulas = []
        model.z3_possible_states = [1, 2, 3]
        
        settings = {'non_empty': True}
        self.assertTrue(is_valid_model(model, settings))
        
        # Empty states
        model.z3_possible_states = []
        self.assertFalse(is_valid_model(model, settings))
    
    def test_validate_premises(self):
        """Test premise validation."""
        # Mock model with premises
        model = Mock()
        
        # Create premise that should be true
        premise1 = Mock()
        premise1.z3_formula = self.x
        
        # Create premise that should be false
        premise2 = Mock()
        premise2.z3_formula = self.y
        
        # All premises true
        model.premise_formulas = [premise1]
        self.assertTrue(validate_premises(model, self.model))
        
        # Some premise false
        model.premise_formulas = [premise1, premise2]
        self.assertFalse(validate_premises(model, self.model))
    
    def test_validate_conclusions_countermodel(self):
        """Test conclusion validation for countermodels."""
        # Mock model with conclusions
        model = Mock()
        
        # Create conclusions
        conc1 = Mock()
        conc1.z3_formula = self.x  # True
        
        conc2 = Mock()
        conc2.z3_formula = self.y  # False
        
        # For countermodel (expectation=True), we want at least one false conclusion
        model.conclusion_formulas = [conc2]
        self.assertTrue(validate_conclusions(model, self.model, expectation=True))
        
        # All conclusions true - invalid countermodel
        model.conclusion_formulas = [conc1]
        self.assertFalse(validate_conclusions(model, self.model, expectation=True))
    
    def test_validate_conclusions_theorem(self):
        """Test conclusion validation for theorems."""
        # Mock model with conclusions
        model = Mock()
        
        # Create conclusions
        conc1 = Mock()
        conc1.z3_formula = self.x  # True
        
        conc2 = Mock()
        conc2.z3_formula = self.y  # False
        
        # For theorem (expectation=False), we want all conclusions true
        model.conclusion_formulas = [conc1]
        self.assertTrue(validate_conclusions(model, self.model, expectation=False))
        
        # Some conclusion false - invalid theorem
        model.conclusion_formulas = [conc1, conc2]
        self.assertFalse(validate_conclusions(model, self.model, expectation=False))


if __name__ == '__main__':
    unittest.main()