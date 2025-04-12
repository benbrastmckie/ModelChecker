"""Tests for the validation utilities."""

import unittest
from unittest.mock import Mock, MagicMock, patch

from model_checker.model import (
    SemanticDefaults,
    PropositionDefaults,
    ModelDefaults
)
from model_checker.syntactic import OperatorCollection
from model_checker.builder.validation import (
    validate_semantic_theory,
    validate_example_case
)

# Mock classes for testing
class MockSemantics(SemanticDefaults):
    def __init__(self, *args, **kwargs):
        pass

class MockProposition(PropositionDefaults):
    def __init__(self, *args, **kwargs):
        pass

class MockModel(ModelDefaults):
    def __init__(self, *args, **kwargs):
        pass

class TestValidation(unittest.TestCase):
    """Test the validation utilities."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.mock_operators = Mock(spec=OperatorCollection)
        
        # Create valid semantic theory
        self.valid_theory = {
            "semantics": MockSemantics,
            "proposition": MockProposition,
            "operators": self.mock_operators,
            "model": MockModel
        }
        
        # Create valid example case
        self.valid_example = (
            ["premise1", "premise2"],
            ["conclusion"],
            {"N": 3, "max_time": 30}
        )
    
    def test_validate_semantic_theory_valid(self):
        """Test validating a valid semantic theory."""
        result = validate_semantic_theory(self.valid_theory)
        self.assertEqual(result[0], MockSemantics)
        self.assertEqual(result[1], MockProposition)
        self.assertEqual(result[2], self.mock_operators)
        self.assertEqual(result[3], MockModel)
    
    def test_validate_semantic_theory_not_dict(self):
        """Test validating a non-dictionary semantic theory."""
        with self.assertRaises(TypeError) as context:
            validate_semantic_theory(["not", "a", "dict"])
        self.assertTrue("must be a dictionary" in str(context.exception))
    
    def test_validate_semantic_theory_missing_component(self):
        """Test validating a semantic theory with missing component."""
        for key in self.valid_theory.keys():
            invalid_theory = self.valid_theory.copy()
            del invalid_theory[key]
            
            with self.assertRaises(TypeError) as context:
                validate_semantic_theory(invalid_theory)
            self.assertTrue(f"missing required component: {key}" in str(context.exception))
    
    def test_validate_semantic_theory_invalid_types(self):
        """Test validating a semantic theory with invalid component types."""
        # Test invalid semantics
        invalid_theory = self.valid_theory.copy()
        invalid_theory["semantics"] = object  # Not a SemanticDefaults subclass
        
        with self.assertRaises(TypeError) as context:
            validate_semantic_theory(invalid_theory)
        self.assertTrue("'semantics' must be a subclass of SemanticDefaults" in str(context.exception))
        
        # Test invalid proposition
        invalid_theory = self.valid_theory.copy()
        invalid_theory["proposition"] = object  # Not a PropositionDefaults subclass
        
        with self.assertRaises(TypeError) as context:
            validate_semantic_theory(invalid_theory)
        self.assertTrue("'proposition' must be a subclass of PropositionDefaults" in str(context.exception))
        
        # Test invalid operators
        invalid_theory = self.valid_theory.copy()
        invalid_theory["operators"] = {}  # Not an OperatorCollection instance
        
        with self.assertRaises(TypeError) as context:
            validate_semantic_theory(invalid_theory)
        self.assertTrue("'operators' must be an instance of OperatorCollection" in str(context.exception))
        
        # Test invalid model
        invalid_theory = self.valid_theory.copy()
        invalid_theory["model"] = object  # Not a ModelDefaults subclass
        
        with self.assertRaises(TypeError) as context:
            validate_semantic_theory(invalid_theory)
        self.assertTrue("'model' must be a subclass of ModelDefaults" in str(context.exception))
    
    def test_validate_example_case_valid(self):
        """Test validating a valid example case."""
        result = validate_example_case(self.valid_example)
        self.assertEqual(result[0], ["premise1", "premise2"])
        self.assertEqual(result[1], ["conclusion"])
        self.assertEqual(result[2], {"N": 3, "max_time": 30})
    
    def test_validate_example_case_not_list(self):
        """Test validating a non-list example case."""
        with self.assertRaises(TypeError) as context:
            validate_example_case("not a list")
        self.assertTrue("must be a list/tuple" in str(context.exception))
    
    def test_validate_example_case_wrong_length(self):
        """Test validating an example case with wrong number of elements."""
        with self.assertRaises(TypeError) as context:
            validate_example_case(["too", "few"])
        self.assertTrue("must be a list/tuple containing exactly 3 elements" in str(context.exception))
    
    def test_validate_example_case_invalid_premises(self):
        """Test validating an example case with invalid premises."""
        invalid_example = (123, ["conclusion"], {})  # First element not a list of strings
        
        with self.assertRaises(TypeError) as context:
            validate_example_case(invalid_example)
        self.assertTrue("premises must be a list of strings" in str(context.exception))
        
        invalid_example = ([1, 2, 3], ["conclusion"], {})  # List but not of strings
        
        with self.assertRaises(TypeError) as context:
            validate_example_case(invalid_example)
        self.assertTrue("premises must be a list of strings" in str(context.exception))
    
    def test_validate_example_case_invalid_conclusions(self):
        """Test validating an example case with invalid conclusions."""
        invalid_example = (["premise"], 123, {})  # Second element not a list of strings
        
        with self.assertRaises(TypeError) as context:
            validate_example_case(invalid_example)
        self.assertTrue("conclusions must be a list of strings" in str(context.exception))
        
        invalid_example = (["premise"], [1, 2, 3], {})  # List but not of strings
        
        with self.assertRaises(TypeError) as context:
            validate_example_case(invalid_example)
        self.assertTrue("conclusions must be a list of strings" in str(context.exception))
    
    def test_validate_example_case_invalid_settings(self):
        """Test validating an example case with invalid settings."""
        invalid_example = (["premise"], ["conclusion"], "not a dict")  # Third element not a dictionary
        
        with self.assertRaises(TypeError) as context:
            validate_example_case(invalid_example)
        self.assertTrue("settings must be a dictionary" in str(context.exception))

if __name__ == "__main__":
    unittest.main()