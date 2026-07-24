"""
Unit tests for validation utilities.

This module tests validation functionality in isolation, including semantic
theory validation, example case validation, and component type checking.
"""

import unittest
from unittest.mock import Mock

from model_checker.builder.tests.fixtures.test_data import TestTheories, TestExamples, TestConstants
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory
from model_checker.builder.tests.fixtures.temp_resources import TempFileCleanup
from model_checker.builder.tests.fixtures.assertions import (
    assert_error_message_contains,
    assert_no_exceptions_during_execution
)

from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults
from model_checker.syntactic import OperatorCollection
from model_checker.builder.validation import (
    validate_semantic_theory,
    validate_example_case
)
from model_checker.builder.error_types import ValidationError


class TestSemanticTheoryValidation(unittest.TestCase):
    """Test semantic theory validation functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create valid semantic theory using centralized test data
        self.valid_theory = TestTheories.COMPLETE_THEORY.copy()
        self.mock_operators = Mock(spec=OperatorCollection)
        self.valid_theory["operators"] = self.mock_operators
    
    def test_validate_semantic_theory_accepts_valid_theory_structure(self):
        """Test validate_semantic_theory accepts valid semantic theory structure."""
        result = assert_no_exceptions_during_execution(
            self,
            lambda: validate_semantic_theory(self.valid_theory),
            operation_name="Valid semantic theory validation"
        )
        
        # Verify returned components
        self.assertEqual(result[0], MockObjectFactory.MockSemantics,
                        "Should return semantics component")
        self.assertEqual(result[1], MockObjectFactory.MockProposition,
                        "Should return proposition component")
        self.assertEqual(result[2], self.mock_operators,
                        "Should return operators component")
        self.assertEqual(result[3], MockObjectFactory.MockModel,
                        "Should return model component")
    
    def test_validate_semantic_theory_rejects_non_dictionary_input(self):
        """Test validate_semantic_theory rejects non-dictionary input appropriately."""
        invalid_inputs = [
            ["not", "a", "dict"],
            "string_input",
            123,
            None
        ]
        
        for invalid_input in invalid_inputs:
            with self.subTest(input_type=type(invalid_input).__name__):
                with self.assertRaises(ValidationError) as context:
                    validate_semantic_theory(invalid_input)
                
                assert_error_message_contains(
                    self, context.exception, "must be a dictionary",
                    "Non-dictionary input validation error"
                )
    
    def test_validate_semantic_theory_identifies_missing_required_components(self):
        """Test validate_semantic_theory identifies missing required components."""
        required_components = ["semantics", "proposition", "operators", "model"]
        
        for missing_component in required_components:
            with self.subTest(missing_component=missing_component):
                incomplete_theory = self.valid_theory.copy()
                del incomplete_theory[missing_component]
                
                with self.assertRaises(ValidationError) as context:
                    validate_semantic_theory(incomplete_theory)
                
                assert_error_message_contains(
                    self, context.exception, f"missing required component: {missing_component}",
                    f"Missing {missing_component} component error"
                )
    
    def test_validate_semantic_theory_validates_component_types_correctly(self):
        """Test validate_semantic_theory validates component types correctly."""
        # Test invalid semantics component
        invalid_theory = self.valid_theory.copy()
        invalid_theory["semantics"] = object  # Not a SemanticDefaults subclass
        
        with self.assertRaises(ValidationError) as context:
            validate_semantic_theory(invalid_theory)
        
        assert_error_message_contains(
            self, context.exception, "must be a subclass of SemanticDefaults",
            "Invalid semantics component validation error"
        )
        
        # Test invalid proposition component
        invalid_theory = self.valid_theory.copy()
        invalid_theory["proposition"] = object  # Not a PropositionDefaults subclass
        
        with self.assertRaises(ValidationError) as context:
            validate_semantic_theory(invalid_theory)
        
        assert_error_message_contains(
            self, context.exception, "must be a subclass of PropositionDefaults",
            "Invalid proposition component validation error"
        )
        
        # Test invalid operators component
        invalid_theory = self.valid_theory.copy()
        invalid_theory["operators"] = {}  # Not an OperatorCollection instance
        
        with self.assertRaises(ValidationError) as context:
            validate_semantic_theory(invalid_theory)
        
        assert_error_message_contains(
            self, context.exception, "must be an instance of OperatorCollection",
            "Invalid operators component validation error"
        )
        
        # Test invalid model component
        invalid_theory = self.valid_theory.copy()
        invalid_theory["model"] = object  # Not a ModelDefaults subclass
        
        with self.assertRaises(ValidationError) as context:
            validate_semantic_theory(invalid_theory)
        
        assert_error_message_contains(
            self, context.exception, "must be a subclass of ModelDefaults",
            "Invalid model component validation error"
        )


class TestExampleCaseValidation(unittest.TestCase):
    """Test example case validation functionality."""
    
    def setUp(self):
        """Set up example case testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Use centralized test data
        self.valid_example = TestExamples.BASIC_VALID
    
    def test_validate_example_case_accepts_valid_example_structure(self):
        """Test validate_example_case accepts valid example case structure."""
        result = assert_no_exceptions_during_execution(
            self,
            lambda: validate_example_case(self.valid_example),
            operation_name="Valid example case validation"
        )
        
        # Verify returned components
        premises, conclusions, settings = result
        self.assertEqual(premises, self.valid_example[0],
                        "Should return premises unchanged")
        self.assertEqual(conclusions, self.valid_example[1],
                        "Should return conclusions unchanged")
        self.assertEqual(settings, self.valid_example[2],
                        "Should return settings unchanged")
    
    def test_validate_example_case_rejects_non_list_input(self):
        """Test validate_example_case rejects non-list/tuple input appropriately."""
        invalid_inputs = [
            "not_a_list",
            123,
            {"dict": "input"},
            None
        ]
        
        for invalid_input in invalid_inputs:
            with self.subTest(input_type=type(invalid_input).__name__):
                with self.assertRaises(ValidationError) as context:
                    validate_example_case(invalid_input)
                
                assert_error_message_contains(
                    self, context.exception, "must be a list/tuple",
                    "Non-list input validation error"
                )
    
    def test_validate_example_case_validates_correct_element_count(self):
        """Test validate_example_case validates correct number of elements."""
        invalid_examples = [
            ["too", "few"],  # Only 2 elements
            ["too", "many", "elements", "here"],  # 4 elements
            [],  # Empty list
            ["only_one"]  # Only 1 element
        ]
        
        for invalid_example in invalid_examples:
            with self.subTest(element_count=len(invalid_example)):
                with self.assertRaises(ValidationError) as context:
                    validate_example_case(invalid_example)
                
                assert_error_message_contains(
                    self, context.exception, "must be a list/tuple with 3 elements",
                    "Wrong element count validation error"
                )
    
    def test_validate_example_case_validates_premises_structure(self):
        """Test validate_example_case validates premises structure correctly."""
        invalid_premise_examples = [
            (123, ["conclusion"], {}),  # Premises not a list
            ("string_premises", ["conclusion"], {}),  # Premises as string
            ([1, 2, 3], ["conclusion"], {}),  # List but not of strings
            ([["nested"], "list"], ["conclusion"], {}),  # Nested list in premises
        ]
        
        for invalid_example in invalid_premise_examples:
            with self.subTest(premises_type=type(invalid_example[0]).__name__):
                with self.assertRaises(ValidationError) as context:
                    validate_example_case(invalid_example)
                
                assert_error_message_contains(
                    self, context.exception, "must be a list of strings",
                    "Invalid premises structure validation error"
                )
    
    def test_validate_example_case_validates_conclusions_structure(self):
        """Test validate_example_case validates conclusions structure correctly."""
        invalid_conclusion_examples = [
            (["premise"], 123, {}),  # Conclusions not a list
            (["premise"], "string_conclusions", {}),  # Conclusions as string
            (["premise"], [1, 2, 3], {}),  # List but not of strings
            (["premise"], [["nested"], "list"], {}),  # Nested list in conclusions
        ]
        
        for invalid_example in invalid_conclusion_examples:
            with self.subTest(conclusions_type=type(invalid_example[1]).__name__):
                with self.assertRaises(ValidationError) as context:
                    validate_example_case(invalid_example)
                
                assert_error_message_contains(
                    self, context.exception, "must be a list of strings",
                    "Invalid conclusions structure validation error"
                )
    
    def test_validate_example_case_validates_settings_structure(self):
        """Test validate_example_case validates settings structure correctly."""
        invalid_settings_examples = [
            (["premise"], ["conclusion"], "not_a_dict"),  # Settings as string
            (["premise"], ["conclusion"], 123),  # Settings as number
            (["premise"], ["conclusion"], ["list", "settings"]),  # Settings as list
        ]
        
        for invalid_example in invalid_settings_examples:
            with self.subTest(settings_type=type(invalid_example[2]).__name__):
                with self.assertRaises(ValidationError) as context:
                    validate_example_case(invalid_example)
                
                assert_error_message_contains(
                    self, context.exception, "must be a dictionary",
                    "Invalid settings structure validation error"
                )


class TestValidationEdgeCases(unittest.TestCase):
    """Test validation edge cases and boundary conditions."""
    
    def setUp(self):
        """Set up edge case testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_validate_example_case_handles_empty_premises_and_conclusions(self):
        """Test validate_example_case handles empty premises and conclusions appropriately."""
        empty_example = ([], [], {"N": 2})
        
        result = assert_no_exceptions_during_execution(
            self,
            lambda: validate_example_case(empty_example),
            operation_name="Empty premises and conclusions validation"
        )
        
        premises, conclusions, settings = result
        self.assertEqual(premises, [],
                        "Should accept empty premises list")
        self.assertEqual(conclusions, [],
                        "Should accept empty conclusions list")
        self.assertEqual(settings, {"N": 2},
                        "Should preserve settings")
    
    def test_validate_example_case_handles_complex_settings_structures(self):
        """Test validate_example_case handles complex settings structures correctly."""
        complex_example = (
            ["premise"],
            ["conclusion"],
            {
                "N": 3,
                "max_time": 30,
                "nested": {
                    "deep": {
                        "structure": {"value": 42}
                    }
                },
                "list_setting": [1, 2, 3, 4, 5]
            }
        )
        
        result = validate_example_case(complex_example)
        
        # Should preserve complex settings structure
        self.assertEqual(result[2]["nested"]["deep"]["structure"]["value"], 42,
                        "Should preserve deeply nested settings")
        self.assertEqual(result[2]["list_setting"], [1, 2, 3, 4, 5],
                        "Should preserve list settings")
    
    def test_validate_semantic_theory_handles_extra_theory_components(self):
        """Test validate_semantic_theory handles theories with extra components gracefully."""
        theory_with_extras = TestTheories.COMPLETE_THEORY.copy()
        theory_with_extras["operators"] = Mock(spec=OperatorCollection)
        theory_with_extras["extra_component"] = "additional_data"
        theory_with_extras["another_extra"] = {"more": "data"}
        
        # Should validate successfully despite extra components
        result = assert_no_exceptions_during_execution(
            self,
            lambda: validate_semantic_theory(theory_with_extras),
            operation_name="Theory with extra components validation"
        )
        
        # Should return standard components
        self.assertEqual(len(result), 4,
                        "Should return exactly 4 standard components")
    
    def test_validate_example_case_handles_unicode_content(self):
        """Test validate_example_case handles Unicode content in strings correctly."""
        unicode_example = (
            ["premise with ∧", "另一个前提"],
            ["conclusion with ¬", "結論"],
            {"N": 2, "unicode_key": "unicode_value_∨"}
        )
        
        result = assert_no_exceptions_during_execution(
            self,
            lambda: validate_example_case(unicode_example),
            operation_name="Unicode content validation"
        )
        
        premises, conclusions, settings = result
        self.assertIn("∧", premises[0],
                     "Should preserve Unicode in premises")
        self.assertIn("另一个前提", premises[1],
                     "Should preserve non-Latin Unicode in premises")
        self.assertIn("¬", conclusions[0],
                     "Should preserve Unicode in conclusions")
        self.assertIn("結論", conclusions[1],
                     "Should preserve non-Latin Unicode in conclusions")


if __name__ == '__main__':
    unittest.main()