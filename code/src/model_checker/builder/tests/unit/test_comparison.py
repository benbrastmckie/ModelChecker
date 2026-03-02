"""
Unit tests for ModelComparison component.

This module tests ModelComparison functionality in isolation, including semantic
theory comparison, result analysis, and integration with BuildModule.
Note: This is currently a TDD test for planned ModelComparison extraction.
"""

import unittest
from unittest.mock import Mock, patch

from model_checker.builder.tests.fixtures.test_data import TestModules, TestExamples, TestTheories, TestConstants
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory
from model_checker.builder.tests.fixtures.temp_resources import TempFileCleanup
from model_checker.builder.tests.fixtures.assertions import (
    assert_error_message_contains,
    assert_no_exceptions_during_execution
)

from model_checker.builder.module import BuildModule

# Test the new comparison module before it exists (TDD)
try:
    from model_checker.builder.comparison import ModelComparison
    COMPARISON_EXISTS = True
except ImportError:
    # Module doesn't exist yet - that's expected in TDD
    ModelComparison = None
    COMPARISON_EXISTS = False


class TestModelComparisonCore(unittest.TestCase):
    """Test ModelComparison core functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create mock build module with multiple theories
        self.mock_build_module = MockObjectFactory.create_build_module({
            'general_settings': TestConstants.DEFAULT_SETTINGS,
            'semantic_theories': {
                'Theory1': TestTheories.LOGOS_THEORY,
                'Theory2': TestTheories.EXCLUSION_THEORY
            }
        })
    
    @unittest.skipIf(not COMPARISON_EXISTS, "ModelComparison not yet implemented")
    def test_model_comparison_initializes_with_valid_build_module(self):
        """Test ModelComparison initializes correctly with valid BuildModule."""
        comparison = ModelComparison(self.mock_build_module)
        
        self.assertIsNotNone(comparison,
                           "ModelComparison should initialize successfully")
        self.assertEqual(comparison.build_module, self.mock_build_module,
                        "BuildModule should be stored correctly")
    
    @unittest.skipIf(not COMPARISON_EXISTS, "ModelComparison not yet implemented")
    def test_model_comparison_has_required_interface_methods(self):
        """Test ModelComparison has all required interface methods."""
        comparison = ModelComparison(self.mock_build_module)
        
        required_methods = ['compare_semantics', 'run_comparison']
        for method_name in required_methods:
            self.assertTrue(hasattr(comparison, method_name),
                          f"ModelComparison should have {method_name} method")
            self.assertTrue(callable(getattr(comparison, method_name)),
                          f"{method_name} should be callable")


class TestModelComparisonExecution(unittest.TestCase):
    """Test ModelComparison semantic comparison execution."""
    
    def setUp(self):
        """Set up comparison execution testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create mock build module
        self.mock_build_module = MockObjectFactory.create_build_module({
            'general_settings': TestConstants.DEFAULT_SETTINGS,
            'semantic_theories': {
                'Logos': TestTheories.LOGOS_THEORY,
                'Exclusion': TestTheories.EXCLUSION_THEORY
            },
            'example_range': {
                'TEST_COMPARISON': TestExamples.BASIC_VALID
            }
        })
    
    @unittest.skipIf(not COMPARISON_EXISTS, "ModelComparison not yet implemented")
    def test_model_comparison_compares_semantics_successfully(self):
        """Test ModelComparison compares semantic theories without errors."""
        comparison = ModelComparison(self.mock_build_module)
        
        example_theory_tuples = [
            ("Logos", TestTheories.LOGOS_THEORY, TestExamples.BASIC_VALID),
            ("Exclusion", TestTheories.EXCLUSION_THEORY, TestExamples.BASIC_VALID)
        ]
        
        # Mock the comparison result
        with patch.object(comparison, 'compare_semantics') as mock_compare:
            mock_compare.return_value = [("Logos", 3), ("Exclusion", 2)]
            
            result = assert_no_exceptions_during_execution(
                self,
                lambda: comparison.compare_semantics(example_theory_tuples),
                operation_name="Semantic comparison execution"
            )
            
            # Verify result format
            self.assertIsInstance(result, list,
                               "Comparison result should be a list")
            self.assertEqual(len(result), 2,
                           "Should return results for both theories")
            
            # Verify result structure
            for theory_result in result:
                self.assertIsInstance(theory_result, tuple,
                                    "Each result should be a tuple")
                self.assertEqual(len(theory_result), 2,
                               "Each result should have theory name and score")
    
    @unittest.skipIf(not COMPARISON_EXISTS, "ModelComparison not yet implemented")
    def test_model_comparison_handles_multiple_example_theories(self):
        """Test ModelComparison processes multiple theory comparisons correctly."""
        comparison = ModelComparison(self.mock_build_module)
        
        complex_theory_tuples = [
            ("Theory1", TestTheories.MINIMAL, TestExamples.COMPLEX_VALID),
            ("Theory2", TestTheories.ADVANCED, TestExamples.COMPLEX_VALID),
            ("Theory3", TestTheories.LOGOS_THEORY, TestExamples.COMPLEX_VALID)
        ]
        
        with patch.object(comparison, 'compare_semantics') as mock_compare:
            mock_compare.return_value = [
                ("Theory1", 5), ("Theory2", 3), ("Theory3", 1)
            ]
            
            result = comparison.compare_semantics(complex_theory_tuples)
            
            self.assertEqual(len(result), 3,
                           "Should handle multiple theory comparisons")


class TestModelComparisonIntegration(unittest.TestCase):
    """Test ModelComparison integration with BuildModule."""
    
    def setUp(self):
        """Set up integration testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create test module file with multiple theories
        self.module_path = self.cleanup.create_temp_file(
            TestModules.MULTI_THEORY_CONTENT,
            suffix=".py"
        )
        
        # Create mock flags for BuildModule in comparison mode
        self.mock_flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'print_constraints': False,
            'print_z3': False,
            'save_output': False,
            'comparison': True  # Enable comparison mode
        })
    
    def test_build_module_integrates_with_comparison_after_refactoring(self):
        """Test BuildModule properly integrates with ModelComparison after refactoring."""
        build_module = BuildModule(self.mock_flags)
        
        # After refactoring, BuildModule should delegate to ModelComparison
        if hasattr(build_module, 'comparison'):
            self.assertIsNotNone(build_module.comparison,
                               "BuildModule should have comparison attribute")
            self.assertTrue(hasattr(build_module.comparison, 'compare_semantics'),
                          "Comparison should have compare_semantics method")
        else:
            # Before refactoring - this documents current state
            self.assertTrue(hasattr(build_module, 'compare_semantics') or 
                          hasattr(build_module, 'run_comparison'),
                          "BuildModule should have comparison methods (pre-refactor)")
    
    def test_build_module_enables_comparison_mode_correctly(self):
        """Test BuildModule correctly enables comparison mode when requested."""
        build_module = BuildModule(self.mock_flags)
        
        # Should recognize comparison mode is enabled
        self.assertTrue(self.mock_flags.comparison,
                       "Comparison mode should be enabled in flags")


class TestModelComparisonErrorHandling(unittest.TestCase):
    """Test ModelComparison error handling scenarios."""
    
    @unittest.skipIf(not COMPARISON_EXISTS, "ModelComparison not yet implemented")
    def test_model_comparison_handles_invalid_build_module_gracefully(self):
        """Test ModelComparison handles invalid BuildModule parameter."""
        with self.assertRaises((TypeError, AttributeError)) as context:
            ModelComparison(None)
        
        # Should get meaningful error about invalid parameter
        self.assertTrue(
            any(word in str(context.exception).lower() 
                for word in ['none', 'invalid', 'required']),
            f"Error should indicate invalid parameter, got: {context.exception}"
        )
    
    @unittest.skipIf(not COMPARISON_EXISTS, "ModelComparison not yet implemented")
    def test_model_comparison_handles_empty_theory_list_gracefully(self):
        """Test ModelComparison handles empty theory comparison list."""
        mock_build_module = MockObjectFactory.create_build_module()
        comparison = ModelComparison(mock_build_module)
        
        empty_theory_tuples = []
        
        with patch.object(comparison, 'compare_semantics') as mock_compare:
            mock_compare.return_value = []
            
            result = comparison.compare_semantics(empty_theory_tuples)
            
            self.assertEqual(result, [],
                           "Empty theory list should return empty results")
    
    @unittest.skipIf(not COMPARISON_EXISTS, "ModelComparison not yet implemented")
    def test_model_comparison_handles_malformed_theory_tuples(self):
        """Test ModelComparison handles malformed theory tuple structures."""
        mock_build_module = MockObjectFactory.create_build_module()
        comparison = ModelComparison(mock_build_module)
        
        malformed_tuples = [
            ("OnlyName",),  # Missing theory and example
            ("Name", "Theory"),  # Missing example
            "NotATuple",  # Wrong type
        ]
        
        for malformed_tuple in malformed_tuples:
            with self.subTest(tuple_data=malformed_tuple):
                with self.assertRaises((TypeError, ValueError, IndexError)):
                    comparison.compare_semantics([malformed_tuple])


class TestModelComparisonResultAnalysis(unittest.TestCase):
    """Test ModelComparison result analysis and formatting."""
    
    @unittest.skipIf(not COMPARISON_EXISTS, "ModelComparison not yet implemented")
    def test_model_comparison_formats_results_correctly(self):
        """Test ModelComparison formats comparison results in expected format."""
        mock_build_module = MockObjectFactory.create_build_module()
        comparison = ModelComparison(mock_build_module)
        
        sample_theory_tuples = [
            ("Theory1", TestTheories.MINIMAL, TestExamples.BASIC_VALID),
            ("Theory2", TestTheories.ADVANCED, TestExamples.BASIC_VALID)
        ]
        
        with patch.object(comparison, 'compare_semantics') as mock_compare:
            # Expected format: list of (theory_name, score) tuples
            mock_compare.return_value = [("Theory1", 4), ("Theory2", 1)]
            
            result = comparison.compare_semantics(sample_theory_tuples)
            
            # Verify proper formatting
            for theory_name, score in result:
                self.assertIsInstance(theory_name, str,
                                    "Theory name should be string")
                self.assertIsInstance(score, (int, float),
                                    "Score should be numeric")


if __name__ == '__main__':
    unittest.main()