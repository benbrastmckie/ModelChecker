"""
Unit tests for ModelRunner component.

This module tests ModelRunner functionality in isolation, including model
checking execution, example processing, and integration with BuildModule.
Note: This is currently a TDD test for planned ModelRunner extraction.
"""

import unittest
import os
import tempfile
from unittest.mock import Mock, patch
from pathlib import Path

from model_checker.builder.tests.fixtures.test_data import TestModules, TestExamples, TestConstants
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory
from model_checker.builder.tests.fixtures.temp_resources import TempFileCleanup
from model_checker.builder.tests.fixtures.assertions import (
    assert_error_message_contains,
    assert_no_exceptions_during_execution
)
from model_checker.builder.error_types import ValidationError

from model_checker.builder.module import BuildModule

# Test the new runner module before it exists (TDD)
try:
    from model_checker.builder.runner import ModelRunner
    RUNNER_EXISTS = True
except ImportError:
    # Module doesn't exist yet - that's expected in TDD
    ModelRunner = None
    RUNNER_EXISTS = False


class TestModelRunnerCore(unittest.TestCase):
    """Test ModelRunner core functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create mock build module
        self.mock_build_module = MockObjectFactory.create_build_module({
            'general_settings': TestConstants.DEFAULT_SETTINGS,
            'translation': Mock()
        })
    
    @unittest.skipIf(not RUNNER_EXISTS, "ModelRunner not yet implemented")
    def test_model_runner_initializes_with_valid_build_module(self):
        """Test ModelRunner initializes correctly with valid BuildModule."""
        runner = ModelRunner(self.mock_build_module)
        
        self.assertIsNotNone(runner, 
                           "ModelRunner should initialize successfully")
        self.assertEqual(runner.build_module, self.mock_build_module,
                        "BuildModule should be stored correctly")
    
    @unittest.skipIf(not RUNNER_EXISTS, "ModelRunner not yet implemented")
    def test_model_runner_has_required_interface_methods(self):
        """Test ModelRunner has all required interface methods."""
        runner = ModelRunner(self.mock_build_module)
        
        required_methods = ['run_model_check', 'try_single_N', 'process_example']
        for method_name in required_methods:
            self.assertTrue(hasattr(runner, method_name),
                          f"ModelRunner should have {method_name} method")
            self.assertTrue(callable(getattr(runner, method_name)),
                          f"{method_name} should be callable")


class TestModelRunnerExecution(unittest.TestCase):
    """Test ModelRunner model checking execution."""
    
    def setUp(self):
        """Set up execution testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create mock build module with translation
        self.mock_build_module = MockObjectFactory.create_build_module({
            'general_settings': TestConstants.DEFAULT_SETTINGS,
            'translation': Mock()
        })
        self.mock_build_module.translation.translate.return_value = TestExamples.BASIC_VALID
    
    @unittest.skipIf(not RUNNER_EXISTS, "ModelRunner not yet implemented")
    def test_model_runner_executes_model_check_successfully(self):
        """Test ModelRunner executes model check without errors."""
        runner = ModelRunner(self.mock_build_module)
        
        with patch('model_checker.builder.example.BuildExample') as mock_build_example:
            result = assert_no_exceptions_during_execution(
                self, 
                lambda: runner.run_model_check(
                    TestExamples.BASIC_VALID, 
                    "test_example", 
                    "TestTheory", 
                    TestConstants.DEFAULT_SEMANTIC_THEORY
                ),
                operation_name="Model check execution"
            )
            
            # Verify BuildExample was created and called correctly
            mock_build_example.assert_called_once()
            self.assertEqual(result, mock_build_example.return_value,
                           "Should return BuildExample instance")
    
    @unittest.skipIf(not RUNNER_EXISTS, "ModelRunner not yet implemented")
    def test_model_runner_handles_example_processing_correctly(self):
        """Test ModelRunner processes examples with proper parameter passing."""
        runner = ModelRunner(self.mock_build_module)
        
        with patch('model_checker.builder.example.BuildExample') as mock_build_example:
            example_case = TestExamples.COMPLEX_VALID
            semantic_theory = TestConstants.ADVANCED_SEMANTIC_THEORY
            
            runner.run_model_check(example_case, "complex_test", "ComplexTheory", semantic_theory)
            
            # Verify correct parameters were passed
            call_args = mock_build_example.call_args
            self.assertIsNotNone(call_args, 
                               "BuildExample should be called with parameters")


class TestModelRunnerIntegration(unittest.TestCase):
    """Test ModelRunner integration with BuildModule."""
    
    def setUp(self):
        """Set up integration testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create test module file for BuildModule
        self.module_path = self.cleanup.create_temp_file(
            TestModules.LOGOS_CONTENT,
            suffix=".py"
        )
        
        # Create mock flags for BuildModule
        self.mock_flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'print_constraints': False,
            'print_z3': False,
            'save_output': False,
            'comparison': False
        })
    
    def test_build_module_integrates_with_runner_after_refactoring(self):
        """Test BuildModule properly integrates with ModelRunner after refactoring."""
        build_module = BuildModule(self.mock_flags)
        
        # After refactoring, BuildModule should delegate to ModelRunner
        if hasattr(build_module, 'runner'):
            self.assertIsNotNone(build_module.runner,
                               "BuildModule should have runner attribute")
            self.assertTrue(hasattr(build_module.runner, 'run_model_check'),
                          "Runner should have run_model_check method")
        else:
            # Before refactoring - this documents current state
            self.assertTrue(hasattr(build_module, 'run_model_check'),
                          "BuildModule should have run_model_check method (pre-refactor)")


class TestModelRunnerErrorHandling(unittest.TestCase):
    """Test ModelRunner error handling scenarios."""
    
    @unittest.skipIf(not RUNNER_EXISTS, "ModelRunner not yet implemented")
    def test_model_runner_handles_invalid_build_module_gracefully(self):
        """Test ModelRunner handles invalid BuildModule parameter."""
        with self.assertRaises((TypeError, AttributeError)) as context:
            ModelRunner(None)
        
        # Should get meaningful error about invalid parameter
        self.assertTrue(
            any(word in str(context.exception).lower() 
                for word in ['none', 'invalid', 'required']),
            f"Error should indicate invalid parameter, got: {context.exception}"
        )
    
    @unittest.skipIf(not RUNNER_EXISTS, "ModelRunner not yet implemented")
    def test_model_runner_handles_missing_translation_gracefully(self):
        """Test ModelRunner handles BuildModule without translation component."""
        mock_build_module = Mock()
        mock_build_module.general_settings = TestConstants.DEFAULT_SETTINGS
        # Create a mock translation that will cause an error when used
        mock_build_module.translation = None
        
        runner = ModelRunner(mock_build_module)
        
        # Create semantic theory with dictionary to trigger translation
        semantic_theory_with_dict = TestConstants.DEFAULT_SEMANTIC_THEORY.copy()
        semantic_theory_with_dict["dictionary"] = {"&": "∧"}
        
        with self.assertRaises(AttributeError) as context:
            runner.run_model_check(TestExamples.BASIC_VALID, "test", "Theory", semantic_theory_with_dict)
        
        # The error will occur when trying to call None.translate
        self.assertIn("translate", str(context.exception),
                     "Error should mention translate method")


class TestModelRunnerEdgeCases(unittest.TestCase):
    """Test ModelRunner edge cases and boundary conditions."""
    
    def setUp(self):
        """Set up edge case testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    @unittest.skipIf(not RUNNER_EXISTS, "ModelRunner not yet implemented")
    def test_model_runner_handles_empty_example_cases_appropriately(self):
        """Test ModelRunner handles empty example cases."""
        mock_build_module = MockObjectFactory.create_build_module()
        runner = ModelRunner(mock_build_module)
        
        empty_example = [[], [], {}]  # Empty premises, conclusions, settings
        
        with patch('model_checker.builder.example.BuildExample'):
            # Should handle empty case without crashing
            result = assert_no_exceptions_during_execution(
                self, 
                lambda: runner.run_model_check(
                    empty_example, "empty_test", "Theory", {}
                ),
                operation_name="Empty example processing"
            )
            
            self.assertIsNotNone(result,
                               "Empty example should still produce result")
    
    @unittest.skipIf(not RUNNER_EXISTS, "ModelRunner not yet implemented")
    def test_model_runner_handles_malformed_example_structure(self):
        """Test ModelRunner handles malformed example structures gracefully."""
        mock_build_module = MockObjectFactory.create_build_module()
        runner = ModelRunner(mock_build_module)
        
        malformed_examples = [
            ["only_premises"],  # Missing conclusions and settings
            [["p"], ["q"]],     # Missing settings dict
            "not_a_list",       # Wrong type entirely
        ]
        
        for malformed_example in malformed_examples:
            with self.subTest(example=malformed_example):
                with self.assertRaises((ValidationError, TypeError, IndexError, AttributeError)):
                    runner.run_model_check(
                        malformed_example, "malformed", "Theory", {}
                    )


if __name__ == '__main__':
    unittest.main()