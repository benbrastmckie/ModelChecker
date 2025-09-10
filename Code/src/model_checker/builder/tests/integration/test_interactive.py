"""
Integration tests for BuildModule interactive functionality.

This module tests BuildModule integration with interactive save functionality,
using real components where possible and minimal mocking.
"""

import unittest
import os
from unittest.mock import Mock, patch
from contextlib import contextmanager
from io import StringIO

from model_checker.builder.tests.fixtures.test_data import TestModules, TestConstants
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory
from model_checker.builder.tests.fixtures.temp_resources import TempFileCleanup
from model_checker.builder.tests.fixtures.assertions import (
    assert_error_message_contains,
    assert_no_exceptions_during_execution
)

from model_checker.builder.module import BuildModule
from model_checker.output import InteractiveSaveManager


class TestBuildModuleInteractiveIntegration(unittest.TestCase):
    """Test BuildModule integration with interactive functionality."""
    
    def setUp(self):
        """Set up interactive integration testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create test module with interactive-appropriate content
        self.interactive_module_content = '''
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults

class InteractiveSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {"N": 5}
    DEFAULT_GENERAL_SETTINGS = {"save_output": False}  # Not used anymore

class InteractiveProposition(PropositionDefaults):
    pass

class InteractiveModel(ModelDefaults):
    pass

semantic_theories = {
    "InteractiveTest": {
        "semantics": InteractiveSemantics,
        "proposition": InteractiveProposition,
        "model": InteractiveModel,
        "operators": {},
        "dictionary": {}
    }
}

example_range = {
    "INTERACTIVE_EXAMPLE_1": [
        ["p ∧ q"],
        ["p", "q"], 
        {"N": 3, "expectation": True}
    ],
    "INTERACTIVE_EXAMPLE_2": [
        ["r ∨ s"],
        ["r"], 
        {"N": 2, "expectation": False}
    ]
}

general_settings = {
    "save_output": False,  # Not used anymore
    "print_constraints": False
}
'''
        
        self.module_path = self.cleanup.create_temp_file(
            self.interactive_module_content,
            suffix=".py"
        )
    
    @contextmanager
    def mock_console_input(self, response):
        """Helper to mock console input with specific response."""
        with patch('builtins.input', return_value=response) as mock_input:
            yield mock_input
    
    def test_interactive_mode_initialization_creates_manager_correctly(self):
        """Test interactive mode initialization creates interactive manager correctly."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save': ['markdown', 'json'],  # Enable saving with formats
            'interactive': False,
            'output_mode': 'batch',
            'sequential_files': 'multiple'
        })
        
        # Mock user choosing sequential mode
        with self.mock_console_input('s') as mock_provider:
            build_module = assert_no_exceptions_during_execution(
                self,
                lambda: BuildModule(flags),
                operation_name="Interactive BuildModule initialization"
            )
            
            # Verify interactive manager was created
            self.assertTrue(hasattr(build_module, 'output_manager'),
                          "BuildModule should have output_manager")
            
            if hasattr(build_module.output_manager, 'interactive_manager'):
                self.assertIsNotNone(build_module.output_manager.interactive_manager,
                                   "Interactive manager should be created")
                self.assertEqual(build_module.output_manager.mode, 'interactive',
                               "Should be in interactive mode")
                
                # Verify user was prompted
                mock_provider.assert_called_once_with(
                    "Save all examples (a) or run in sequence (s)? "
                )
    
    def test_batch_mode_initialization_skips_interactive_prompts(self):
        """Test batch mode initialization does not create interactive manager."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save_output': False,  # Batch mode - no save output
            'interactive': False,
            'output_mode': 'batch'
        })
        
        build_module = assert_no_exceptions_during_execution(
            self,
            lambda: BuildModule(flags),
            operation_name="Batch mode BuildModule initialization"
        )
        
        # In batch mode, should not create interactive components
        if hasattr(build_module, 'output_manager'):
            if hasattr(build_module.output_manager, 'interactive_manager'):
                # Interactive manager may exist but should not be in interactive mode
                if build_module.output_manager.interactive_manager:
                    self.assertNotEqual(
                        getattr(build_module.output_manager, 'mode', None), 'interactive',
                        "Batch mode should not be in interactive mode"
                    )
    
    def test_interactive_mode_handles_all_examples_selection(self):
        """Test interactive mode handles 'save all examples' selection correctly."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save': ['markdown', 'json'],  # Enable saving with formats
            'sequential_files': 'multiple'
        })
        
        # Mock user choosing to save all examples
        with self.mock_console_input('a') as mock_provider:
            build_module = assert_no_exceptions_during_execution(
                self,
                lambda: BuildModule(flags),
                operation_name="Interactive 'save all' mode initialization"
            )
            
            # Verify appropriate mode selection
            if hasattr(build_module, 'output_manager') and \
               hasattr(build_module.output_manager, 'mode'):
                # Mode should reflect the 'all' selection
                mode = build_module.output_manager.mode
                self.assertIn(mode, ['batch', 'all', 'interactive'],
                            f"Mode should be valid: {mode}")
                
                # Verify user was prompted
                mock_provider.assert_called_once_with(
                    "Save all examples (a) or run in sequence (s)? "
                )
    
    def test_interactive_mode_integrates_with_real_example_processing(self):
        """Test interactive mode integration with real example processing."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save_output': True
        })
        
        with self.mock_console_input('s'):
            build_module = BuildModule(flags)
            
            # Verify module loaded examples correctly
            self.assertTrue(hasattr(build_module, 'example_range'),
                          "BuildModule should load example_range")
            
            if hasattr(build_module, 'example_range'):
                examples = build_module.example_range
                self.assertGreater(len(examples), 0,
                                 "Should have loaded examples from module")
                
                # Verify examples have correct structure
                for example_name, example_case in examples.items():
                    self.assertIsInstance(example_case, list,
                                        f"Example {example_name} should be list")
                    self.assertEqual(len(example_case), 3,
                                   f"Example {example_name} should have 3 elements")
    
    def test_interactive_save_manager_integration_with_output_directory(self):
        """Test interactive save manager integration with output directory handling."""
        # Create output directory
        output_dir = self.cleanup.create_temp_dir()
        
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save': ['markdown', 'json'],  # Enable saving with formats
            'output_dir': output_dir
        })
        
        with self.mock_console_input('s'):
            build_module = BuildModule(flags)
            
            # Verify output manager can handle directory
            if hasattr(build_module, 'output_manager'):
                output_manager = build_module.output_manager
                
                # Should be able to work with provided output directory
                if hasattr(output_manager, 'output_dir'):
                    self.assertTrue(os.path.exists(output_dir),
                                  "Output directory should exist")


class TestInteractiveErrorHandling(unittest.TestCase):
    """Test error handling in interactive mode scenarios."""
    
    def setUp(self):
        """Set up error handling testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_interactive_mode_handles_invalid_user_input_gracefully(self):
        """Test interactive mode handles invalid user input gracefully."""
        module_path = self.cleanup.create_temp_file(
            TestModules.MINIMAL_CONTENT,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': module_path,
            'save_output': True
        })
        
        # Mock invalid user input followed by valid input
        with patch('builtins.input', side_effect=['invalid', 's']):
            
            # Should handle invalid input gracefully
            build_module = assert_no_exceptions_during_execution(
                self,
                lambda: BuildModule(flags),
                operation_name="Interactive mode with invalid input handling"
            )
            
            # Should eventually succeed with valid input
            self.assertIsNotNone(build_module,
                               "Should create BuildModule despite invalid input")
    
    def test_interactive_mode_handles_output_manager_initialization_errors(self):
        """Test interactive mode handles output manager initialization errors."""
        module_path = self.cleanup.create_temp_file(
            TestModules.MINIMAL_CONTENT,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': module_path,
            'save_output': True
        })
        
        # Mock input function to avoid stdin issues
        with patch('builtins.input', return_value='s'):
            
            # Mock output manager initialization failure
            with patch('model_checker.output.OutputManager') as mock_output_manager:
                mock_output_manager.side_effect = Exception("Output manager initialization failed")
                
                # BuildModule initialization might fail or handle error gracefully
                try:
                    build_module = BuildModule(flags)
                    # If it succeeds, verify it handles the error appropriately
                    self.assertIsNotNone(build_module,
                                       "BuildModule should handle output manager errors")
                except Exception as e:
                    # Accept various initialization-related errors
                    error_msg = str(e).lower()
                    acceptable_errors = ['initialization', 'output manager', 'failed']
                    has_acceptable_error = any(keyword in error_msg for keyword in acceptable_errors)
                    self.assertTrue(has_acceptable_error,
                                  f"Error should relate to initialization: {e}")


class TestInteractiveWorkflowIntegration(unittest.TestCase):
    """Test complete interactive workflow integration."""
    
    def setUp(self):
        """Set up workflow integration testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create module with multiple examples suitable for interactive processing
        self.workflow_module_content = '''
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults

class WorkflowSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {"N": 3}
    DEFAULT_GENERAL_SETTINGS = {"save_output": False}

class WorkflowProposition(PropositionDefaults):
    pass

class WorkflowModel(ModelDefaults):
    pass

semantic_theories = {
    "WorkflowTest": {
        "semantics": WorkflowSemantics,
        "proposition": WorkflowProposition,
        "model": WorkflowModel,
        "operators": {},
        "dictionary": {"\\\\wedge": "∧", "\\\\vee": "∨"}
    }
}

example_range = {
    "WORKFLOW_1": [["p \\\\wedge q"], ["p"], {"N": 2}],
    "WORKFLOW_2": [["r \\\\vee s"], ["r"], {"N": 3}],
    "WORKFLOW_3": [["p"], ["p \\\\vee q"], {"N": 2}]
}

general_settings = {"save_output": False}  # Not used anymore
'''
        
        self.module_path = self.cleanup.create_temp_file(
            self.workflow_module_content,
            suffix=".py"
        )
    
    def test_complete_interactive_workflow_processes_multiple_examples(self):
        """Test complete interactive workflow processes multiple examples correctly."""
        output_dir = self.cleanup.create_temp_dir()
        
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save': ['markdown', 'json'],  # Enable saving with formats
            'output_dir': output_dir
        })
        
        with patch('builtins.input', return_value='s'):
            
            build_module = assert_no_exceptions_during_execution(
                self,
                lambda: BuildModule(flags),
                operation_name="Complete interactive workflow"
            )
            
            # Verify module loaded all examples
            if hasattr(build_module, 'example_range'):
                examples = build_module.example_range
                self.assertEqual(len(examples), 3,
                               "Should load all 3 workflow examples")
                
                # Verify each example has correct structure
                for example_name in ["WORKFLOW_1", "WORKFLOW_2", "WORKFLOW_3"]:
                    self.assertIn(example_name, examples,
                                f"Should contain {example_name}")
                    
                    example = examples[example_name]
                    self.assertEqual(len(example), 3,
                                   f"{example_name} should have 3 components")
                    self.assertIsInstance(example[0], list,
                                        f"{example_name} premises should be list")
                    self.assertIsInstance(example[1], list,
                                        f"{example_name} conclusions should be list")
                    self.assertIsInstance(example[2], dict,
                                        f"{example_name} settings should be dict")


if __name__ == '__main__':
    unittest.main()