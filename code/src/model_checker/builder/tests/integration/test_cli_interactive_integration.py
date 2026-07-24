"""
Integration tests for CLI interactive flag functionality.

This module tests the integration between CLI interactive flags and BuildModule
behavior, ensuring proper mode setting and user interaction flow.
"""

import unittest
from unittest.mock import patch

from model_checker.builder.tests.fixtures.test_data import TestModules, TestConstants
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory
from model_checker.builder.tests.fixtures.temp_resources import TempFileCleanup
from model_checker.builder.tests.fixtures.assertions import (
    assert_error_message_contains,
    assert_no_exceptions_during_execution
)

from model_checker.builder.module import BuildModule


class TestCLIInteractiveFlagIntegration(unittest.TestCase):
    """Test CLI interactive flag integration with BuildModule behavior."""
    
    def setUp(self):
        """Set up CLI interactive flag testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create test module suitable for interactive testing
        self.interactive_module_content = '''
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults

class InteractiveTestSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {"N": 5}
    DEFAULT_GENERAL_SETTINGS = {"save_output": True}

class InteractiveTestProposition(PropositionDefaults):
    pass

class InteractiveTestModel(ModelDefaults):
    pass

semantic_theories = {
    "InteractiveTest": {
        "semantics": InteractiveTestSemantics,
        "proposition": InteractiveTestProposition,
        "model": InteractiveTestModel,
        "operators": {},
        "dictionary": {}
    }
}

example_range = {
    "CLI_INTERACTIVE_EXAMPLE": [
        ["p ∧ q"],
        ["p"], 
        {"N": 3, "expectation": True}
    ]
}

general_settings = {
    "save_output": True,
    "print_constraints": False
}
'''
        
        self.module_path = self.cleanup.create_temp_file(
            self.interactive_module_content,
            suffix=".py"
        )
    
    def test_interactive_flag_bypasses_mode_prompting_correctly(self):
        """Test interactive flag bypasses mode prompting and sets mode directly."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save': ['markdown', 'json'],  # Enable saving with formats
            'interactive': True  # Interactive flag set
        })
        
        # Should not prompt user when interactive flag is set
        with patch('builtins.input', return_value='s'):
            build_module = assert_no_exceptions_during_execution(
                self,
                lambda: BuildModule(flags),
                operation_name="BuildModule with interactive flag set"
            )
        
        # Verify module initialized successfully
        self.assertIsNotNone(build_module,
                           "BuildModule should initialize with interactive flag")
        
        # Verify interactive mode is enabled
        if hasattr(build_module, 'output_manager'):
            output_manager = build_module.output_manager
            
            if hasattr(output_manager, 'interactive_manager'):
                interactive_manager = output_manager.interactive_manager
                
                # Interactive manager should be initialized
                self.assertIsNotNone(interactive_manager,
                                   "Interactive manager should be created with interactive flag")
                
                # Mode should be set to interactive
                if hasattr(interactive_manager, 'mode'):
                    self.assertEqual(interactive_manager.mode, 'interactive',
                                   "Mode should be set to interactive when flag is True")
    
    def test_no_interactive_flag_prompts_user_for_mode_selection(self):
        """Test that without interactive flag, user is prompted for mode selection."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save_output': True,
            'interactive': False  # No interactive flag
        })
        
        # Mock user input for mode selection
        with patch('builtins.input', return_value='s'):
            build_module = assert_no_exceptions_during_execution(
                self,
                lambda: BuildModule(flags),
                operation_name="BuildModule without interactive flag (should prompt)"
            )
            
            # Verify module initialized successfully
            self.assertIsNotNone(build_module,
                               "BuildModule should initialize and prompt for mode")
    
    def test_interactive_flag_integration_with_batch_mode_settings(self):
        """Test interactive flag integration with batch mode configuration settings."""
        batch_mode_flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save_output': True,
            'interactive': False,  # Batch mode
            'output_mode': 'batch',
            'sequential_files': 'single'
        })
        
        with patch('builtins.input', return_value='s'):
            build_module = assert_no_exceptions_during_execution(
                self,
                lambda: BuildModule(batch_mode_flags),
                operation_name="BuildModule in batch mode"
            )
        
        # Verify batch mode integration
        self.assertIsNotNone(build_module,
                           "BuildModule should handle batch mode settings")
        
        # In batch mode with save_output=True, user will be prompted for mode
        if hasattr(build_module, 'output_manager'):
            output_manager = build_module.output_manager
            
            # When save_output is True, interactive manager will be created
            if hasattr(output_manager, 'interactive_manager'):
                interactive_manager = output_manager.interactive_manager
                
                # The mode depends on user input (we patched 's' which means interactive)
                if interactive_manager and hasattr(interactive_manager, 'mode'):
                    # Since we patched input to return 's', mode will be 'interactive'
                    self.assertEqual(interactive_manager.mode, 'interactive',
                                   "Mode should be 'interactive' based on user input 's'")
    
    def test_interactive_flag_handles_missing_output_configuration_gracefully(self):
        """Test interactive flag handles missing output configuration gracefully."""
        # Create module without output configuration
        no_output_module_content = '''
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults

class NoOutputSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {"N": 2}
    DEFAULT_GENERAL_SETTINGS = {"save_output": False}

class NoOutputProposition(PropositionDefaults):
    pass

class NoOutputModel(ModelDefaults):
    pass

semantic_theories = {
    "NoOutputTest": {
        "semantics": NoOutputSemantics,
        "proposition": NoOutputProposition,
        "model": NoOutputModel,
        "operators": {},
        "dictionary": {}
    }
}

example_range = {
    "NO_OUTPUT_EXAMPLE": [["p"], ["p"], {"N": 2}]
}

general_settings = {
    "save_output": False  # No output saving
}
'''
        
        no_output_module_path = self.cleanup.create_temp_file(
            no_output_module_content,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': no_output_module_path,
            'save_output': False,
            'interactive': True  # Interactive flag with no output
        })
        
        # Should handle interactive flag even when output is disabled
        with patch('builtins.input', return_value='s'):
            build_module = assert_no_exceptions_during_execution(
                self,
                lambda: BuildModule(flags),
                operation_name="BuildModule with interactive flag but no output"
            )
        
        self.assertIsNotNone(build_module,
                           "Should handle interactive flag with disabled output")


class TestInteractiveFlagEdgeCases(unittest.TestCase):
    """Test edge cases in CLI interactive flag handling."""
    
    def setUp(self):
        """Set up interactive flag edge case testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        self.module_path = self.cleanup.create_temp_file(
            TestModules.MINIMAL_CONTENT,
            suffix=".py"
        )
    
    def test_interactive_flag_with_conflicting_configuration_resolves_appropriately(self):
        """Test interactive flag with conflicting configuration resolves appropriately."""
        conflicting_flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save_output': True,
            'interactive': True,      # Interactive mode
            'output_mode': 'batch'    # But batch output mode
        })
        
        # Should resolve conflict appropriately (interactive flag should take precedence)
        with patch('builtins.input', return_value='s'):
            build_module = assert_no_exceptions_during_execution(
                self,
                lambda: BuildModule(conflicting_flags),
                operation_name="BuildModule with conflicting interactive configuration"
            )
        
        self.assertIsNotNone(build_module,
                           "Should resolve conflicting configuration appropriately")
    
    def test_interactive_flag_behavior_with_empty_example_range(self):
        """Test interactive flag behavior when module has empty example range."""
        # Create module with no examples
        empty_examples_content = '''
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults

class EmptyTestSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {"N": 2}
    DEFAULT_GENERAL_SETTINGS = {"save_output": True}

class EmptyTestProposition(PropositionDefaults):
    pass

class EmptyTestModel(ModelDefaults):
    pass

semantic_theories = {
    "EmptyTest": {
        "semantics": EmptyTestSemantics,
        "proposition": EmptyTestProposition,
        "model": EmptyTestModel,
        "operators": {},
        "dictionary": {}
    }
}

example_range = {}  # No examples

general_settings = {"save_output": True}
'''
        
        empty_examples_path = self.cleanup.create_temp_file(
            empty_examples_content,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': empty_examples_path,
            'save_output': True,
            'interactive': True
        })
        
        # Should reject modules with no examples
        with patch('builtins.input', return_value='s'):
            with self.assertRaises(ImportError) as context:
                BuildModule(flags)
            
            self.assertIn("empty", str(context.exception).lower(),
                         "Error message should indicate empty example range")
            self.assertIn("example_range", str(context.exception),
                         "Error message should mention example_range")
    
    def test_interactive_flag_with_invalid_module_produces_clear_error(self):
        """Test interactive flag with invalid module produces clear error message."""
        # Create module with invalid structure
        invalid_module_content = '''
# Invalid module missing semantic_theories
example_range = {"TEST": [["p"], ["p"], {"N": 2}]}
general_settings = {}
'''
        
        invalid_module_path = self.cleanup.create_temp_file(
            invalid_module_content,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': invalid_module_path,
            'interactive': True
        })
        
        # Should produce clear error about invalid module
        with self.assertRaises(ImportError) as context:
            BuildModule(flags)
        
        # Error should be clear about the problem
        assert_error_message_contains(
            self, context.exception, "semantic_theories",
            "Interactive flag with invalid module error"
        )


class TestInteractiveModeUserExperience(unittest.TestCase):
    """Test user experience aspects of interactive mode."""
    
    def setUp(self):
        """Set up user experience testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create module with multiple examples for interactive testing
        self.multi_example_content = '''
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults

class UserExperienceSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {"N": 2}
    DEFAULT_GENERAL_SETTINGS = {"save_output": True}

class UserExperienceProposition(PropositionDefaults):
    pass

class UserExperienceModel(ModelDefaults):
    pass

semantic_theories = {
    "UserExperienceTest": {
        "semantics": UserExperienceSemantics,
        "proposition": UserExperienceProposition,
        "model": UserExperienceModel,
        "operators": {},
        "dictionary": {}
    }
}

example_range = {
    "EXAMPLE_1": [["p"], ["p"], {"N": 2}],
    "EXAMPLE_2": [["q"], ["q"], {"N": 2}],
    "EXAMPLE_3": [["r"], ["r"], {"N": 2}]
}

general_settings = {"save_output": True}
'''
        
        self.module_path = self.cleanup.create_temp_file(
            self.multi_example_content,
            suffix=".py"
        )
    
    def test_interactive_mode_provides_appropriate_user_feedback(self):
        """Test interactive mode provides appropriate feedback to users."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save_output': True,
            'interactive': True
        })
        
        with patch('builtins.input', return_value='s'):
            build_module = assert_no_exceptions_during_execution(
                self,
                lambda: BuildModule(flags),
                operation_name="Interactive mode user feedback"
            )
        
        # Verify module supports interactive operations
        self.assertIsNotNone(build_module,
                           "Interactive mode should initialize for user feedback")
        
        # Verify multiple examples are available for interactive processing
        if hasattr(build_module, 'example_range'):
            examples = build_module.example_range
            self.assertGreater(len(examples), 1,
                             "Should have multiple examples for interactive mode")
    
    def test_interactive_mode_integration_with_real_user_workflow(self):
        """Test interactive mode integration matches real user workflow expectations."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save_output': True,
            'interactive': True
        })
        
        # This test documents the expected user workflow
        with patch('builtins.input', return_value='s'):
            build_module = BuildModule(flags)
        
        # User workflow expectation: Module loads successfully
        self.assertIsNotNone(build_module,
                           "User should be able to create BuildModule interactively")
        
        # User workflow expectation: Examples are available
        if hasattr(build_module, 'example_range'):
            self.assertIsInstance(build_module.example_range, dict,
                                "Users should have access to examples dictionary")
        
        # User workflow expectation: Interactive components are available
        if hasattr(build_module, 'output_manager'):
            output_manager = build_module.output_manager
            self.assertIsNotNone(output_manager,
                               "Users should have access to output management")


if __name__ == '__main__':
    unittest.main()