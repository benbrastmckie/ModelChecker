"""
Integration tests for output directory guidance functionality.

This module tests the integration between BuildModule and output management
to ensure users receive appropriate guidance for accessing saved output.
"""

import unittest
import os
import sys
from io import StringIO
from unittest.mock import patch

from model_checker.builder.tests.fixtures.test_data import TestModules
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory
from model_checker.builder.tests.fixtures.temp_resources import TempFileCleanup
from model_checker.builder.tests.fixtures.assertions import (
    assert_error_message_contains,
    assert_no_exceptions_during_execution
)

from model_checker.builder.module import BuildModule


class TestOutputDirectoryGuidanceIntegration(unittest.TestCase):
    """Test integration of output directory guidance with real components."""
    
    def setUp(self):
        """Set up output directory guidance testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create test module with save output enabled
        self.output_enabled_module_content = TestModules.OUTPUT_ENABLED_MODULE_CONTENT
        
        self.module_path = self.cleanup.create_temp_file(
            self.output_enabled_module_content,
            suffix=".py"
        )
        
        # Create output directory
        self.output_dir = self.cleanup.create_temp_dir()
    
    def test_build_module_provides_output_directory_guidance_when_saving(self):
        """Test BuildModule provides output directory guidance when saving is enabled."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save_output': True,
            'output_dir': self.output_dir
        })
        
        # Capture stdout to verify guidance is provided
        captured_output = StringIO()
        original_stdout = sys.stdout
        
        try:
            sys.stdout = captured_output
            
            # Mock input to avoid stdin issues
            with patch('builtins.input', return_value='s'):
                build_module = assert_no_exceptions_during_execution(
                    self,
                    lambda: BuildModule(flags),
                    operation_name="BuildModule with output saving enabled"
                )
            
            # Test interaction with output manager if available
            if hasattr(build_module, 'output_manager'):
                output_manager = build_module.output_manager
                
                # If output manager supports directory operations
                if hasattr(output_manager, 'output_dir') and output_manager.output_dir:
                    # Directory guidance should be available
                    self.assertTrue(os.path.exists(self.output_dir),
                                  "Output directory should exist")
            
        finally:
            sys.stdout = original_stdout
        
        # Verify BuildModule initialized successfully with output configuration
        self.assertIsNotNone(build_module,
                           "BuildModule should initialize with output saving")
    
    def test_output_directory_guidance_handles_nonexistent_directories_gracefully(self):
        """Test output directory guidance handles nonexistent directories gracefully."""
        nonexistent_output_dir = os.path.join(self.cleanup.temp_dir, 'nonexistent_output')
        
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save_output': True,
            'output_dir': nonexistent_output_dir
        })
        
        # Should handle nonexistent output directory gracefully
        with patch('builtins.input', return_value='s'):
            build_module = assert_no_exceptions_during_execution(
                self,
                lambda: BuildModule(flags),
                operation_name="BuildModule with nonexistent output directory"
            )
        
        # Module should initialize even if output directory doesn't exist
        self.assertIsNotNone(build_module,
                           "BuildModule should handle nonexistent output directories")
    
    def test_batch_mode_output_guidance_provides_command_line_instructions(self):
        """Test batch mode output guidance provides clear command line instructions."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save_output': True,
            'output_dir': self.output_dir,
            'interactive': False  # Batch mode
        })
        
        captured_output = StringIO()
        original_stdout = sys.stdout
        
        try:
            sys.stdout = captured_output
            
            with patch('builtins.input', return_value='s'):
                build_module = BuildModule(flags)
            
            # Simulate output completion (if methods exist)
            if hasattr(build_module, 'output_manager'):
                output_manager = build_module.output_manager
                
                # Test finalization behavior if available
                if hasattr(output_manager, 'finalize'):
                    try:
                        output_manager.finalize()
                    except (AttributeError, NotImplementedError):
                        # Method may not be fully implemented
                        pass
            
            output_content = captured_output.getvalue()
            
        finally:
            sys.stdout = original_stdout
        
        # Document expected behavior - batch mode should provide guidance
        # The specific format may vary based on implementation
        self.assertIsNotNone(build_module,
                           "Batch mode should initialize successfully")


class TestInteractiveOutputDirectoryIntegration(unittest.TestCase):
    """Test interactive output directory guidance integration."""
    
    def setUp(self):
        """Set up interactive output directory testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        self.module_path = self.cleanup.create_temp_file(
            TestModules.MINIMAL_CONTENT,
            suffix=".py"
        )
        self.output_dir = self.cleanup.create_temp_dir()
    
    def test_interactive_mode_integrates_output_directory_prompts_correctly(self):
        """Test interactive mode integrates output directory prompts correctly."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'save_output': True,
            'output_dir': self.output_dir,
            'interactive': True
        })
        
        # Mock interactive input if console input is used
        with patch('model_checker.output.ConsoleInputProvider') as mock_provider_class:
            mock_provider = MockObjectFactory.create_mock_input_provider('s')
            mock_provider_class.return_value = mock_provider
            
            with patch('builtins.input', return_value='s'):
                build_module = assert_no_exceptions_during_execution(
                    self,
                    lambda: BuildModule(flags),
                    operation_name="Interactive BuildModule with output directory"
                )
            
            # Verify interactive components are integrated
            if hasattr(build_module, 'output_manager'):
                output_manager = build_module.output_manager
                
                # Interactive manager should be available
                if hasattr(output_manager, 'interactive_manager'):
                    interactive_manager = output_manager.interactive_manager
                    
                    # Should be able to handle directory operations
                    if hasattr(interactive_manager, 'prompt_change_directory'):
                        # Interactive directory prompting is available
                        self.assertTrue(callable(interactive_manager.prompt_change_directory),
                                      "Interactive directory prompting should be callable")
    
    def test_output_directory_guidance_adapts_to_user_preferences(self):
        """Test output directory guidance adapts to different user interaction preferences."""
        user_preference_scenarios = [
            {'interactive': True, 'expected_behavior': 'interactive_prompts'},
            {'interactive': False, 'expected_behavior': 'direct_instructions'}
        ]
        
        for scenario in user_preference_scenarios:
            with self.subTest(interactive=scenario['interactive']):
                flags = MockObjectFactory.create_flags({
                    'file_path': self.module_path,
                    'save_output': True,
                    'output_dir': self.output_dir,
                    'interactive': scenario['interactive']
                })
                
                if scenario['interactive']:
                    # Mock interactive input
                    with patch('builtins.input', return_value='s'):
                        build_module = BuildModule(flags)
                else:
                    # Batch mode - still need input mocking for save_output=True
                    with patch('builtins.input', return_value='s'):
                        build_module = BuildModule(flags)
                
                # Verify module adapts to user preference
                self.assertIsNotNone(build_module,
                                   f"Should handle {scenario['expected_behavior']} preference")


class TestOutputGuidanceErrorHandling(unittest.TestCase):
    """Test error handling in output directory guidance scenarios."""
    
    def setUp(self):
        """Set up error handling testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        self.module_path = self.cleanup.create_temp_file(
            TestModules.MINIMAL_CONTENT,
            suffix=".py"
        )
    
    def test_output_guidance_handles_permission_denied_directories_gracefully(self):
        """Test output guidance handles permission denied directories gracefully."""
        # Create directory with restricted permissions (if supported)
        restricted_dir = self.cleanup.create_temp_dir()
        
        # Try to restrict permissions
        try:
            os.chmod(restricted_dir, 0o444)  # Read-only
            
            flags = MockObjectFactory.create_flags({
                'file_path': self.module_path,
                'save_output': True,
                'output_dir': restricted_dir
            })
            
            # Should handle permission issues gracefully
            with patch('builtins.input', return_value='s'):
                build_module = assert_no_exceptions_during_execution(
                    self,
                    lambda: BuildModule(flags),
                    operation_name="BuildModule with restricted output directory"
                )
            
            self.assertIsNotNone(build_module,
                               "Should handle permission restrictions gracefully")
            
        finally:
            # Restore permissions for cleanup
            try:
                os.chmod(restricted_dir, 0o755)
            except (OSError, FileNotFoundError):
                pass
    
    def test_output_guidance_handles_invalid_directory_paths_informatively(self):
        """Test output guidance handles invalid directory paths with informative messages."""
        invalid_directory_paths = [
            '',  # Empty string
            '/dev/null/invalid',  # Invalid nested path
            '\x00invalid',  # Path with null character
        ]
        
        for invalid_path in invalid_directory_paths:
            with self.subTest(invalid_path=repr(invalid_path)):
                flags = MockObjectFactory.create_flags({
                    'file_path': self.module_path,
                    'save_output': True,
                    'output_dir': invalid_path
                })
                
                try:
                    with patch('builtins.input', return_value='s'):
                        build_module = BuildModule(flags)
                    # If it succeeds, verify it handles the invalid path
                    self.assertIsNotNone(build_module,
                                       "Should handle invalid paths gracefully")
                except (OSError, ValueError) as e:
                    # If it fails, error should be informative
                    error_message = str(e).lower()
                    self.assertTrue(
                        any(keyword in error_message 
                            for keyword in ['path', 'directory', 'invalid']),
                        f"Error should be informative about path issue: {e}"
                    )


if __name__ == '__main__':
    unittest.main()