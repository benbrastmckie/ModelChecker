"""Tests for CLI interactive flag integration with BuildModule."""

import os
import tempfile
import shutil
import pytest
from unittest.mock import Mock, patch, MagicMock

from model_checker.builder.module import BuildModule
from model_checker.output import InteractiveSaveManager


class MockFlags:
    """Mock command-line flags."""
    def __init__(self, save_output=True, interactive=False):
        self.file_path = "test_examples.py"
        self.save_output = save_output
        self.interactive = interactive
        self.output_mode = 'batch'
        self.sequential_files = 'multiple'
        self.print_impossible = False
        self.print_constraints = False
        self.print_z3 = False
        self.maximize = False


class TestCLIInteractiveIntegration:
    """Test CLI interactive flag integration with BuildModule."""
    
    def setup_method(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
        os.chdir(self.temp_dir)
        
    def teardown_method(self):
        """Clean up."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir)
        
    @patch('model_checker.builder.module.BuildModule._load_module')
    def test_interactive_flag_sets_mode_directly(self, mock_load):
        """Test that interactive flag bypasses mode prompt."""
        # Mock module
        mock_module = Mock()
        
        # Create proper semantics mock
        mock_semantics = Mock()
        mock_semantics.DEFAULT_EXAMPLE_SETTINGS = {"N": 5}
        mock_semantics.DEFAULT_GENERAL_SETTINGS = {"save_output": True}
        
        mock_module.semantic_theories = {"test": {
            "semantics": mock_semantics,
            "proposition": Mock,
            "model": Mock,
            "operators": {},
            "dictionary": {}
        }}
        mock_module.example_range = {}
        mock_module.general_settings = {"save_output": True}
        mock_load.return_value = mock_module
        
        # Create module with interactive flag
        flags = MockFlags(save_output=True, interactive=True)
        
        # Mock prompt_save_mode to track if it's called
        with patch.object(InteractiveSaveManager, 'prompt_save_mode') as mock_prompt:
            module = BuildModule(flags)
            
            # Verify mode was set directly without prompting
            assert module.interactive_manager is not None
            assert module.interactive_manager.mode == 'interactive'
            mock_prompt.assert_not_called()
            
    @patch('model_checker.builder.module.BuildModule._load_module')
    def test_no_interactive_flag_prompts_user(self, mock_load):
        """Test that without interactive flag, user is prompted."""
        # Mock module
        mock_module = Mock()
        
        # Create proper semantics mock
        mock_semantics = Mock()
        mock_semantics.DEFAULT_EXAMPLE_SETTINGS = {"N": 5}
        mock_semantics.DEFAULT_GENERAL_SETTINGS = {"save_output": True}
        
        mock_module.semantic_theories = {"test": {
            "semantics": mock_semantics,
            "proposition": Mock,
            "model": Mock,
            "operators": {},
            "dictionary": {}
        }}
        mock_module.example_range = {}
        mock_module.general_settings = {"save_output": True}
        mock_load.return_value = mock_module
        
        # Mock input provider for batch mode
        with patch('model_checker.output.ConsoleInputProvider') as mock_provider_class:
            mock_provider = Mock()
            mock_provider.get_input.return_value = 'a'  # Batch mode
            mock_provider_class.return_value = mock_provider
            
            # Create module without interactive flag
            flags = MockFlags(save_output=True, interactive=False)
            module = BuildModule(flags)
            
            # Verify prompt was called
            assert module.interactive_manager is not None
            assert module.interactive_manager.mode == 'batch'
            mock_provider.get_input.assert_called_once_with("Save all examples (a) or run in sequence (s)? ")
        
    @patch('model_checker.builder.module.BuildModule._load_module')
    def test_interactive_flag_without_save_output(self, mock_load):
        """Test interactive flag has no effect without save_output."""
        # Mock module
        mock_module = Mock()
        
        # Create proper semantics mock
        mock_semantics = Mock()
        mock_semantics.DEFAULT_EXAMPLE_SETTINGS = {"N": 5}
        mock_semantics.DEFAULT_GENERAL_SETTINGS = {"save_output": False}
        
        mock_module.semantic_theories = {"test": {
            "semantics": mock_semantics,
            "proposition": Mock,
            "model": Mock,
            "operators": {},
            "dictionary": {}
        }}
        mock_module.example_range = {}
        mock_module.general_settings = {"save_output": False}
        mock_load.return_value = mock_module
        
        # Create module with interactive flag but no save_output
        flags = MockFlags(save_output=False, interactive=True)
        module = BuildModule(flags)
        
        # Verify no interactive manager created
        assert module.interactive_manager is None
        assert module.output_manager.interactive_manager is None
        
    @patch('model_checker.builder.module.BuildModule._load_module')
    def test_interactive_flag_with_output_manager(self, mock_load):
        """Test interactive flag properly configures OutputManager."""
        # Mock module
        mock_module = Mock()
        
        # Create proper semantics mock
        mock_semantics = Mock()
        mock_semantics.DEFAULT_EXAMPLE_SETTINGS = {"N": 5}
        mock_semantics.DEFAULT_GENERAL_SETTINGS = {"save_output": True}
        
        mock_module.semantic_theories = {"test": {
            "semantics": mock_semantics,
            "proposition": Mock,
            "model": Mock,
            "operators": {},
            "dictionary": {}
        }}
        mock_module.example_range = {}
        mock_module.general_settings = {"save_output": True}
        mock_load.return_value = mock_module
        
        # Create module with interactive flag
        flags = MockFlags(save_output=True, interactive=True)
        module = BuildModule(flags)
        
        # Verify OutputManager has interactive mode
        assert module.output_manager.mode == 'interactive'
        assert module.output_manager.interactive_manager is module.interactive_manager
        
    def test_set_mode_validation(self):
        """Test set_mode validates input."""
        from model_checker.output import MockInputProvider
        manager = InteractiveSaveManager(MockInputProvider([]))
        
        # Valid modes
        manager.set_mode('batch')
        assert manager.mode == 'batch'
        
        manager.set_mode('interactive')
        assert manager.mode == 'interactive'
        
        # Invalid mode
        with pytest.raises(ValueError) as exc_info:
            manager.set_mode('invalid')
        assert "Invalid mode: invalid" in str(exc_info.value)