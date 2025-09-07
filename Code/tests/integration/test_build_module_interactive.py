"""Integration tests for BuildModule with interactive save functionality."""

import os
import tempfile
import shutil
import pytest
from unittest.mock import Mock, MagicMock, patch, call
import sys
from io import StringIO

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


class TestBuildModuleInteractive:
    """Test BuildModule integration with interactive save."""
    
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
    @patch('model_checker.output.interactive.prompt_choice')
    def test_interactive_mode_initialization(self, mock_choice, mock_load):
        """Test BuildModule initializes with interactive mode."""
        # Mock module loading
        mock_module = Mock()
        mock_module.semantic_theories = {"test": {}}
        mock_module.example_range = {}
        mock_module.general_settings = {"save_output": True}
        mock_load.return_value = mock_module
        
        # User selects interactive mode
        mock_choice.return_value = 'interactive - Prompt after each model'
        
        flags = MockFlags(save_output=True)
        module = BuildModule(flags)
        
        # Check interactive manager created and mode prompted
        assert module.output_manager.interactive_manager is not None
        assert module.output_manager.mode == 'interactive'
        mock_choice.assert_called_once()
        
    @patch('model_checker.builder.module.BuildModule._load_module')
    def test_batch_mode_no_prompts(self, mock_load):
        """Test batch mode doesn't create interactive manager."""
        mock_module = Mock()
        mock_module.semantic_theories = {"test": {}}
        mock_module.example_range = {}
        mock_module.general_settings = {"save_output": False}
        mock_load.return_value = mock_module
        
        flags = MockFlags(save_output=False)
        module = BuildModule(flags)
        
        # No interactive manager in batch mode
        assert module.output_manager.interactive_manager is None
        
    @patch('model_checker.builder.module.BuildModule._load_module')
    @patch('model_checker.builder.module.BuildModule.process_example')
    @patch('model_checker.output.interactive.prompt_choice')
    @patch('model_checker.output.interactive.prompt_yes_no')
    def test_interactive_workflow_save_decision(self, mock_yes_no, mock_choice, 
                                               mock_process, mock_load):
        """Test interactive save decision after model found."""
        # Mock module
        mock_module = Mock()
        mock_module.semantic_theories = {"test_theory": {
            "semantics": Mock,
            "proposition": Mock,
            "model": Mock,
            "operators": {},
            "dictionary": {}
        }}
        mock_module.example_range = {
            "EXAMPLE_1": [[], [], {"N": 3, "iterate": 1}]
        }
        mock_module.general_settings = {"save_output": True}
        mock_load.return_value = mock_module
        
        # Mock user choices
        mock_choice.return_value = 'interactive - Prompt after each model'
        mock_yes_no.side_effect = [True, False]  # Save first, don't iterate
        
        # Mock example processing
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_process.return_value = mock_example
        
        flags = MockFlags(save_output=True)
        module = BuildModule(flags)
        
        # Run with capturing
        with patch.object(module.output_manager.interactive_manager, 
                         'prompt_save_model', return_value=True) as mock_save_prompt:
            module.run_examples()
            
            # Verify save was prompted
            mock_save_prompt.assert_called_with("EXAMPLE_1")
            
    @patch('model_checker.builder.module.BuildModule._load_module')
    @patch('model_checker.output.interactive.prompt_choice')
    @patch('model_checker.output.interactive.prompt_yes_no')
    @patch('builtins.print')
    def test_final_directory_prompt(self, mock_print, mock_yes_no, 
                                   mock_choice, mock_load):
        """Test final directory change prompt."""
        # Mock module
        mock_module = Mock()
        mock_module.semantic_theories = {"test": {}}
        mock_module.example_range = {}
        mock_module.general_settings = {"save_output": True}
        mock_load.return_value = mock_module
        
        # Mock choices
        mock_choice.return_value = 'interactive - Prompt after each model'
        mock_yes_no.return_value = True  # Yes to cd
        
        flags = MockFlags(save_output=True)
        module = BuildModule(flags)
        
        # Create output directory
        module.output_manager.create_output_directory()
        output_path = os.path.abspath(module.output_manager.output_dir)
        
        # Run examples (empty, but will still finalize)
        module.run_examples()
        
        # Check cd prompt was called
        mock_yes_no.assert_any_call("Change to output directory?", default=False)
        
        # Check cd command was displayed
        mock_print.assert_any_call(f"  cd {output_path}")
        
    @patch('model_checker.builder.module.BuildModule._load_module')
    @patch('model_checker.output.interactive.prompt_choice')
    def test_interactive_manager_passed_to_output(self, mock_choice, mock_load):
        """Test interactive manager is properly passed to OutputManager."""
        mock_module = Mock()
        mock_module.semantic_theories = {"test": {}}
        mock_module.example_range = {}
        mock_module.general_settings = {"save_output": True}
        mock_load.return_value = mock_module
        
        mock_choice.return_value = 'interactive - Prompt after each model'
        
        flags = MockFlags(save_output=True)
        module = BuildModule(flags)
        
        # Verify connection
        assert module.interactive_manager is not None
        assert module.output_manager.interactive_manager is module.interactive_manager
        assert module.interactive_manager.mode == 'interactive'
        
    @patch('model_checker.builder.module.BuildModule._load_module')
    @patch('model_checker.builder.module.BuildModule._capture_and_save_output')
    @patch('model_checker.output.interactive.prompt_choice')
    @patch('model_checker.output.interactive.prompt_yes_no')
    def test_model_saved_only_when_prompted_yes(self, mock_yes_no, mock_choice,
                                               mock_capture, mock_load):
        """Test model is saved only when user says yes."""
        # Mock module
        mock_module = Mock()
        mock_module.semantic_theories = {"test": {
            "semantics": Mock,
            "proposition": Mock,
            "model": Mock,
            "operators": {},
            "dictionary": {}
        }}
        mock_module.example_range = {
            "SAVE_ME": [[], [], {"N": 3}],
            "SKIP_ME": [[], [], {"N": 3}]
        }
        mock_module.general_settings = {"save_output": True}
        mock_load.return_value = mock_module
        
        # Mock choices
        mock_choice.return_value = 'interactive - Prompt after each model'
        
        # Create module
        flags = MockFlags(save_output=True)
        module = BuildModule(flags)
        
        # Mock save decisions
        module.interactive_manager.prompt_save_model = Mock(
            side_effect=[True, False]  # Save first, skip second
        )
        
        # Track calls to save
        save_calls = []
        original_save = module.output_manager.save_model_interactive
        
        def track_save(*args, **kwargs):
            save_calls.append(args[0])  # example name
            return original_save(*args, **kwargs)
            
        module.output_manager.save_model_interactive = Mock(side_effect=track_save)
        
        # Process examples (mock the actual processing)
        with patch.object(module, 'process_example') as mock_process:
            mock_example = Mock()
            mock_example.model_structure.z3_model_status = True
            mock_process.return_value = mock_example
            
            module.run_examples()
            
        # Verify only SAVE_ME was saved
        assert len(save_calls) == 1
        assert save_calls[0] == "SAVE_ME"