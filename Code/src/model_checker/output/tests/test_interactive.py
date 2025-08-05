"""Tests for interactive save manager."""

import pytest
from unittest.mock import Mock, patch, MagicMock
import os
import tempfile
import shutil

from model_checker.output.interactive import InteractiveSaveManager


class TestInteractiveSaveManager:
    """Test InteractiveSaveManager functionality."""
    
    def setup_method(self):
        """Create temporary directory for tests."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
        os.chdir(self.temp_dir)
        
    def teardown_method(self):
        """Clean up temporary directory."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir)
    
    def test_initialization(self):
        """Test manager initialization."""
        manager = InteractiveSaveManager()
        assert manager.mode is None
        assert manager.current_example is None
        assert manager.model_count == {}
        
    @patch('model_checker.output.interactive.prompt_choice')
    def test_prompt_save_mode(self, mock_choice):
        """Test save mode prompting."""
        manager = InteractiveSaveManager()
        
        # Test batch mode selection
        mock_choice.return_value = 'batch'
        mode = manager.prompt_save_mode()
        assert mode == 'batch'
        assert manager.mode == 'batch'
        mock_choice.assert_called_with(
            "Select save mode:",
            ['batch - Save all at end', 'interactive - Prompt after each model']
        )
        
        # Test interactive mode selection
        mock_choice.return_value = 'interactive'
        mode = manager.prompt_save_mode()
        assert mode == 'interactive'
        assert manager.mode == 'interactive'
        
    @patch('model_checker.output.interactive.prompt_yes_no')
    def test_prompt_save_model(self, mock_yes_no):
        """Test save model prompting."""
        manager = InteractiveSaveManager()
        manager.mode = 'interactive'
        
        # Test yes response
        mock_yes_no.return_value = True
        result = manager.prompt_save_model("TEST_EXAMPLE")
        assert result is True
        mock_yes_no.assert_called_with(
            "\nSave model for TEST_EXAMPLE?",
            default=True
        )
        
        # Test no response
        mock_yes_no.return_value = False
        result = manager.prompt_save_model("OTHER_EXAMPLE")
        assert result is False
        
    def test_prompt_save_model_batch_mode(self):
        """Test that batch mode always returns True without prompting."""
        manager = InteractiveSaveManager()
        manager.mode = 'batch'
        
        with patch('model_checker.output.interactive.prompt_yes_no') as mock_yes_no:
            result = manager.prompt_save_model("TEST_EXAMPLE")
            assert result is True
            mock_yes_no.assert_not_called()
            
    @patch('model_checker.output.interactive.prompt_yes_no')
    def test_prompt_find_more_models(self, mock_yes_no):
        """Test prompting for additional models."""
        manager = InteractiveSaveManager()
        manager.mode = 'interactive'
        
        # Test yes response
        mock_yes_no.return_value = True
        result = manager.prompt_find_more_models()
        assert result is True
        mock_yes_no.assert_called_with(
            "Find additional models?",
            default=False
        )
        
        # Test no response
        mock_yes_no.return_value = False
        result = manager.prompt_find_more_models()
        assert result is False
        
    def test_prompt_find_more_batch_mode(self):
        """Test that batch mode returns False without prompting."""
        manager = InteractiveSaveManager()
        manager.mode = 'batch'
        
        with patch('model_checker.output.interactive.prompt_yes_no') as mock_yes_no:
            result = manager.prompt_find_more_models()
            assert result is False
            mock_yes_no.assert_not_called()
            
    @patch('model_checker.output.interactive.prompt_yes_no')
    @patch('builtins.print')
    def test_prompt_change_directory(self, mock_print, mock_yes_no):
        """Test directory change prompting."""
        manager = InteractiveSaveManager()
        test_path = "/test/output/directory"
        
        # Test yes response
        mock_yes_no.return_value = True
        result = manager.prompt_change_directory(test_path)
        assert result is True
        
        # Check prompts
        mock_yes_no.assert_called_with(
            "Change to output directory?",
            default=False
        )
        
        # Check cd command display
        mock_print.assert_any_call(f"\nAll models saved to: {test_path}")
        mock_print.assert_any_call("To change directory, run:")
        mock_print.assert_any_call(f"  cd {test_path}")
        
    def test_track_model_count(self):
        """Test model counting functionality."""
        manager = InteractiveSaveManager()
        
        # First model for example
        count = manager.get_next_model_number("EXAMPLE_1")
        assert count == 1
        assert manager.model_count["EXAMPLE_1"] == 1
        
        # Second model for same example
        count = manager.get_next_model_number("EXAMPLE_1")
        assert count == 2
        assert manager.model_count["EXAMPLE_1"] == 2
        
        # First model for different example
        count = manager.get_next_model_number("EXAMPLE_2")
        assert count == 1
        assert manager.model_count["EXAMPLE_2"] == 1
        
    def test_reset_for_new_example(self):
        """Test resetting state for new example."""
        manager = InteractiveSaveManager()
        manager.current_example = "OLD_EXAMPLE"
        manager.model_count["OLD_EXAMPLE"] = 3
        
        manager.reset_for_new_example("NEW_EXAMPLE")
        assert manager.current_example == "NEW_EXAMPLE"
        assert "NEW_EXAMPLE" not in manager.model_count
        
    def test_is_interactive_mode(self):
        """Test mode checking."""
        manager = InteractiveSaveManager()
        
        # No mode set
        assert manager.is_interactive() is False
        
        # Batch mode
        manager.mode = 'batch'
        assert manager.is_interactive() is False
        
        # Interactive mode
        manager.mode = 'interactive'
        assert manager.is_interactive() is True
        
    @patch('model_checker.output.interactive.prompt_choice')
    def test_cancelled_mode_selection(self, mock_choice):
        """Test handling cancelled mode selection."""
        manager = InteractiveSaveManager()
        mock_choice.return_value = None  # Cancelled
        
        mode = manager.prompt_save_mode()
        assert mode == 'batch'  # Should default to batch
        assert manager.mode == 'batch'