"""Tests for sequential save manager functionality."""

import pytest
from unittest.mock import Mock, patch
from model_checker.output.sequential_manager import SequentialSaveManager
from model_checker.output.input_provider import MockInputProvider


class TestSequentialSaveManager:
    """Test SequentialSaveManager functionality."""
    
    def test_initialization(self):
        """Test manager initialization."""
        input_provider = MockInputProvider([])
        manager = SequentialSaveManager(input_provider)
        assert manager.input_provider is input_provider
        assert manager.saved_count == {}
    
    @patch('model_checker.output.sequential_manager.prompt_yes_no')
    def test_should_save_yes(self, mock_yes_no):
        """Test should_save returns True when user says yes."""
        mock_yes_no.return_value = True
        manager = SequentialSaveManager()
        
        result = manager.should_save("TEST_EXAMPLE")
        
        assert result is True
        mock_yes_no.assert_called_with(
            "\nSave model for TEST_EXAMPLE?",
            default=True
        )
    
    @patch('model_checker.output.sequential_manager.prompt_yes_no')
    def test_should_save_no(self, mock_yes_no):
        """Test should_save returns False when user says no."""
        mock_yes_no.return_value = False
        manager = SequentialSaveManager()
        
        result = manager.should_save("TEST_EXAMPLE")
        
        assert result is False
    
    @patch('model_checker.output.sequential_manager.prompt_yes_no')
    def test_should_find_more(self, mock_yes_no):
        """Test should_find_more prompting."""
        mock_yes_no.return_value = True
        manager = SequentialSaveManager()
        
        result = manager.should_find_more()
        
        assert result is True
        mock_yes_no.assert_called_with(
            "Find additional models?",
            default=False
        )
    
    def test_get_next_model_number(self):
        """Test model number tracking."""
        manager = SequentialSaveManager()
        
        # First model for example
        assert manager.get_next_model_number("EXAMPLE_1") == 1
        assert manager.saved_count["EXAMPLE_1"] == 1
        
        # Second model for same example
        assert manager.get_next_model_number("EXAMPLE_1") == 2
        assert manager.saved_count["EXAMPLE_1"] == 2
        
        # First model for different example
        assert manager.get_next_model_number("EXAMPLE_2") == 1
        assert manager.saved_count["EXAMPLE_2"] == 1
    
    @patch('model_checker.output.sequential_manager.prompt_yes_no')
    @patch('builtins.print')
    def test_prompt_directory_change(self, mock_print, mock_yes_no):
        """Test directory change prompting."""
        mock_yes_no.return_value = True
        manager = SequentialSaveManager()
        
        result = manager.prompt_directory_change("/test/output")
        
        assert result is True
        mock_print.assert_any_call("\nAll models saved to: /test/output")
        mock_print.assert_any_call("To change directory, run:")
        mock_print.assert_any_call("  cd /test/output")
        mock_yes_no.assert_called_with(
            "Change to output directory?",
            default=False
        )