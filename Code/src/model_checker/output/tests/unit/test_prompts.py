"""Tests for interactive prompt utilities."""

import pytest
from unittest.mock import patch, MagicMock
from io import StringIO

from model_checker.output.prompts import prompt_yes_no, prompt_choice


class TestPromptYesNo:
    """Test yes/no prompt functionality."""
    
    @patch('builtins.input')
    def test_prompt_yes_responses(self, mock_input):
        """Test various affirmative responses."""
        affirmative_responses = ['y', 'Y', 'yes', 'YES', 'Yes']
        
        for response in affirmative_responses:
            mock_input.return_value = response
            result = prompt_yes_no("Test prompt?")
            assert result is True, f"'{response}' should return True"
            
    @patch('builtins.input')
    def test_prompt_no_responses(self, mock_input):
        """Test various negative responses."""
        negative_responses = ['n', 'N', 'no', 'NO', 'No']
        
        for response in negative_responses:
            mock_input.return_value = response
            result = prompt_yes_no("Test prompt?")
            assert result is False, f"'{response}' should return False"
            
    @patch('builtins.input')
    def test_prompt_default_on_empty(self, mock_input):
        """Test default value on empty input."""
        mock_input.return_value = ''
        
        # Test default False
        result = prompt_yes_no("Test prompt?", default=False)
        assert result is False
        
        # Test default True
        result = prompt_yes_no("Test prompt?", default=True)
        assert result is True
        
    @patch('builtins.input')
    def test_prompt_invalid_input_retry(self, mock_input):
        """Test retry on invalid input."""
        # First invalid, then valid
        mock_input.side_effect = ['invalid', 'maybe', 'y']
        
        result = prompt_yes_no("Test prompt?")
        assert result is True
        assert mock_input.call_count == 3
        
    @patch('builtins.input')
    def test_prompt_message_display(self, mock_input):
        """Test that prompt message is displayed correctly."""
        mock_input.return_value = 'y'
        
        # Test default True shows (Y/n)
        prompt_yes_no("Save this model?", default=True)
        mock_input.assert_called_with("Save this model? (Y/n): ")
        
        # Test default False shows (y/N)
        prompt_yes_no("Continue?", default=False)
        mock_input.assert_called_with("Continue? (y/N): ")
            
    @patch('builtins.input')
    def test_keyboard_interrupt_handling(self, mock_input):
        """Test handling of Ctrl+C."""
        mock_input.side_effect = KeyboardInterrupt()
        
        result = prompt_yes_no("Test prompt?")
        assert result is False  # Should return False on interrupt
        

class TestPromptChoice:
    """Test choice prompt functionality."""
    
    @patch('builtins.input')
    def test_valid_choice_selection(self, mock_input):
        """Test selecting valid choices."""
        choices = ['batch', 'interactive', 'cancel']
        
        for i, choice in enumerate(choices):
            mock_input.return_value = str(i + 1)
            result = prompt_choice("Select mode:", choices)
            assert result == choice
            
    @patch('builtins.input')
    def test_choice_by_letter(self, mock_input):
        """Test selecting choices by first letter."""
        choices = ['batch', 'interactive', 'cancel']
        mock_input.side_effect = ['b', 'i', 'c']
        
        result = prompt_choice("Select mode:", choices)
        assert result == 'batch'
        
        result = prompt_choice("Select mode:", choices)
        assert result == 'interactive'
        
        result = prompt_choice("Select mode:", choices)
        assert result == 'cancel'
        
    @patch('builtins.input')
    def test_invalid_choice_retry(self, mock_input):
        """Test retry on invalid choice."""
        mock_input.side_effect = ['0', '5', 'x', '2']
        choices = ['batch', 'interactive']
        
        result = prompt_choice("Select mode:", choices)
        assert result == 'interactive'
        assert mock_input.call_count == 4
        
    @patch('builtins.input')
    def test_choice_display_format(self, mock_input):
        """Test choice display formatting."""
        mock_input.return_value = '1'
        choices = ['batch', 'interactive']
        
        with patch('sys.stdout', new_callable=StringIO) as mock_stdout:
            prompt_choice("Select save mode:", choices)
            output = mock_stdout.getvalue()
            
            assert "Select save mode:" in output
            assert "1. batch" in output
            assert "2. interactive" in output
            
        # Check that input was called with correct prompt
        mock_input.assert_called_with("Choice (1-2): ")
            
    @patch('builtins.input')
    def test_single_choice_auto_select(self, mock_input):
        """Test auto-selection with single choice."""
        choices = ['only_option']
        
        # Should not call input when only one choice
        result = prompt_choice("Select:", choices)
        assert result == 'only_option'
        mock_input.assert_not_called()
        
    @patch('builtins.input')
    def test_empty_choices_error(self, mock_input):
        """Test error on empty choices."""
        with pytest.raises(ValueError, match="No choices provided"):
            prompt_choice("Select:", [])
            
    @patch('builtins.input')
    def test_keyboard_interrupt_returns_none(self, mock_input):
        """Test Ctrl+C returns None."""
        mock_input.side_effect = KeyboardInterrupt()
        choices = ['batch', 'interactive']
        
        result = prompt_choice("Select:", choices)
        assert result is None