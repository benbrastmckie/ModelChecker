"""Tests for markdown formatting of model output."""

import pytest
from unittest.mock import Mock, MagicMock

from model_checker.output.formatters import MarkdownFormatter


class TestMarkdownFormatter:
    """Test markdown generation for examples."""
    
    def setup_method(self):
        """Create formatter and test data."""
        self.formatter = MarkdownFormatter(use_colors=True)
        self.formatter_no_color = MarkdownFormatter(use_colors=False)
        
    def test_format_state_type_with_colors(self):
        """Test state formatting with indicators."""
        # Test possible state
        result = self.formatter.format_state_type("s0", "possible")
        assert result == "• s0"
        
        # Test impossible state
        result = self.formatter.format_state_type("s1", "impossible")
        assert result == "○ s1"
        
        # Test world state
        result = self.formatter.format_state_type("s2", "world")
        assert result == "▪ s2"
        
        # Test evaluation world
        result = self.formatter.format_state_type("s3", "evaluation")
        assert result == "★ s3"
        
    def test_format_state_type_no_colors(self):
        """Test state formatting without colors."""
        # Test possible state
        result = self.formatter_no_color.format_state_type("s0", "possible")
        assert result == "s0 [POSSIBLE]"
        
        # Test impossible state
        result = self.formatter_no_color.format_state_type("s1", "impossible")
        assert result == "s1 [IMPOSSIBLE]"
        
        # Test world state
        result = self.formatter_no_color.format_state_type("s2", "world")
        assert result == "s2 [WORLD]"
        
        # Test evaluation world
        result = self.formatter_no_color.format_state_type("s3", "evaluation")
        assert result == "s3 [EVALUATION]"
        
    def test_format_example_with_model(self):
        """Test formatting when model is found."""
        example_data = {
            "example": "test_example",
            "theory": "logos",
            "has_model": True
        }
        
        # When raw output is provided, it should be returned as-is
        raw_output = "Test model output\nWith multiple lines"
        result = self.formatter.format_example(example_data, raw_output)
        assert result == raw_output.strip()
        
    def test_format_example_no_model(self):
        """Test formatting when no model found."""
        example_data = {
            "example": "no_model",
            "theory": "bimodal",
            "has_model": False,
            "evaluation_world": None,
            "states": {"possible": [], "impossible": [], "worlds": []},
            "relations": {},
            "propositions": {}
        }
        
        result = self.formatter.format_example(example_data, "")
        
        assert result == "EXAMPLE no_model: there is no countermodel."
        
    def test_format_batch(self):
        """Test batch formatting combines examples."""
        examples = [
            "Example 1 output",
            "Example 2 output",
            "Example 3 output"
        ]
        
        result = self.formatter.format_batch(examples)
        
        # Check all examples are present
        assert "Example 1 output" in result
        assert "Example 2 output" in result
        assert "Example 3 output" in result
        
        # Check separators
        assert "---" in result
        
    def test_get_file_extension(self):
        """Test file extension is correct."""
        assert self.formatter.get_file_extension() == 'md'
        
    def test_format_example_with_empty_output(self):
        """Test formatting when no output provided."""
        example_data = {
            "example": "test_empty",
            "has_model": True
        }
        
        # With empty output but model found
        result = self.formatter.format_example(example_data, "")
        assert result == "EXAMPLE test_empty: model found but no output available."
        
    def test_format_complete_example(self):
        """Test formatting a complete example."""
        example_data = {
            "example": "complete_test",
            "theory": "logos",
            "has_model": True,
            "evaluation_world": "s1",
            "states": {
                "possible": ["s0", "s1", "s2"],
                "impossible": ["s3"],
                "worlds": ["s1", "s2"]
            },
            "relations": {
                "R": {"s1": ["s1", "s2"], "s2": ["s1"]}
            },
            "propositions": {
                "p": {"s1": True, "s2": False}
            }
        }
        
        model_output = "Original model output here..."
        
        result = self.formatter.format_example(example_data, model_output)
        
        # Should just return the raw output
        assert result == "Original model output here..."