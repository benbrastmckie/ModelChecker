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
        """Test state formatting with color emojis."""
        # Test possible state
        result = self.formatter.format_state_type("s0", "possible")
        assert result == "🟢 s0 (Possible)"
        
        # Test impossible state
        result = self.formatter.format_state_type("s1", "impossible")
        assert result == "🔴 s1 (Impossible)"
        
        # Test world state
        result = self.formatter.format_state_type("s2", "world")
        assert result == "🔵 s2 (World State)"
        
        # Test evaluation world
        result = self.formatter.format_state_type("s3", "evaluation")
        assert result == "⭐ s3 (Evaluation World)"
        
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
        
    def test_format_example_header(self):
        """Test example header formatting."""
        example_data = {
            "example": "test_example",
            "theory": "logos",
            "has_model": True
        }
        
        result = self.formatter._format_header(example_data)
        
        assert "## test_example" in result
        assert "**Theory**: logos" in result
        assert "**Model Found**: Yes" in result
        
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
        
    def test_format_states_section(self):
        """Test states section formatting."""
        example_data = {
            "example": "test",
            "theory": "logos",
            "has_model": True,
            "evaluation_world": "s1",
            "states": {
                "possible": ["s0", "s1", "s2"],
                "impossible": ["s3"],
                "worlds": ["s1", "s2"]
            }
        }
        
        result = self.formatter._format_states(example_data)
        
        # Check section header
        assert "### States" in result
        
        # Check evaluation world is marked
        assert "⭐ s1 (Evaluation World)" in result or "s1 [EVALUATION]" in result
        
        # Check world states
        assert "🔵 s2 (World State)" in result or "s2 [WORLD]" in result
        
        # Check possible non-world state
        assert "🟢 s0 (Possible)" in result or "s0 [POSSIBLE]" in result
        
        # Check impossible state
        assert "🔴 s3 (Impossible)" in result or "s3 [IMPOSSIBLE]" in result
        
    def test_format_relations_section(self):
        """Test relations section formatting."""
        example_data = {
            "relations": {
                "R": {
                    "s1": ["s1", "s2"],
                    "s2": ["s1"]
                }
            }
        }
        
        result = self.formatter._format_relations(example_data)
        
        assert "### Relations" in result
        assert "#### R Relation" in result
        assert "- s1 → s1, s2" in result
        assert "- s2 → s1" in result
        
    def test_format_propositions_section(self):
        """Test propositions section formatting."""
        example_data = {
            "propositions": {
                "p": {"s1": True, "s2": False},
                "q": {"s1": False, "s2": True}
            }
        }
        
        result = self.formatter._format_propositions(example_data)
        
        assert "### Propositions" in result
        assert "- **p**: s1 ✓, s2 ✗" in result
        assert "- **q**: s1 ✗, s2 ✓" in result
        
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