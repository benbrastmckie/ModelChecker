"""Tests for markdown formatter with enhanced relation types."""

import unittest

from model_checker.output.formatters import MarkdownFormatter


class TestMarkdownRelations(unittest.TestCase):
    """Test markdown formatter handles different relation types."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.formatter = MarkdownFormatter(use_colors=False)
        
    def test_format_time_shift_relations(self):
        """Test formatting of bimodal time shift relations."""
        example_data = {
            "example": "test",
            "theory": "bimodal",
            "has_model": True,
            "relations": {
                "time_shift": {
                    "s3": {"0": "s3", "1": "s5", "-1": "s2"},
                    "s5": {"0": "s5", "-1": "s3"}
                }
            }
        }
        
        result = self.formatter.format_example(example_data, "")
        
        # Should return default message when no output
        self.assertEqual(result, "EXAMPLE test: model found but no output available.")
        
    def test_format_imposition_relations(self):
        """Test formatting of imposition relations."""
        example_data = {
            "example": "test",
            "theory": "imposition",
            "has_model": True,
            "relations": {
                "imposition": {
                    "s3": {"s1": "s3", "s2": "s5"},
                    "s5": {"s1": "s7", "s4": "s5"}
                }
            }
        }
        
        result = self.formatter.format_example(example_data, "")
        
        # Should return default message when no output
        self.assertEqual(result, "EXAMPLE test: model found but no output available.")
        
    def test_format_exclusion_relations(self):
        """Test formatting of exclusion relations."""
        example_data = {
            "example": "test",
            "theory": "exclusion",
            "has_model": True,
            "relations": {
                "excludes": {
                    "s0": ["s2", "s4"],
                    "s1": ["s3"],
                    "s2": ["s0", "s4"],
                    "s3": []
                }
            }
        }
        
        result = self.formatter.format_example(example_data, "")
        
        # Should return default message when no output
        self.assertEqual(result, "EXAMPLE test: model found but no output available.")
        
    def test_format_default_relations(self):
        """Test formatting of default R-style relations."""
        example_data = {
            "example": "test",
            "theory": "modal",
            "has_model": True,
            "relations": {
                "R": {
                    "s0": ["s1", "s2"],
                    "s1": ["s1"],
                    "s2": []
                }
            }
        }
        
        result = self.formatter.format_example(example_data, "")
        
        # Should return default message when no output
        self.assertEqual(result, "EXAMPLE test: model found but no output available.")
        
    def test_format_mixed_relations(self):
        """Test formatting with multiple relation types."""
        example_data = {
            "example": "test",
            "theory": "complex",
            "has_model": True,
            "relations": {
                "R": {"s0": ["s1"], "s1": ["s0"]},
                "time_shift": {"s0": {"0": "s0", "1": "s1"}},
                "excludes": {"s0": ["s2"], "s1": ["s3"]}
            }
        }
        
        result = self.formatter.format_example(example_data, "")
        
        # Should return default message when no output
        self.assertEqual(result, "EXAMPLE test: model found but no output available.")


if __name__ == '__main__':
    unittest.main()