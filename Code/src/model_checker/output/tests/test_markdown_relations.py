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
        
        # Check that time shift formatting is correct
        self.assertIn("#### time_shift Relation", result)
        self.assertIn("s3 →_{-1} s2", result)
        self.assertIn("s3 →_{0} s3", result)
        self.assertIn("s3 →_{1} s5", result)
        self.assertIn("s5 →_{-1} s3", result)
        self.assertIn("s5 →_{0} s5", result)
        
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
        
        # Check imposition formatting
        self.assertIn("#### imposition Relation", result)
        self.assertIn("s3 →_{s1} s3", result)
        self.assertIn("s3 →_{s2} s5", result)
        self.assertIn("s5 →_{s1} s7", result)
        self.assertIn("s5 →_{s4} s5", result)
        
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
        
        # Check exclusion formatting
        self.assertIn("#### excludes Relation", result)
        self.assertIn("s0 ⊥ s2, s4", result)
        self.assertIn("s1 ⊥ s3", result)
        self.assertIn("s2 ⊥ s0, s4", result)
        # s3 excludes nothing, so should not appear
        self.assertNotIn("s3 ⊥", result)
        
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
        
        # Check default formatting
        self.assertIn("#### R Relation", result)
        self.assertIn("s0 → s1, s2", result)
        self.assertIn("s1 → s1", result)
        self.assertIn("s2 → ∅", result)
        
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
        
        # Check all relation types appear
        self.assertIn("#### R Relation", result)
        self.assertIn("#### time_shift Relation", result)
        self.assertIn("#### excludes Relation", result)
        
        # Check formatting of each
        self.assertIn("s0 → s1", result)
        self.assertIn("s0 →_{0} s0", result)
        self.assertIn("s0 ⊥ s2", result)


if __name__ == '__main__':
    unittest.main()