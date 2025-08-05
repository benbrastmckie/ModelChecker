"""Integration test for output system with data extraction.

Tests the complete output pipeline including:
- Data extraction from model structures
- JSON collection
- Markdown formatting
"""

import unittest
from unittest.mock import Mock

from model_checker.output.collectors import ModelDataCollector
from model_checker.output.formatters import MarkdownFormatter


class TestOutputIntegration(unittest.TestCase):
    """Test complete output system integration."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.collector = ModelDataCollector()
        self.formatter = MarkdownFormatter(use_colors=False)
        
    def test_bimodal_output_pipeline(self):
        """Test output pipeline with bimodal model structure."""
        # Create mock bimodal model structure
        model = self._create_bimodal_mock()
        
        # Collect data
        data = self.collector.collect_model_data(model, "test_bimodal", "bimodal")
        
        # Verify collection
        self.assertTrue(data["has_model"])
        self.assertEqual(data["evaluation_world"], "s3")
        self.assertEqual(data["states"]["worlds"], ["s3", "s5"])
        self.assertIn("time_shift", data["relations"])
        
        # Format as markdown
        output = "Model checking output here..."
        markdown = self.formatter.format_example(data, output)
        
        # Verify markdown formatting
        self.assertIn("## Example: test_bimodal", markdown)
        self.assertIn("Theory: bimodal", markdown)
        self.assertIn("### States", markdown)
        self.assertIn("s3 [EVALUATION]", markdown)  # s3 is the evaluation world
        self.assertIn("s5 [WORLD]", markdown)
        self.assertIn("### Relations", markdown)
        self.assertIn("time_shift", markdown)
        self.assertIn("s3 →_{0} s3", markdown)
        
    def test_logos_output_pipeline(self):
        """Test output pipeline with logos model structure."""
        # Create mock logos model
        model = self._create_logos_mock()
        
        # Collect data
        data = self.collector.collect_model_data(model, "test_logos", "logos")
        
        # Verify collection
        self.assertTrue(data["has_model"])
        self.assertEqual(data["states"]["worlds"], ["s7"])
        self.assertEqual(data["states"]["possible"], ["s3", "s5", "s6"])
        self.assertEqual(data["states"]["impossible"], ["s0", "s1", "s2", "s4"])
        
        # Format as markdown
        markdown = self.formatter.format_example(data, "")
        
        # Verify state categorization in markdown
        self.assertIn("s7 [EVALUATION]", markdown)  # s7 is the evaluation world
        self.assertIn("s3 [POSSIBLE]", markdown)
        self.assertIn("s0 [IMPOSSIBLE]", markdown)
        
    def test_imposition_output_pipeline(self):
        """Test output pipeline with imposition model structure."""
        # Create mock imposition model
        model = self._create_imposition_mock()
        
        # Collect data
        data = self.collector.collect_model_data(model, "test_imposition", "imposition")
        
        # Verify collection
        self.assertTrue(data["has_model"])
        self.assertIn("imposition", data["relations"])
        
        # Verify imposition relations
        impositions = data["relations"]["imposition"]
        self.assertEqual(impositions["s3"]["s1"], "s3")
        self.assertEqual(impositions["s3"]["s2"], "s5")
        
        # Format as markdown
        markdown = self.formatter.format_example(data, "")
        
        # Verify imposition formatting
        self.assertIn("#### imposition Relation", markdown)
        self.assertIn("s3 →_{s1} s3", markdown)
        self.assertIn("s3 →_{s2} s5", markdown)
        
    def test_exclusion_output_pipeline(self):
        """Test output pipeline with exclusion model structure."""
        # Create mock exclusion model
        model = self._create_exclusion_mock()
        
        # Collect data
        data = self.collector.collect_model_data(model, "test_exclusion", "exclusion")
        
        # Verify collection
        self.assertTrue(data["has_model"])
        self.assertIn("excludes", data["relations"])
        
        # Verify exclusion relations
        excludes = data["relations"]["excludes"]
        self.assertEqual(excludes["s0"], ["s2", "s4"])
        self.assertEqual(excludes["s1"], ["s3"])
        
        # Format as markdown
        markdown = self.formatter.format_example(data, "")
        
        # Verify exclusion formatting
        self.assertIn("#### excludes Relation", markdown)
        self.assertIn("s0 ⊥ s2, s4", markdown)
        self.assertIn("s1 ⊥ s3", markdown)
        
    def _create_bimodal_mock(self):
        """Create mock bimodal model structure."""
        model = Mock()
        model.z3_model_status = True
        
        model.extract_states = Mock(return_value={
            "worlds": ["s3", "s5"],
            "possible": [],
            "impossible": []
        })
        
        model.extract_evaluation_world = Mock(return_value="s3")
        
        model.extract_relations = Mock(return_value={
            "time_shift": {
                "s3": {"0": "s3", "1": "s5"},
                "s5": {"0": "s5", "-1": "s3"}
            }
        })
        
        model.extract_propositions = Mock(return_value={
            "p": {"s3": True, "s5": False}
        })
        
        return model
        
    def _create_logos_mock(self):
        """Create mock logos model structure."""
        model = Mock()
        model.z3_model_status = True
        
        model.extract_states = Mock(return_value={
            "worlds": ["s7"],
            "possible": ["s3", "s5", "s6"],
            "impossible": ["s0", "s1", "s2", "s4"]
        })
        
        model.extract_evaluation_world = Mock(return_value="s7")
        model.extract_relations = Mock(return_value={})
        model.extract_propositions = Mock(return_value={
            "p": {"s7": True}
        })
        
        return model
        
    def _create_imposition_mock(self):
        """Create mock imposition model structure."""
        model = Mock()
        model.z3_model_status = True
        
        model.extract_states = Mock(return_value={
            "worlds": ["s3", "s5"],
            "possible": ["s1", "s7"],
            "impossible": ["s0", "s2", "s4", "s6"]
        })
        
        model.extract_evaluation_world = Mock(return_value="s3")
        
        model.extract_relations = Mock(return_value={
            "imposition": {
                "s3": {"s1": "s3", "s2": "s5"},
                "s5": {"s1": "s7", "s4": "s5"}
            }
        })
        
        model.extract_propositions = Mock(return_value={})
        
        return model
        
    def _create_exclusion_mock(self):
        """Create mock exclusion model structure."""
        model = Mock()
        model.z3_model_status = True
        
        model.extract_states = Mock(return_value={
            "worlds": ["s3"],
            "possible": ["s1", "s7"],
            "impossible": ["s0", "s2", "s4", "s5", "s6"]
        })
        
        model.extract_evaluation_world = Mock(return_value="s3")
        
        model.extract_relations = Mock(return_value={
            "excludes": {
                "s0": ["s2", "s4"],
                "s1": ["s3"],
                "s2": ["s0", "s4"],
                "s3": []
            }
        })
        
        model.extract_propositions = Mock(return_value={})
        
        return model


if __name__ == '__main__':
    unittest.main()