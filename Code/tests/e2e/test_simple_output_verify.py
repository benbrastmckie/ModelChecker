"""Simple test to verify batch output with data extraction works."""

import unittest
from unittest.mock import Mock, patch
import json

from model_checker.output.manager import OutputManager
from model_checker.output.collectors import ModelDataCollector
from model_checker.output.formatters import MarkdownFormatter


class TestSimpleOutputVerify(unittest.TestCase):
    """Simple test to verify output system with extraction methods."""
    
    def test_output_manager_with_extraction(self):
        """Test OutputManager uses extraction methods correctly."""
        # Create mock model structure with extraction methods
        model_structure = Mock()
        model_structure.z3_model_status = True
        
        # Mock extraction methods
        model_structure.extract_states = Mock(return_value={
            "worlds": ["s3", "s5"], 
            "possible": ["s1"],
            "impossible": ["s0", "s2", "s4", "s6", "s7"]
        })
        
        model_structure.extract_evaluation_world = Mock(return_value="s3")
        
        model_structure.extract_relations = Mock(return_value={
            "time_shift": {
                "s3": {"0": "s3", "1": "s5"},
                "s5": {"0": "s5", "-1": "s3"}
            }
        })
        
        model_structure.extract_propositions = Mock(return_value={
            "p": {"s3": True, "s5": False}
        })
        
        # Create output manager
        output_manager = OutputManager(save_output=True)
        
        # Mock stdout capture
        output_manager.captured_outputs = {
            "test_example": "Model output for test_example"
        }
        
        # Collect data for example
        output_manager.data_collector = ModelDataCollector()
        model_data = output_manager.data_collector.collect_model_data(
            model_structure, "test_example", "bimodal"
        )
        
        # Verify data was collected properly
        self.assertTrue(model_data["has_model"])
        self.assertEqual(model_data["evaluation_world"], "s3")
        self.assertEqual(model_data["states"]["worlds"], ["s3", "s5"])
        self.assertIn("time_shift", model_data["relations"])
        self.assertEqual(model_data["propositions"]["p"]["s3"], True)
        
        # Test JSON formatting
        json_content = output_manager._format_json({
            "examples": [model_data]
        })
        
        # Should be valid JSON
        parsed = json.loads(json_content)
        self.assertEqual(len(parsed["examples"]), 1)
        self.assertEqual(parsed["examples"][0]["theory"], "bimodal")
        
        # Test markdown formatting
        formatter = MarkdownFormatter(use_colors=False)
        markdown = formatter.format_example(model_data, "Model output")
        
        # Check markdown contains key elements
        self.assertIn("## Example: test_example", markdown)
        self.assertIn("Theory: bimodal", markdown)
        self.assertIn("### States", markdown)
        self.assertIn("s3 [WORLD]", markdown)
        self.assertIn("### Relations", markdown)
        self.assertIn("time_shift", markdown)
        self.assertIn("s3 →_{0} s3", markdown)


if __name__ == '__main__':
    unittest.main()