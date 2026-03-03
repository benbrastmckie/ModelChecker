"""Simple test to verify batch output with data extraction works."""

import unittest
from unittest.mock import Mock, patch
import json

from model_checker.output.manager import OutputManager
from model_checker.output.config import OutputConfig
from model_checker.output.collectors import ModelDataCollector
from model_checker.output.formatters import MarkdownFormatter, JSONFormatter


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
        
        # Create output manager with OutputConfig
        config = OutputConfig(formats=['markdown', 'json'], save_output=True)
        output_manager = OutputManager(config)
        
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
        
        # Test JSON formatting using JSONFormatter directly
        json_formatter = JSONFormatter()
        json_content = json_formatter.format_example(model_data, "Model output")

        # Should be valid JSON
        parsed = json.loads(json_content)
        self.assertEqual(parsed["example"], "test_example")
        self.assertEqual(parsed["theory"], "bimodal")
        
        # Test markdown formatting
        formatter = MarkdownFormatter(use_colors=False)

        # When model_output is provided, formatter returns it as-is
        markdown = formatter.format_example(model_data, "Model output")
        self.assertEqual(markdown, "Model output")

        # When no model_output, formatter creates summary from data
        markdown_no_output = formatter.format_example(model_data, "")
        self.assertIn("test_example", markdown_no_output)
        self.assertIn("model found", markdown_no_output)

        # Test state type formatting
        state_formatted = formatter.format_state_type("s3", "world")
        self.assertIn("s3", state_formatted)
        self.assertIn("WORLD", state_formatted)


if __name__ == '__main__':
    unittest.main()