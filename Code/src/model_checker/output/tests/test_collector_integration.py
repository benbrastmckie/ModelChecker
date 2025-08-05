"""Integration tests for ModelDataCollector with new extraction methods."""

import unittest
from unittest.mock import Mock

from model_checker.output.collectors import ModelDataCollector


class TestCollectorIntegration(unittest.TestCase):
    """Test ModelDataCollector with model structure extraction methods."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.collector = ModelDataCollector()
        
    def test_collect_with_extraction_methods(self):
        """Test collector uses model structure extraction methods."""
        # Create mock model structure with extraction methods
        model_structure = Mock()
        model_structure.z3_model_status = True
        
        # Mock extraction methods
        model_structure.extract_states = Mock(return_value={
            "worlds": ["s3", "s5"], 
            "possible": ["s1", "s7"],
            "impossible": ["s0", "s2", "s4", "s6"]
        })
        
        model_structure.extract_evaluation_world = Mock(return_value="s3")
        
        model_structure.extract_relations = Mock(return_value={
            "time_shift": {
                "s3": {"0": "s3", "1": "s5"},
                "s5": {"0": "s5", "-1": "s3"}
            }
        })
        
        model_structure.extract_propositions = Mock(return_value={
            "p": {"s3": True, "s5": False},
            "q": {"s3": False, "s5": True}
        })
        
        # Collect data
        result = self.collector.collect_model_data(
            model_structure, "test_example", "bimodal"
        )
        
        # Verify extraction methods were called
        model_structure.extract_states.assert_called_once()
        model_structure.extract_evaluation_world.assert_called_once()
        model_structure.extract_relations.assert_called_once()
        model_structure.extract_propositions.assert_called_once()
        
        # Verify collected data
        self.assertEqual(result["example"], "test_example")
        self.assertEqual(result["theory"], "bimodal")
        self.assertTrue(result["has_model"])
        self.assertEqual(result["evaluation_world"], "s3")
        
        # Verify states
        self.assertEqual(result["states"]["worlds"], ["s3", "s5"])
        self.assertEqual(result["states"]["possible"], ["s1", "s7"])
        self.assertEqual(result["states"]["impossible"], ["s0", "s2", "s4", "s6"])
        
        # Verify relations
        self.assertIn("time_shift", result["relations"])
        self.assertEqual(result["relations"]["time_shift"]["s3"]["1"], "s5")
        
        # Verify propositions
        self.assertEqual(result["propositions"]["p"]["s3"], True)
        self.assertEqual(result["propositions"]["q"]["s5"], True)
        
    def test_collect_without_extraction_methods(self):
        """Test collector fallback when extraction methods not available."""
        # Create mock model structure without extraction methods
        model_structure = Mock()
        model_structure.z3_model_status = True
        
        # Ensure methods don't exist
        delattr(model_structure, 'extract_states')
        delattr(model_structure, 'extract_evaluation_world')
        delattr(model_structure, 'extract_relations')
        delattr(model_structure, 'extract_propositions')
        
        # Collect data
        result = self.collector.collect_model_data(
            model_structure, "test_example", "legacy_theory"
        )
        
        # Verify fallback behavior
        self.assertTrue(result["has_model"])
        self.assertIsNone(result["evaluation_world"])
        self.assertEqual(result["states"], {"worlds": [], "possible": [], "impossible": []})
        self.assertEqual(result["relations"], {})
        self.assertEqual(result["propositions"], {})
        
    def test_collect_no_model(self):
        """Test collector when no model found."""
        # Create mock with no model
        model_structure = Mock()
        model_structure.z3_model_status = False
        
        # Collect data
        result = self.collector.collect_model_data(
            model_structure, "test_example", "test_theory"
        )
        
        # Verify no model result
        self.assertFalse(result["has_model"])
        self.assertIsNone(result["evaluation_world"])
        self.assertEqual(result["states"], {"worlds": [], "possible": [], "impossible": []})
        self.assertEqual(result["relations"], {})
        self.assertEqual(result["propositions"], {})


if __name__ == '__main__':
    unittest.main()