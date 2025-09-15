"""Tests for MODELS.json suppression in sequential/interactive modes."""

import unittest
import tempfile
import os
from unittest.mock import Mock, MagicMock, patch
from model_checker.output.manager import OutputManager
from model_checker.output.config import OutputConfig
from model_checker.output.constants import (
    FORMAT_JSON, MODE_BATCH, MODE_SEQUENTIAL
)


class TestModelsJsonSuppression(unittest.TestCase):
    """Test that MODELS.json is only generated in batch mode."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        if os.path.exists(self.temp_dir):
            shutil.rmtree(self.temp_dir)
    
    def test_batch_mode_generates_models_json(self):
        """Test that batch mode generates MODELS.json when JSON format enabled."""
        config = OutputConfig(
            formats=[FORMAT_JSON],
            mode=MODE_BATCH,
            save_output=True
        )
        
        manager = OutputManager(config)
        manager.output_dir = self.temp_dir
        manager.models_data = [{"example": "test", "has_model": False}]
        
        # Call finalize
        manager.finalize()
        
        # Check that MODELS.json was created
        models_path = os.path.join(self.temp_dir, "MODELS.json")
        self.assertTrue(os.path.exists(models_path))
    
    def test_sequential_mode_suppresses_models_json(self):
        """Test that sequential mode does not generate MODELS.json."""
        config = OutputConfig(
            formats=[FORMAT_JSON],
            mode=MODE_SEQUENTIAL,
            save_output=True
        )
        
        manager = OutputManager(config)
        manager.output_dir = self.temp_dir
        manager.models_data = [{"example": "test", "has_model": False}]
        
        # Call finalize
        manager.finalize()
        
        # Check that MODELS.json was NOT created
        models_path = os.path.join(self.temp_dir, "MODELS.json")
        self.assertFalse(os.path.exists(models_path))
    
    def test_interactive_mode_suppresses_models_json(self):
        """Test that interactive mode does not generate MODELS.json."""
        config = OutputConfig(
            formats=[FORMAT_JSON],
            mode=MODE_SEQUENTIAL,
            save_output=True
        )
        
        # Create mock interactive manager
        mock_interactive = Mock()
        mock_interactive.is_interactive.return_value = True
        mock_interactive.get_summary.return_value = {
            "mode": "interactive",
            "saved_models": {}
        }
        
        manager = OutputManager(config, mock_interactive)
        manager.output_dir = self.temp_dir
        manager.models_data = [{"example": "test", "has_model": False}]
        
        # Call finalize
        manager.finalize()
        
        # Check that MODELS.json was NOT created
        models_path = os.path.join(self.temp_dir, "MODELS.json")
        self.assertFalse(os.path.exists(models_path))
    
    def test_batch_mode_without_json_format(self):
        """Test that batch mode without JSON format doesn't generate MODELS.json."""
        config = OutputConfig(
            formats=[],  # No JSON format
            mode=MODE_BATCH,
            save_output=True
        )
        
        manager = OutputManager(config)
        manager.output_dir = self.temp_dir
        manager.models_data = [{"example": "test", "has_model": False}]
        
        # Call finalize
        manager.finalize()
        
        # Check that MODELS.json was NOT created
        models_path = os.path.join(self.temp_dir, "MODELS.json")
        self.assertFalse(os.path.exists(models_path))
    
    def test_sequential_mode_creates_summary_json(self):
        """Test that sequential prompted mode still creates summary.json."""
        config = OutputConfig(
            formats=[FORMAT_JSON],
            mode=MODE_SEQUENTIAL,
            save_output=True
        )
        
        # Create mock sequential manager
        mock_sequential = Mock()
        mock_sequential.is_sequential.return_value = True
        mock_sequential.mode = 'sequential'  # Set the mode attribute
        mock_sequential.get_summary.return_value = {
            "mode": "sequential",
            "saved_models": {"example1": [1, 2]}
        }
        
        manager = OutputManager(config, mock_sequential)
        manager.output_dir = self.temp_dir
        # Add sequential saves data for summary generation
        manager._sequential_saves = {"example1": [1, 2]}
        
        # Call finalize
        manager.finalize()
        
        # Check that summary.json was created but not MODELS.json
        summary_path = os.path.join(self.temp_dir, "summary.json")
        models_path = os.path.join(self.temp_dir, "MODELS.json")
        
        self.assertTrue(os.path.exists(summary_path))
        self.assertFalse(os.path.exists(models_path))


if __name__ == '__main__':
    unittest.main()