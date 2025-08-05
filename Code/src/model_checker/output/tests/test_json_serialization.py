"""Tests for JSON serialization of model data."""

import json
import os
import tempfile
import shutil
from datetime import datetime
import pytest

from model_checker.output.manager import OutputManager


class TestJSONSerialization:
    """Test JSON output format and structure."""
    
    def setup_method(self):
        """Create temporary directory for tests."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
        os.chdir(self.temp_dir)
        
    def teardown_method(self):
        """Clean up temporary directory."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir)
        
    def test_save_models_json_structure(self):
        """Test MODELS.json has correct structure."""
        manager = OutputManager(save_output=True)
        manager.create_output_directory()
        
        # Add test model data
        model1 = {
            "example": "test1",
            "theory": "logos",
            "has_model": True,
            "evaluation_world": "s1",
            "states": {
                "possible": ["s0", "s1", "s2"],
                "impossible": ["s3"],
                "worlds": ["s1", "s2"]
            },
            "relations": {"R": {"s1": ["s1", "s2"], "s2": ["s1"]}},
            "propositions": {"p": {"s1": True, "s2": False}}
        }
        
        model2 = {
            "example": "test2",
            "theory": "bimodal",
            "has_model": False,
            "evaluation_world": None,
            "states": {"possible": [], "impossible": [], "worlds": []},
            "relations": {},
            "propositions": {}
        }
        
        manager.models_data = [model1, model2]
        
        # Save JSON
        manager._save_models_json()
        
        # Check file exists
        json_path = os.path.join(manager.output_dir, 'MODELS.json')
        assert os.path.exists(json_path)
        
        # Load and verify structure
        with open(json_path, 'r') as f:
            data = json.load(f)
            
        assert "metadata" in data
        assert "models" in data
        assert len(data["models"]) == 2
        
        # Check metadata
        metadata = data["metadata"]
        assert "timestamp" in metadata
        assert "version" in metadata
        assert metadata["version"] == "1.0"
        
        # Check first model
        assert data["models"][0] == model1
        assert data["models"][1] == model2
        
    def test_json_formatting(self):
        """Test JSON is properly formatted with indentation."""
        manager = OutputManager(save_output=True)
        manager.create_output_directory()
        
        manager.models_data = [{
            "example": "test",
            "theory": "logos",
            "has_model": True,
            "evaluation_world": "s0",
            "states": {"possible": ["s0"], "impossible": [], "worlds": ["s0"]},
            "relations": {},
            "propositions": {}
        }]
        
        manager._save_models_json()
        
        json_path = os.path.join(manager.output_dir, 'MODELS.json')
        with open(json_path, 'r') as f:
            content = f.read()
            
        # Check for proper formatting
        assert '    "metadata"' in content  # 4-space indentation
        assert '"models": [\n        {' in content  # Proper array formatting
        
    def test_empty_models_json(self):
        """Test JSON structure when no models collected."""
        manager = OutputManager(save_output=True)
        manager.create_output_directory()
        
        # No models added
        manager._save_models_json()
        
        json_path = os.path.join(manager.output_dir, 'MODELS.json')
        with open(json_path, 'r') as f:
            data = json.load(f)
            
        assert data["models"] == []
        assert "metadata" in data
        
    def test_json_encoding(self):
        """Test JSON handles UTF-8 encoding properly."""
        manager = OutputManager(save_output=True)
        manager.create_output_directory()
        
        # Model with Unicode characters
        manager.models_data = [{
            "example": "test_unicode",
            "theory": "logos",
            "has_model": True,
            "evaluation_world": "s0",
            "states": {"possible": ["s0"], "impossible": [], "worlds": ["s0"]},
            "relations": {},
            "propositions": {"φ": {"s0": True}}  # Greek phi
        }]
        
        manager._save_models_json()
        
        json_path = os.path.join(manager.output_dir, 'MODELS.json')
        with open(json_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
            
        # Verify Unicode preserved
        assert "φ" in data["models"][0]["propositions"]