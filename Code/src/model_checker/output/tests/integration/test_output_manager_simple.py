"""Tests for simplified OutputManager."""

import os
import json
import tempfile
import shutil
import pytest
from unittest.mock import Mock, MagicMock
from model_checker.output import OutputManager, OutputConfig, SequentialSaveManager


class TestOutputManager:
    """Test OutputManager with simplified architecture."""
    
    def setup_method(self):
        """Create temporary directory for tests."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
        os.chdir(self.temp_dir)
    
    def teardown_method(self):
        """Clean up temporary directory."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir)
    
    def test_initialization_batch_mode(self):
        """Test OutputManager in batch mode (default)."""
        config = OutputConfig(formats=['markdown', 'json'])
        manager = OutputManager(config)
        
        assert manager.config == config
        assert manager.prompt_manager is None
        assert manager.accumulated_outputs == []
        assert manager.saved_models == {}
    
    def test_initialization_sequential_mode(self):
        """Test OutputManager with sequential manager."""
        config = OutputConfig(sequential=True)
        prompt_manager = Mock(spec=SequentialSaveManager)
        manager = OutputManager(config, prompt_manager)
        
        assert manager.config == config
        assert manager.prompt_manager == prompt_manager
    
    def test_create_output_directory_default(self):
        """Test creating timestamped output directory."""
        config = OutputConfig()
        manager = OutputManager(config)
        
        manager.create_output_directory()
        
        assert manager.output_dir is not None
        assert manager.output_dir.startswith('output_')
        assert os.path.exists(manager.output_dir)
    
    def test_create_output_directory_custom(self):
        """Test creating custom named directory."""
        config = OutputConfig()
        manager = OutputManager(config)
        
        manager.create_output_directory('custom_output')
        
        assert manager.output_dir == 'custom_output'
        assert os.path.exists('custom_output')
    
    def test_save_example_batch_mode(self):
        """Test saving in batch mode (accumulates)."""
        config = OutputConfig(sequential=False)
        manager = OutputManager(config)
        manager.create_output_directory()
        
        example_data = {"test": "data"}
        output = "Test output"
        
        manager.save_example("TEST", example_data, output)
        
        # Should accumulate, not save immediately
        assert len(manager.accumulated_outputs) == 1
        assert manager.accumulated_outputs[0] == ("TEST", example_data, output)
        assert not os.path.exists(os.path.join(manager.output_dir, "TEST.md"))
    
    def test_save_example_sequential_mode(self):
        """Test saving in sequential mode (immediate)."""
        config = OutputConfig(sequential=True, formats=['markdown'])
        manager = OutputManager(config)
        manager.create_output_directory()
        
        example_data = {"test": "data"}
        output = "Test output"
        
        manager.save_example("TEST", example_data, output)
        
        # Should save immediately
        assert manager.saved_models["TEST"] is True
        assert len(manager.accumulated_outputs) == 0
    
    def test_save_prompted_model(self):
        """Test saving individual model with numbering."""
        config = OutputConfig(formats=['markdown', 'json'])
        manager = OutputManager(config)
        manager.create_output_directory()
        
        model_data = {"model": 1}
        output = "Model 1 output"
        
        manager.save_prompted_model("EXAMPLE", model_data, output, 1)
        
        # Check files created
        example_dir = os.path.join(manager.output_dir, "EXAMPLE")
        assert os.path.exists(example_dir)
        assert os.path.exists(os.path.join(example_dir, "MODEL_1.md"))
        assert os.path.exists(os.path.join(example_dir, "MODEL_1.json"))
        
        # Check tracking
        assert "EXAMPLE" in manager.saved_models
        assert 1 in manager.saved_models["EXAMPLE"]
    
    def test_finalize_batch_mode(self):
        """Test finalize saves accumulated outputs."""
        config = OutputConfig(formats=['markdown'])
        manager = OutputManager(config)
        manager.create_output_directory()
        
        # Accumulate some outputs
        manager.save_example("TEST1", {"n": 1}, "Output 1")
        manager.save_example("TEST2", {"n": 2}, "Output 2")
        
        manager.finalize()
        
        # Should have created combined file
        assert os.path.exists(os.path.join(manager.output_dir, "EXAMPLES.md"))
        
        with open(os.path.join(manager.output_dir, "EXAMPLES.md")) as f:
            content = f.read()
            assert "Output 1" in content
            assert "Output 2" in content
            assert "---" in content  # Separator
    
    def test_finalize_sequential_mode(self):
        """Test finalize creates summary in sequential mode."""
        config = OutputConfig(sequential=True)
        manager = OutputManager(config)
        manager.create_output_directory()
        
        # Track some saves
        manager.saved_models = {
            "EX1": [1, 2],
            "EX2": [1]
        }
        
        manager.finalize()
        
        # Should have created summary
        summary_path = os.path.join(manager.output_dir, "summary.json")
        assert os.path.exists(summary_path)
        
        with open(summary_path) as f:
            summary = json.load(f)
            assert summary["metadata"]["mode"] == "sequential"
            assert summary["metadata"]["total_examples"] == 2
            assert summary["metadata"]["total_models"] == 3
    
    def test_should_save(self):
        """Test should_save method."""
        config1 = OutputConfig(save_output=True)
        manager1 = OutputManager(config1)
        assert manager1.should_save() is True
        
        config2 = OutputConfig(save_output=False)
        manager2 = OutputManager(config2)
        assert manager2.should_save() is False