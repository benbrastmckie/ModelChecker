"""Tests for OutputManager interactive mode support."""

import os
import json
import tempfile
import shutil
import pytest
from unittest.mock import Mock, MagicMock, patch
from datetime import datetime

from model_checker.output import OutputManager, InteractiveSaveManager, MockInputProvider


class TestOutputManagerInteractive:
    """Test OutputManager with interactive mode features."""
    
    def setup_method(self):
        """Create temporary directory for tests."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
        os.chdir(self.temp_dir)
        
    def teardown_method(self):
        """Clean up temporary directory."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir)
    
    def test_initialization_with_interactive_manager(self):
        """Test OutputManager can be initialized with InteractiveSaveManager."""
        interactive_manager = InteractiveSaveManager(MockInputProvider([]))
        interactive_manager.mode = 'interactive'
        
        output_manager = OutputManager(
            save_output=True,
            interactive_manager=interactive_manager
        )
        
        assert output_manager.save_output is True
        assert output_manager.interactive_manager is interactive_manager
        assert output_manager.mode == 'interactive'
        
    def test_create_example_directory(self):
        """Test creating per-example directories in interactive mode."""
        interactive_manager = InteractiveSaveManager(MockInputProvider([]))
        interactive_manager.mode = 'interactive'
        
        output_manager = OutputManager(
            save_output=True,
            interactive_manager=interactive_manager
        )
        output_manager.create_output_directory()
        
        # Create example directory
        example_dir = output_manager.create_example_directory("TEST_EXAMPLE")
        
        assert os.path.exists(example_dir)
        assert os.path.basename(example_dir) == "TEST_EXAMPLE"
        assert example_dir.startswith(output_manager.output_dir)
        
    def test_save_model_interactive_mode(self):
        """Test saving individual models in interactive mode."""
        interactive_manager = InteractiveSaveManager(MockInputProvider([]))
        interactive_manager.mode = 'interactive'
        
        output_manager = OutputManager(
            save_output=True,
            interactive_manager=interactive_manager
        )
        output_manager.create_output_directory()
        
        # Save first model
        model_data = {
            "example": "TEST_EX",
            "theory": "test_theory",
            "has_model": True,
            "evaluation_world": "s1"
        }
        formatted_output = "# Test Model 1"
        
        output_manager.save_model_interactive(
            "TEST_EX", 
            model_data, 
            formatted_output,
            model_num=1
        )
        
        # Check files created
        example_dir = os.path.join(output_manager.output_dir, "TEST_EX")
        assert os.path.exists(example_dir)
        
        model_md = os.path.join(example_dir, "MODEL_1.md")
        model_json = os.path.join(example_dir, "MODEL_1.json")
        
        assert os.path.exists(model_md)
        assert os.path.exists(model_json)
        
        # Verify content
        with open(model_md, 'r') as f:
            assert f.read() == "# Test Model 1"
            
        with open(model_json, 'r') as f:
            data = json.load(f)
            assert data["example"] == "TEST_EX"
            
    def test_save_multiple_models_same_example(self):
        """Test saving multiple models for same example."""
        interactive_manager = InteractiveSaveManager(MockInputProvider([]))
        interactive_manager.mode = 'interactive'
        
        output_manager = OutputManager(
            save_output=True,
            interactive_manager=interactive_manager
        )
        output_manager.create_output_directory()
        
        # Save three models
        for i in range(1, 4):
            model_data = {"example": "MULTI", "model_num": i}
            output_manager.save_model_interactive(
                "MULTI",
                model_data,
                f"Model {i}",
                model_num=i
            )
            
        # Check all files exist
        example_dir = os.path.join(output_manager.output_dir, "MULTI")
        for i in range(1, 4):
            assert os.path.exists(os.path.join(example_dir, f"MODEL_{i}.md"))
            assert os.path.exists(os.path.join(example_dir, f"MODEL_{i}.json"))
            
    def test_batch_mode_compatibility(self):
        """Test that batch mode still works with interactive manager."""
        interactive_manager = InteractiveSaveManager(MockInputProvider([]))
        interactive_manager.mode = 'batch'
        
        output_manager = OutputManager(
            save_output=True,
            interactive_manager=interactive_manager
        )
        output_manager.create_output_directory()
        
        # Should use normal save_example method
        model_data = {"example": "BATCH_TEST"}
        output_manager.save_example("BATCH_TEST", model_data, "Batch output")
        
        # Finalize to write batch outputs
        output_manager.finalize()
        
        # Check it went to main EXAMPLES.md
        assert os.path.exists(os.path.join(output_manager.output_dir, "EXAMPLES.md"))
        assert not os.path.exists(os.path.join(output_manager.output_dir, "BATCH_TEST"))
        
    def test_finalize_with_summary(self):
        """Test finalize creates summary.json in interactive mode."""
        interactive_manager = InteractiveSaveManager(MockInputProvider([]))
        interactive_manager.mode = 'interactive'
        interactive_manager.model_count = {
            "EX1": 2,
            "EX2": 1,
            "EX3": 3
        }
        
        output_manager = OutputManager(
            save_output=True,
            interactive_manager=interactive_manager
        )
        output_manager.create_output_directory()
        
        # Save some models
        output_manager.save_model_interactive("EX1", {}, "Model", 1)
        output_manager.save_model_interactive("EX1", {}, "Model", 2)
        
        # Finalize
        output_manager.finalize()
        
        # Check summary.json
        summary_path = os.path.join(output_manager.output_dir, "summary.json")
        assert os.path.exists(summary_path)
        
        with open(summary_path, 'r') as f:
            summary = json.load(f)
            
        assert "metadata" in summary
        assert "examples" in summary
        assert summary["examples"]["EX1"]["model_count"] == 2
        assert summary["examples"]["EX1"]["directory"] == "EX1"
        
    def test_get_output_path_interactive(self):
        """Test getting output paths in interactive mode."""
        interactive_manager = InteractiveSaveManager(MockInputProvider([]))
        interactive_manager.mode = 'interactive'
        
        output_manager = OutputManager(
            save_output=True,
            interactive_manager=interactive_manager
        )
        output_manager.create_output_directory()
        
        # Get path for model file
        path = output_manager.get_output_path("TEST_EX", "MODEL_1.md")
        assert path.endswith("TEST_EX/MODEL_1.md")
        
    def test_no_interactive_manager_defaults(self):
        """Test OutputManager works without interactive manager."""
        output_manager = OutputManager(save_output=True)
        
        assert output_manager.interactive_manager is None
        assert output_manager.mode == 'batch'
        
    def test_directory_structure_interactive(self):
        """Test complete directory structure in interactive mode."""
        interactive_manager = InteractiveSaveManager(MockInputProvider([]))
        interactive_manager.mode = 'interactive'
        
        output_manager = OutputManager(
            save_output=True,
            interactive_manager=interactive_manager
        )
        output_manager.create_output_directory()
        
        # Save models for multiple examples
        examples = [
            ("LOGIC_1", 2),
            ("LOGIC_2", 1),
            ("LOGIC_3", 3)
        ]
        
        for example_name, model_count in examples:
            for i in range(1, model_count + 1):
                output_manager.save_model_interactive(
                    example_name,
                    {"model": i},
                    f"Model {i} for {example_name}",
                    model_num=i
                )
                
        # Verify structure
        for example_name, model_count in examples:
            example_dir = os.path.join(output_manager.output_dir, example_name)
            assert os.path.exists(example_dir)
            
            # Check model files
            files = os.listdir(example_dir)
            assert len(files) == model_count * 2  # .md and .json for each
            
    @patch('builtins.print')
    def test_save_location_display(self, mock_print):
        """Test that save location is displayed after saving."""
        interactive_manager = InteractiveSaveManager(MockInputProvider([]))
        interactive_manager.mode = 'interactive'
        
        output_manager = OutputManager(
            save_output=True,
            interactive_manager=interactive_manager
        )
        output_manager.create_output_directory()
        
        # Save a model
        output_manager.save_model_interactive(
            "DISPLAY_TEST",
            {"test": True},
            "Test output",
            model_num=1
        )
        
        # Check that location was printed
        expected_path = os.path.join(
            output_manager.output_dir,
            "DISPLAY_TEST",
            "MODEL_1.md"
        )
        mock_print.assert_any_call(f"Saved to: {expected_path}")