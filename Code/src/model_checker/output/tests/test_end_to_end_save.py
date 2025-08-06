"""End-to-end tests for complete save workflow."""

import os
import json
import tempfile
import shutil
import pytest
from unittest.mock import Mock, MagicMock, patch

from model_checker.output import OutputManager, ModelDataCollector, MarkdownFormatter


class TestEndToEndSave:
    """Test complete save workflow from start to finish."""
    
    def setup_method(self):
        """Create temporary directory for tests."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
        os.chdir(self.temp_dir)
        
    def teardown_method(self):
        """Clean up temporary directory."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir)
        
    def test_complete_batch_workflow(self):
        """Test complete batch mode workflow with multiple examples."""
        # Initialize components
        output_manager = OutputManager(save_output=True, mode='batch')
        output_manager.create_output_directory()
        
        collector = ModelDataCollector()
        formatter = MarkdownFormatter(use_colors=True)
        
        # Process multiple examples
        examples = [
            ("example1", "logos", True),
            ("example2", "bimodal", False),
            ("example3", "exclusion", True)
        ]
        
        for example_name, theory_name, has_model in examples:
            # Create mock model
            mock_model = Mock()
            mock_model.z3_model_status = has_model
            
            if has_model:
                # Mock extraction methods
                mock_model.extract_evaluation_world = Mock(return_value="s1")
                mock_model.extract_states = Mock(return_value={
                    "worlds": ["s1", "s2"],
                    "possible": ["s0", "s1", "s2"],
                    "impossible": []
                })
                mock_model.extract_relations = Mock(return_value={})
                mock_model.extract_propositions = Mock(return_value={
                    'p': {'s0': True, 's1': False, 's2': True}
                })
            else:
                mock_model.z3_model = None
                
            # Collect data
            model_data = collector.collect_model_data(
                mock_model, example_name, theory_name
            )
            
            # Format output
            raw_output = f"Raw output for {example_name}"
            formatted_output = formatter.format_example(model_data, raw_output)
            
            # Save
            output_manager.save_example(example_name, model_data, formatted_output)
            
        # Finalize
        output_manager.finalize()
        
        # Verify EXAMPLES.md
        examples_path = os.path.join(output_manager.output_dir, 'EXAMPLES.md')
        assert os.path.exists(examples_path)
        
        with open(examples_path, 'r') as f:
            content = f.read()
            
        # Check all examples present (simplified formatter just returns raw output)
        assert "Raw output for example1" in content
        assert "Raw output for example2" in content
        assert "Raw output for example3" in content
        
        # Verify MODELS.json
        json_path = os.path.join(output_manager.output_dir, 'MODELS.json')
        assert os.path.exists(json_path)
        
        with open(json_path, 'r') as f:
            data = json.load(f)
            
        assert "metadata" in data
        assert "models" in data
        assert len(data["models"]) == 3
        assert data["models"][0]["has_model"] is True
        assert data["models"][1]["has_model"] is False
        
    def test_sequential_multiple_files_workflow(self):
        """Test sequential mode with multiple files."""
        # Initialize
        output_manager = OutputManager(
            save_output=True,
            mode='sequential',
            sequential_files='multiple'
        )
        output_manager.create_output_directory()
        
        # Process examples
        for i in range(3):
            model_data = {
                "example": f"seq_example_{i}",
                "theory": "logos",
                "has_model": True,
                "evaluation_world": f"s{i}",
                "states": {
                    "possible": [f"s{i}"],
                    "impossible": [],
                    "worlds": [f"s{i}"]
                },
                "relations": {},
                "propositions": {}
            }
            
            formatted = f"# Sequential Example {i}"
            output_manager.save_example(f"seq_example_{i}", model_data, formatted)
            
        output_manager.finalize()
        
        # Verify individual files
        seq_dir = os.path.join(output_manager.output_dir, 'sequential')
        assert os.path.exists(seq_dir)
        
        for i in range(3):
            file_path = os.path.join(seq_dir, f'seq_example_{i}.md')
            assert os.path.exists(file_path)
            
            with open(file_path, 'r') as f:
                content = f.read()
            assert f"Sequential Example {i}" in content
            
    def test_sequential_single_file_workflow(self):
        """Test sequential mode with single file."""
        # Initialize
        output_manager = OutputManager(
            save_output=True,
            mode='sequential',
            sequential_files='single'
        )
        output_manager.create_output_directory()
        
        # Process examples
        for i in range(3):
            model_data = {
                "example": f"single_ex_{i}",
                "theory": "bimodal",
                "has_model": True,
                "evaluation_world": f"s{i}",
                "states": {"possible": [f"s{i}"], "impossible": [], "worlds": [f"s{i}"]},
                "relations": {},
                "propositions": {}
            }
            
            formatted = f"# Single File Example {i}"
            output_manager.save_example(f"single_ex_{i}", model_data, formatted)
            
        output_manager.finalize()
        
        # Verify single EXAMPLES.md
        examples_path = os.path.join(output_manager.output_dir, 'EXAMPLES.md')
        assert os.path.exists(examples_path)
        
        with open(examples_path, 'r') as f:
            content = f.read()
            
        # Check all examples with separators
        assert "Single File Example 0" in content
        assert "Single File Example 1" in content
        assert "Single File Example 2" in content
        assert content.count("---") >= 2  # Separators between examples
        
    def test_ansi_color_conversion_in_output(self):
        """Test ANSI colors are converted in saved output."""
        from model_checker.output.formatters import ANSIToMarkdown
        
        output_manager = OutputManager(save_output=True, mode='batch')
        output_manager.create_output_directory()
        
        # Simulate colored output
        ansi_output = "Model: \033[32ms0\033[0m (possible), \033[31ms1\033[0m (impossible)"
        
        # Convert ANSI to markdown
        converter = ANSIToMarkdown()
        converted = converter.convert(ansi_output)
        
        # Create example data
        model_data = {
            "example": "color_test",
            "theory": "logos",
            "has_model": True,
            "evaluation_world": "s0",
            "states": {"possible": ["s0"], "impossible": ["s1"], "worlds": ["s0"]},
            "relations": {},
            "propositions": {}
        }
        
        # Format with converted output
        formatter = MarkdownFormatter()
        formatted = formatter.format_example(model_data, converted)
        
        output_manager.save_example("color_test", model_data, formatted)
        output_manager.finalize()
        
        # Verify conversion
        examples_path = os.path.join(output_manager.output_dir, 'EXAMPLES.md')
        with open(examples_path, 'r') as f:
            content = f.read()
            
        assert "_s0_" in content  # Green converted to italic
        assert "**s1**" in content  # Red converted to bold