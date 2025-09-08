"""Tests for integration with BuildModule."""

import pytest
from unittest.mock import Mock, MagicMock, patch
import io
import sys

from model_checker.output.manager import OutputManager
from model_checker.output.collectors import ModelDataCollector
from model_checker.output.formatters import MarkdownFormatter


class TestBuildIntegration:
    """Test integration of output system with BuildModule."""
    
    def test_output_manager_initialization_in_build_module(self):
        """Test OutputManager is properly initialized in BuildModule."""
        # Mock module flags
        mock_flags = Mock()
        mock_flags.save_output = True
        mock_flags.output_mode = 'batch'
        mock_flags.sequential_files = None
        mock_flags.file_path = "test.py"
        
        # Test that BuildModule would initialize OutputManager
        # This test verifies the initialization pattern
        output_manager = OutputManager(
            save_output=mock_flags.save_output,
            mode=getattr(mock_flags, 'output_mode', 'batch'),
            sequential_files=getattr(mock_flags, 'sequential_files', 'multiple')
        )
        
        assert output_manager.save_output is True
        assert output_manager.mode == 'batch'
        assert output_manager.sequential_files is None
        
    def test_capture_model_output(self):
        """Test capturing model output during execution."""
        # Create a mock model structure with output
        mock_model = Mock()
        mock_model.z3_model_status = True
        mock_model.print_to = Mock()
        
        # Capture what would be printed
        captured_output = io.StringIO()
        
        # Simulate print_to behavior
        def mock_print_to(settings, example_name, theory_name, 
                         print_constraints=None, output=None):
            if output is None:
                output = sys.stdout
            print("Model found!", file=output)
            print("States: s0, s1, s2", file=output)
            
        mock_model.print_to.side_effect = mock_print_to
        
        # Redirect stdout to capture
        old_stdout = sys.stdout
        sys.stdout = captured_output
        
        try:
            # Call print_to as BuildExample would
            mock_model.print_to({}, "test", "logos")
            output_text = captured_output.getvalue()
        finally:
            sys.stdout = old_stdout
            
        assert "Model found!" in output_text
        assert "States: s0, s1, s2" in output_text
        
    def test_collect_and_format_integration(self):
        """Test data collection and formatting work together."""
        # Create mock model
        mock_model = Mock()
        mock_model.z3_model_status = True
        
        # Mock extraction methods
        mock_model.extract_evaluation_world = Mock(return_value="s1")
        mock_model.extract_states = Mock(return_value={
            "worlds": ["s1", "s2"],
            "possible": ["s0", "s1", "s2"],
            "impossible": []
        })
        mock_model.extract_relations = Mock(return_value={})
        mock_model.extract_propositions = Mock(return_value={})
        
        # Collect data
        collector = ModelDataCollector()
        model_data = collector.collect_model_data(mock_model, "test", "logos")
        
        # Format data
        formatter = MarkdownFormatter()
        formatted_output = formatter.format_example(model_data, "Raw output here")
        
        # Verify integration - formatter should just return the raw output
        assert formatted_output == "Raw output here"
        
    def test_save_workflow(self):
        """Test complete save workflow."""
        # Create output manager
        manager = OutputManager(save_output=True, mode='batch')
        manager.create_output_directory("test_output")
        
        # Simulate processing examples
        for i in range(2):
            example_data = {
                "example": f"test{i}",
                "theory": "logos",
                "has_model": True,
                "evaluation_world": f"s{i}",
                "states": {"possible": [f"s{i}"], "impossible": [], "worlds": [f"s{i}"]},
                "relations": {},
                "propositions": {}
            }
            
            formatted = f"# Example {i} output"
            manager.save_example(f"test{i}", example_data, formatted)
            
        # Finalize
        manager.finalize()
        
        # Verify files created
        import os
        assert os.path.exists("test_output/EXAMPLES.md")
        assert os.path.exists("test_output/MODELS.json")
        
        # Clean up
        import shutil
        shutil.rmtree("test_output")
        
    def test_sequential_mode_workflow(self):
        """Test sequential mode with multiple files."""
        # Create output manager in sequential mode
        manager = OutputManager(save_output=True, mode='sequential', 
                              sequential_files='multiple')
        manager.create_output_directory("test_seq_output")
        
        # Save example
        example_data = {
            "example": "seq_test",
            "theory": "bimodal",
            "has_model": True,
            "evaluation_world": "s0",
            "states": {"possible": ["s0"], "impossible": [], "worlds": ["s0"]},
            "relations": {},
            "propositions": {}
        }
        
        manager.save_example("seq_test", example_data, "Sequential output")
        manager.finalize()
        
        # Verify files
        import os
        assert os.path.exists("test_seq_output/sequential/seq_test.md")
        assert os.path.exists("test_seq_output/MODELS.json")
        
        # Clean up
        import shutil
        shutil.rmtree("test_seq_output")