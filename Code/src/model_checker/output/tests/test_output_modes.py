"""Tests for batch vs sequential output modes."""

import os
import tempfile
import shutil
import pytest

from model_checker.output.manager import OutputManager


class TestOutputModes:
    """Test different output mode behaviors."""
    
    def setup_method(self):
        """Create temporary directory for tests."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
        os.chdir(self.temp_dir)
        
    def teardown_method(self):
        """Clean up temporary directory."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir)
        
    def test_batch_mode_initialization(self):
        """Test batch mode properly initializes."""
        manager = OutputManager(save_output=True, mode='batch')
        assert manager.mode == 'batch'
        assert not hasattr(manager, 'sequential_files') or manager.sequential_files is None
        
    def test_sequential_mode_initialization(self):
        """Test sequential mode properly initializes."""
        manager = OutputManager(save_output=True, mode='sequential')
        assert manager.mode == 'sequential'
        assert manager.sequential_files == 'multiple'  # default
        
    def test_append_to_batch(self):
        """Test appending examples in batch mode."""
        manager = OutputManager(save_output=True, mode='batch')
        manager.create_output_directory()
        
        # Mock example data
        example_data = {'example': 'test1', 'theory': 'logos'}
        formatted_output = "# Example: test1\\nModel output here..."
        
        manager._append_to_batch('test1', example_data, formatted_output)
        
        # Check internal storage
        assert len(manager._batch_outputs) == 1
        assert manager._batch_outputs[0] == formatted_output
        assert len(manager.models_data) == 1
        assert manager.models_data[0] == example_data
        
    def test_save_sequential_multiple_files(self):
        """Test saving to multiple files in sequential mode."""
        manager = OutputManager(
            save_output=True, 
            mode='sequential',
            sequential_files='multiple'
        )
        manager.create_output_directory()
        
        # Mock example data
        example_data = {'example': 'test1', 'theory': 'logos'}
        formatted_output = "# Example: test1\\nModel output here..."
        
        manager._save_sequential('test1', example_data, formatted_output)
        
        # Check file was created
        expected_file = os.path.join(manager.output_dir, 'sequential', 'test1.md')
        assert os.path.exists(expected_file)
        
        # Check content
        with open(expected_file, 'r') as f:
            content = f.read()
        assert content == formatted_output
        
    def test_save_sequential_single_file(self):
        """Test appending to single file in sequential mode."""
        manager = OutputManager(
            save_output=True,
            mode='sequential', 
            sequential_files='single'
        )
        manager.create_output_directory()
        
        # Save first example
        example1_data = {'example': 'test1', 'theory': 'logos'}
        formatted1 = "# Example: test1\\nFirst model..."
        manager._save_sequential('test1', example1_data, formatted1)
        
        # Save second example
        example2_data = {'example': 'test2', 'theory': 'logos'}
        formatted2 = "# Example: test2\\nSecond model..."
        manager._save_sequential('test2', example2_data, formatted2)
        
        # Check single file exists
        expected_file = os.path.join(manager.output_dir, 'EXAMPLES.md')
        assert os.path.exists(expected_file)
        
        # Check both examples are in file with separator
        with open(expected_file, 'r') as f:
            content = f.read()
        assert 'test1' in content
        assert 'test2' in content
        assert '---' in content  # separator between examples
        
    def test_save_example_delegates_correctly(self):
        """Test save_example delegates to correct method based on mode."""
        # Test batch mode
        batch_manager = OutputManager(save_output=True, mode='batch')
        batch_manager.create_output_directory()
        batch_manager._append_to_batch = lambda n, d, o: setattr(batch_manager, '_batch_called', True)
        
        batch_manager.save_example('test', {}, '')
        assert hasattr(batch_manager, '_batch_called')
        
        # Test sequential mode
        seq_manager = OutputManager(save_output=True, mode='sequential')
        seq_manager.create_output_directory()
        seq_manager._save_sequential = lambda n, d, o: setattr(seq_manager, '_seq_called', True)
        
        seq_manager.save_example('test', {}, '')
        assert hasattr(seq_manager, '_seq_called')