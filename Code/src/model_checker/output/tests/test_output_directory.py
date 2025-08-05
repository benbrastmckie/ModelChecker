"""Tests for output directory creation and management."""

import os
import tempfile
import shutil
from datetime import datetime
import pytest

from model_checker.output.manager import OutputManager


class TestOutputDirectory:
    """Test output directory creation and structure."""
    
    def setup_method(self):
        """Create temporary directory for tests."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
        os.chdir(self.temp_dir)
        
    def teardown_method(self):
        """Clean up temporary directory."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir)
        
    def test_output_manager_initialization(self):
        """Test OutputManager initializes with correct settings."""
        manager = OutputManager(save_output=True, mode='batch')
        assert manager.save_output is True
        assert manager.mode == 'batch'
        assert manager.output_dir is None
        assert manager.models_data == []
        
    def test_output_manager_disabled(self):
        """Test OutputManager when save_output is False."""
        manager = OutputManager(save_output=False)
        assert manager.should_save() is False
        
    def test_output_manager_enabled(self):
        """Test OutputManager when save_output is True."""
        manager = OutputManager(save_output=True)
        assert manager.should_save() is True
        
    def test_create_output_directory(self):
        """Test output directory creation with timestamp."""
        manager = OutputManager(save_output=True)
        manager.create_output_directory()
        
        assert manager.output_dir is not None
        assert os.path.exists(manager.output_dir)
        assert os.path.isdir(manager.output_dir)
        
        # Check directory name format
        dir_name = os.path.basename(manager.output_dir)
        assert dir_name.startswith('output_')
        # Should have timestamp format: output_YYYYMMDD_HHMMSS
        assert len(dir_name) == 22  # output_ (7) + date (8) + _ (1) + time (6)
        
    def test_sequential_subdirectory_creation(self):
        """Test sequential subdirectory is created in sequential mode."""
        manager = OutputManager(save_output=True, mode='sequential')
        manager.create_output_directory()
        
        sequential_dir = os.path.join(manager.output_dir, 'sequential')
        assert os.path.exists(sequential_dir)
        assert os.path.isdir(sequential_dir)
        
    def test_batch_mode_no_subdirectory(self):
        """Test no sequential subdirectory in batch mode."""
        manager = OutputManager(save_output=True, mode='batch')
        manager.create_output_directory()
        
        sequential_dir = os.path.join(manager.output_dir, 'sequential')
        assert not os.path.exists(sequential_dir)
        
    def test_custom_output_directory_name(self):
        """Test custom output directory name."""
        manager = OutputManager(save_output=True)
        custom_name = "my_custom_output"
        manager.create_output_directory(custom_name)
        
        assert manager.output_dir is not None
        assert os.path.basename(manager.output_dir) == custom_name
        assert os.path.exists(manager.output_dir)
        
    def test_output_modes(self):
        """Test different output mode settings."""
        # Test batch mode
        batch_manager = OutputManager(save_output=True, mode='batch')
        assert batch_manager.mode == 'batch'
        
        # Test sequential mode
        seq_manager = OutputManager(save_output=True, mode='sequential')
        assert seq_manager.mode == 'sequential'
        
        # Test invalid mode defaults to batch
        default_manager = OutputManager(save_output=True, mode='invalid')
        assert default_manager.mode == 'batch'
        
    def test_sequential_file_options(self):
        """Test sequential file options."""
        # Test single file option
        single_manager = OutputManager(
            save_output=True, 
            mode='sequential',
            sequential_files='single'
        )
        assert single_manager.sequential_files == 'single'
        
        # Test multiple files option
        multi_manager = OutputManager(
            save_output=True,
            mode='sequential', 
            sequential_files='multiple'
        )
        assert multi_manager.sequential_files == 'multiple'
        
        # Test default is multiple
        default_manager = OutputManager(save_output=True, mode='sequential')
        assert default_manager.sequential_files == 'multiple'