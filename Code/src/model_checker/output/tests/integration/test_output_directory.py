"""Tests for output directory creation and management."""

import os
import tempfile
import shutil
from datetime import datetime
import pytest

from model_checker.output.manager import OutputManager
from model_checker.output.config import OutputConfig


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
        config = OutputConfig(save_output=True, sequential=False)
        manager = OutputManager(config=config)
        assert manager.config.save_output is True
        assert manager.config.sequential is False
        assert manager.output_dir is None
        assert manager.accumulated_outputs == []
        
    def test_output_manager_disabled(self):
        """Test OutputManager when save_output is False."""
        config = OutputConfig(save_output=False)
        manager = OutputManager(config=config)
        assert manager.should_save() is False
        
    def test_output_manager_enabled(self):
        """Test OutputManager when save_output is True."""
        config = OutputConfig(save_output=True)
        manager = OutputManager(config=config)
        assert manager.should_save() is True
        
    def test_create_output_directory(self):
        """Test output directory creation with timestamp."""
        config = OutputConfig(save_output=True)
        manager = OutputManager(config=config)
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
        """Test output directory is created in sequential mode."""
        config = OutputConfig(save_output=True, sequential=True)
        manager = OutputManager(config=config)
        manager.create_output_directory()
        
        # In sequential mode, the main output directory is created
        # Subdirectories are created per example when saving
        assert os.path.exists(manager.output_dir)
        assert os.path.isdir(manager.output_dir)
        
    def test_batch_mode_no_subdirectory(self):
        """Test no sequential subdirectory in batch mode."""
        config = OutputConfig(save_output=True, sequential=False)
        manager = OutputManager(config=config)
        manager.create_output_directory()
        
        sequential_dir = os.path.join(manager.output_dir, 'sequential')
        assert not os.path.exists(sequential_dir)
        
    def test_custom_output_directory_name(self):
        """Test custom output directory name."""
        config = OutputConfig(save_output=True)
        manager = OutputManager(config=config)
        custom_name = "my_custom_output"
        manager.create_output_directory(custom_name)
        
        assert manager.output_dir is not None
        assert os.path.basename(manager.output_dir) == custom_name
        assert os.path.exists(manager.output_dir)
        
    def test_output_modes(self):
        """Test different output mode settings."""
        # Test batch mode
        config_batch = OutputConfig(save_output=True, sequential=False)
        batch_manager = OutputManager(config=config_batch)
        assert batch_manager.config.sequential is False
        
        # Test sequential mode
        config_seq = OutputConfig(save_output=True, sequential=True)
        seq_manager = OutputManager(config=config_seq)
        assert seq_manager.config.sequential is True
        
        # Test default is batch mode
        config_default = OutputConfig(save_output=True)
        default_manager = OutputManager(config=config_default)
        assert default_manager.config.sequential is False
        
    def test_sequential_file_options(self):
        """Test sequential mode configuration."""
        # Test sequential mode enabled
        config_seq = OutputConfig(
            save_output=True, 
            sequential=True
        )
        seq_manager = OutputManager(config=config_seq)
        assert seq_manager.config.sequential is True
        
        # Test batch mode (sequential=False)
        config_batch = OutputConfig(
            save_output=True,
            sequential=False
        )
        batch_manager = OutputManager(config=config_batch)
        assert batch_manager.config.sequential is False
        
        # Test default is batch mode
        config_def = OutputConfig(save_output=True)
        default_manager = OutputManager(config=config_def)
        assert default_manager.config.sequential is False