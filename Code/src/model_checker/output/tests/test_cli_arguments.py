"""Tests for CLI argument parsing."""

import pytest
import sys
from unittest.mock import patch

from model_checker.__main__ import ParseFileFlags


class TestCLIArguments:
    """Test CLI argument parsing for output options."""
    
    def test_default_output_mode(self):
        """Test default output mode is batch."""
        parser = ParseFileFlags()
        
        with patch.object(sys, 'argv', ['model-checker', 'test.py']):
            flags, _ = parser.parse()
            
        assert hasattr(flags, 'output_mode')
        assert flags.output_mode == 'batch'
        
    def test_sequential_output_mode(self):
        """Test setting sequential output mode."""
        parser = ParseFileFlags()
        
        with patch.object(sys, 'argv', ['model-checker', 'test.py', '--output-mode', 'sequential']):
            flags, _ = parser.parse()
            
        assert flags.output_mode == 'sequential'
        
    def test_default_sequential_files(self):
        """Test default sequential files is multiple."""
        parser = ParseFileFlags()
        
        with patch.object(sys, 'argv', ['model-checker', 'test.py']):
            flags, _ = parser.parse()
            
        assert hasattr(flags, 'sequential_files')
        assert flags.sequential_files == 'multiple'
        
    def test_single_sequential_files(self):
        """Test setting single sequential files."""
        parser = ParseFileFlags()
        
        with patch.object(sys, 'argv', ['model-checker', 'test.py', '--sequential-files', 'single']):
            flags, _ = parser.parse()
            
        assert flags.sequential_files == 'single'
        
    def test_combined_save_and_mode_flags(self):
        """Test combining -s with output mode flags."""
        parser = ParseFileFlags()
        
        with patch.object(sys, 'argv', [
            'model-checker', 'test.py', '-s', 
            '--output-mode', 'sequential',
            '--sequential-files', 'single'
        ]):
            flags, _ = parser.parse()
            
        assert flags.save_output is True
        assert flags.output_mode == 'sequential'
        assert flags.sequential_files == 'single'
        
    def test_invalid_output_mode_rejected(self):
        """Test invalid output mode is rejected."""
        parser = ParseFileFlags()
        
        with patch.object(sys, 'argv', ['model-checker', 'test.py', '--output-mode', 'invalid']):
            with pytest.raises(SystemExit):  # argparse exits on invalid choice
                parser.parse()
                
    def test_help_includes_new_options(self):
        """Test help text includes new output options."""
        parser = ParseFileFlags()
        help_text = parser.parser.format_help()
        
        assert '--output-mode' in help_text
        assert 'batch' in help_text
        assert 'sequential' in help_text
        assert '--sequential-files' in help_text
        assert 'single' in help_text
        assert 'multiple' in help_text