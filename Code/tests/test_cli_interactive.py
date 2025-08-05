"""Tests for CLI interactive flag integration."""

import sys
import pytest
from unittest.mock import Mock, patch
from io import StringIO

from model_checker.__main__ import ParseFileFlags, main


class TestCLIInteractiveFlag:
    """Test CLI handling of interactive flag."""
    
    def test_interactive_flag_parsing(self):
        """Test that -I and --interactive flags are parsed correctly."""
        # Test short flag
        parser = ParseFileFlags()
        with patch.object(sys, 'argv', ['model-checker', '-s', '-I', 'test.py']):
            flags, _ = parser.parse()
            assert flags.save_output is True
            assert flags.interactive is True
            
        # Test long flag
        parser = ParseFileFlags()
        with patch.object(sys, 'argv', ['model-checker', '-s', '--interactive', 'test.py']):
            flags, _ = parser.parse()
            assert flags.save_output is True
            assert flags.interactive is True
            
    def test_interactive_flag_in_short_to_long_map(self):
        """Test that I is mapped to interactive."""
        parser = ParseFileFlags()
        # Don't call parse() as it triggers argument parsing
        # Just check the _short_to_long is created in parse()
        with patch.object(sys, 'argv', ['model-checker', 'test.py']):
            parser.parse()
            assert parser._short_to_long['I'] == 'interactive'
        
    def test_interactive_without_save_output(self):
        """Test interactive flag works even without -s."""
        parser = ParseFileFlags()
        with patch.object(sys, 'argv', ['model-checker', '--interactive', 'test.py']):
            flags, _ = parser.parse()
            assert flags.interactive is True
            assert flags.save_output is False
            
    @patch('model_checker.__main__.BuildModule')
    def test_interactive_flag_passed_to_build_module(self, mock_build_module):
        """Test that interactive flag is passed to BuildModule."""
        # Create a test file
        test_file = 'test_example.py'
        with open(test_file, 'w') as f:
            f.write("# Test example file\n")
            
        try:
            with patch.object(sys, 'argv', ['model-checker', '-s', '-I', test_file]):
                main()
                
            # Check that BuildModule was called with flags containing interactive=True
            assert mock_build_module.called
            call_args = mock_build_module.call_args[0][0]
            assert hasattr(call_args, 'interactive')
            assert call_args.interactive is True
            assert call_args.save_output is True
        finally:
            import os
            if os.path.exists(test_file):
                os.remove(test_file)
                
    def test_help_shows_interactive_flag(self):
        """Test that help text includes interactive flag."""
        parser = ParseFileFlags()
        help_text = parser.parser.format_help()
        assert '--interactive' in help_text
        assert '-I' in help_text
        assert 'interactive save mode' in help_text
        
    def test_interactive_mode_combinations(self):
        """Test various flag combinations with interactive."""
        parser = ParseFileFlags()
        
        # Interactive with batch mode (should be ignored in favor of interactive)
        with patch.object(sys, 'argv', ['model-checker', '-s', '-I', '--output-mode', 'batch', 'test.py']):
            flags, _ = parser.parse()
            assert flags.save_output is True
            assert flags.interactive is True
            assert flags.output_mode == 'batch'
            
        # Interactive with sequential mode
        with patch.object(sys, 'argv', ['model-checker', '-s', '-I', '--output-mode', 'sequential', 'test.py']):
            flags, _ = parser.parse()
            assert flags.save_output is True
            assert flags.interactive is True
            assert flags.output_mode == 'sequential'
            
    def test_argument_order_independence(self):
        """Test that argument order doesn't matter."""
        parser = ParseFileFlags()
        
        # Interactive flag before save output
        with patch.object(sys, 'argv', ['model-checker', '-I', '-s', 'test.py']):
            flags, _ = parser.parse()
            assert flags.save_output is True
            assert flags.interactive is True
            
        # Interactive flag after save output
        with patch.object(sys, 'argv', ['model-checker', '-s', '-I', 'test.py']):
            flags, _ = parser.parse()
            assert flags.save_output is True
            assert flags.interactive is True
            
        # Mixed with other flags
        with patch.object(sys, 'argv', ['model-checker', '-p', '-I', '-s', '-i', 'test.py']):
            flags, _ = parser.parse()
            assert flags.save_output is True
            assert flags.interactive is True
            assert flags.print_constraints is True
            assert flags.print_impossible is True