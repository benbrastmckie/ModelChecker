"""Tests for CLI interactive flag integration.

Tests the command-line interface handling of interactive mode,
including flag parsing, argument combinations, and integration
with the build module.
"""

import sys
import os
import pytest
from unittest.mock import Mock, patch
from io import StringIO
from pathlib import Path

from model_checker.__main__ import ParseFileFlags, main
from tests.utils.helpers import create_test_module


class TestCLIInteractiveFlag:
    """Test CLI handling of interactive flag."""
    
    @pytest.mark.parametrize("flag_variant,expected_interactive", [
        (['-I'], True),
        (['--interactive'], True),
        (['-s', '-I'], True),
        (['-s', '--interactive'], True),
        (['-s'], False),
        ([], False)
    ])
    def test_interactive_flag_parsing(self, flag_variant, expected_interactive):
        """Test that interactive flags are parsed correctly."""
        parser = ParseFileFlags()
        argv = ['model-checker'] + flag_variant + ['test.py']
        
        with patch.object(sys, 'argv', argv):
            flags, _ = parser.parse()
            assert flags.interactive == expected_interactive
            
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
    def test_interactive_flag_passed_to_build_module(self, mock_build_module, tmp_path):
        """Test that interactive flag is passed to BuildModule."""
        # Create a test file using helper
        test_content = "# Test example file\n"
        test_file = create_test_module(test_content, tmp_path, 'test_example.py')
            
        with patch.object(sys, 'argv', ['model-checker', '-s', '-I', test_file]):
            main()
            
        # Check that BuildModule was called with flags containing interactive=True
        assert mock_build_module.called
        call_args = mock_build_module.call_args[0][0]
        assert hasattr(call_args, 'interactive')
        assert call_args.interactive is True
        assert call_args.save_output is True
                
    def test_help_shows_interactive_flag(self):
        """Test that help text includes interactive flag."""
        parser = ParseFileFlags()
        help_text = parser.parser.format_help()
        assert '--interactive' in help_text
        assert '-I' in help_text
        assert 'interactive save mode' in help_text
        
    @pytest.mark.parametrize("output_mode,other_flags", [
        ('batch', ['-s']),
        ('sequential', ['-s']),
        ('batch', ['-p', '-i']),
        ('sequential', ['-z', '-c'])
    ])
    def test_interactive_mode_combinations(self, output_mode, other_flags):
        """Test various flag combinations with interactive."""
        parser = ParseFileFlags()
        argv = ['model-checker'] + other_flags + ['-I', '--output-mode', output_mode, 'test.py']
        
        with patch.object(sys, 'argv', argv):
            flags, _ = parser.parse()
            assert flags.interactive is True
            assert flags.output_mode == output_mode
            
    @pytest.mark.parametrize("arg_order", [
        ['-I', '-s'],
        ['-s', '-I'],
        ['-p', '-I', '-s', '-i'],
        ['-i', '-s', '-p', '-I'],
        ['--interactive', '-s'],
        ['-s', '--interactive']
    ])
    def test_argument_order_independence(self, arg_order):
        """Test that argument order doesn't matter."""
        parser = ParseFileFlags()
        argv = ['model-checker'] + arg_order + ['test.py']
        
        with patch.object(sys, 'argv', argv):
            flags, _ = parser.parse()
            
            # Interactive should be set if -I or --interactive present
            if '-I' in arg_order or '--interactive' in arg_order:
                assert flags.interactive is True
            
            # Check other flags are set correctly
            if '-s' in arg_order:
                assert flags.save_output is True
            if '-p' in arg_order:
                assert flags.print_constraints is True
            if '-i' in arg_order:
                assert flags.print_impossible is True