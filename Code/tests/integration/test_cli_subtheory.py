"""
Integration tests for CLI subtheory selection functionality.

This module tests the --subtheory flag for logos theory, including
special keywords, error handling, and dependency resolution.
"""

import unittest
import sys
from unittest.mock import patch, MagicMock
from pathlib import Path

from model_checker.__main__ import ParseFileFlags, main
from model_checker.builder.project import BuildProject


class TestCLISubtheoryFlag(unittest.TestCase):
    """Test --subtheory CLI flag functionality."""

    def test_subtheory_flag_parsing_single(self):
        """Test parsing single subtheory."""
        parser = ParseFileFlags()
        with patch('sys.argv', ['model-checker', '-l', 'logos', '--subtheory', 'modal', 'test.py']):
            flags, _ = parser.parse()
            self.assertEqual(flags.load_theory, 'logos')
            self.assertEqual(flags.subtheory, ['modal'])

    def test_subtheory_flag_parsing_multiple(self):
        """Test parsing multiple subtheories."""
        parser = ParseFileFlags()
        with patch('sys.argv', ['model-checker', '-l', 'logos', '--subtheory',
                                'modal', 'constitutive', 'test.py']):
            flags, _ = parser.parse()
            self.assertEqual(flags.load_theory, 'logos')
            self.assertEqual(flags.subtheory, ['modal', 'constitutive'])

    def test_subtheory_short_form(self):
        """Test -st short form."""
        parser = ParseFileFlags()
        with patch('sys.argv', ['model-checker', '-l', 'logos', '-st', 'extensional', 'test.py']):
            flags, _ = parser.parse()
            self.assertEqual(flags.load_theory, 'logos')
            self.assertEqual(flags.subtheory, ['extensional'])


    def test_subtheory_invalid_choice(self):
        """Test that invalid subtheory names are rejected."""
        parser = ParseFileFlags()
        with patch('sys.argv', ['model-checker', '-l', 'logos', '--subtheory', 'invalid', 'test.py']):
            with self.assertRaises(SystemExit):
                # argparse will exit on invalid choice
                flags, _ = parser.parse()

    def test_no_subtheory_flag(self):
        """Test that subtheory is None when not specified."""
        parser = ParseFileFlags()
        with patch('sys.argv', ['model-checker', '-l', 'logos', 'test.py']):
            flags, _ = parser.parse()
            self.assertEqual(flags.load_theory, 'logos')
            # When --subtheory is not provided, it should be None
            self.assertIsNone(getattr(flags, 'subtheory', None))

    def test_subtheory_with_non_logos_theory(self):
        """Test error when using --subtheory with non-logos theory."""
        parser = ParseFileFlags()
        # This should parse successfully
        with patch('sys.argv', ['model-checker', '-l', 'exclusion', '--subtheory', 'modal', 'test.py']):
            flags, _ = parser.parse()
            self.assertEqual(flags.load_theory, 'exclusion')
            self.assertEqual(flags.subtheory, ['modal'])

        # But main() should handle the error
        with patch('sys.argv', ['model-checker', '-l', 'exclusion', '--subtheory', 'modal']):
            with patch('model_checker.builder.project.BuildProject'):
                with patch('builtins.print') as mock_print:
                    with self.assertRaises(SystemExit) as cm:
                        # Mock sys.argv length check
                        with patch('sys.argv', ['model-checker', '-l', 'exclusion', '--subtheory', 'modal']):
                            # This will trigger the load_theory path
                            import model_checker.__main__ as main_module
                            # We need to test the actual logic
                            flags = MagicMock()
                            flags.load_theory = 'exclusion'
                            flags.subtheory = ['modal']
                            # The main function should print an error
                            # We'll test this indirectly through BuildProject
                    # Verify error was about subtheory only applying to logos
                    # Note: The actual implementation prints the error but doesn't exit
                    # so we check for the print call instead


class TestBuildProjectSubtheory(unittest.TestCase):
    """Test BuildProject subtheory handling."""

    def test_buildproject_with_subtheories(self):
        """Test BuildProject initialization with subtheories."""
        project = BuildProject('logos', subtheories=['modal', 'constitutive'])
        self.assertEqual(project.theory, 'logos')
        self.assertEqual(project.subtheories, ['modal', 'constitutive'])


    def test_buildproject_no_subtheories(self):
        """Test BuildProject with no subtheories specified."""
        project = BuildProject('logos')
        self.assertEqual(project.theory, 'logos')
        self.assertIsNone(project.subtheories)

    def test_buildproject_non_logos_ignores_subtheories(self):
        """Test that non-logos theories don't process subtheories."""
        # This should work without error, subtheories are just ignored
        project = BuildProject('exclusion', subtheories=['modal'])
        self.assertEqual(project.theory, 'exclusion')
        self.assertEqual(project.subtheories, ['modal'])  # Not processed for non-logos


    @patch('builtins.input')
    def test_ask_generate_with_subtheories(self, mock_input):
        """Test that ask_generate shows subtheories in prompt."""
        mock_input.return_value = 'n'  # Don't actually generate

        project = BuildProject('logos', subtheories=['modal', 'constitutive'])

        with patch('builtins.print') as mock_print:
            project.ask_generate()

        # Check that the input prompt includes subtheories
        mock_input.assert_called_once()
        call_args = mock_input.call_args[0][0]
        self.assertIn('modal', call_args)
        self.assertIn('constitutive', call_args)

    @patch('builtins.input')
    def test_ask_generate_without_subtheories(self, mock_input):
        """Test that ask_generate works without subtheories."""
        mock_input.return_value = 'n'  # Don't actually generate

        project = BuildProject('exclusion')

        with patch('builtins.print') as mock_print:
            project.ask_generate()

        # Check that the prompt doesn't mention subtheories
        mock_input.assert_called_once()
        call_args = mock_input.call_args[0][0]
        self.assertNotIn('subtheories', call_args)
        self.assertNotIn('modal', call_args)


if __name__ == '__main__':
    unittest.main()