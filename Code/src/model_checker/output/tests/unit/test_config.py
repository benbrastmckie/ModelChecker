"""Unit tests for output configuration management."""

import unittest
from unittest.mock import Mock, MagicMock
from model_checker.output.config import OutputConfig, create_output_config_from_cli_args
from model_checker.output.constants import (
    DEFAULT_FORMATS, FORMAT_MARKDOWN, FORMAT_JSON, FORMAT_NOTEBOOK,
    MODE_BATCH, MODE_SEQUENTIAL,
    SEQUENTIAL_SINGLE, SEQUENTIAL_MULTIPLE
)


class TestOutputConfig(unittest.TestCase):
    """Test OutputConfig class."""
    
    def test_init_with_defaults(self):
        """Test initialization with default values."""
        config = OutputConfig()
        
        self.assertEqual(config.enabled_formats, set(DEFAULT_FORMATS))
        self.assertEqual(config.mode, MODE_BATCH)
        self.assertEqual(config.sequential_files, SEQUENTIAL_MULTIPLE)
        self.assertTrue(config.save_output)
    
    def test_init_with_custom_values(self):
        """Test initialization with custom values."""
        config = OutputConfig(
            formats=['markdown'],
            mode=MODE_SEQUENTIAL,
            sequential_files=SEQUENTIAL_SINGLE,
            save_output=False
        )
        
        self.assertEqual(config.enabled_formats, {'markdown'})
        self.assertEqual(config.mode, MODE_SEQUENTIAL)
        self.assertEqual(config.sequential_files, SEQUENTIAL_SINGLE)
        self.assertFalse(config.save_output)
    
    def test_init_with_none_formats(self):
        """Test initialization with None formats uses defaults."""
        config = OutputConfig(formats=None)
        self.assertEqual(config.enabled_formats, set(DEFAULT_FORMATS))
    
    def test_is_format_enabled(self):
        """Test checking if format is enabled."""
        config = OutputConfig(formats=['markdown'])
        
        self.assertTrue(config.is_format_enabled('markdown'))
        self.assertFalse(config.is_format_enabled('json'))
        self.assertFalse(config.is_format_enabled('unknown'))
    
    def test_get_enabled_formats(self):
        """Test getting enabled formats returns a copy."""
        config = OutputConfig(formats=['markdown', 'json'])
        formats = config.get_enabled_formats()
        
        self.assertEqual(formats, {'markdown', 'json'})
        
        # Modify returned set shouldn't affect original
        formats.add('new_format')
        self.assertEqual(config.enabled_formats, {'markdown', 'json'})
    
    def test_disable_format(self):
        """Test disabling a format."""
        config = OutputConfig(formats=['markdown', 'json'])
        
        config.disable_format('markdown')
        self.assertFalse(config.is_format_enabled('markdown'))
        self.assertTrue(config.is_format_enabled('json'))
        
        # Disabling non-existent format should not error
        config.disable_format('unknown')
        
    def test_enable_format(self):
        """Test enabling a format."""
        config = OutputConfig(formats=['markdown'])
        
        config.enable_format('json')
        self.assertTrue(config.is_format_enabled('json'))
        self.assertTrue(config.is_format_enabled('markdown'))
        
        # Enabling already enabled format should not error
        config.enable_format('markdown')
        self.assertTrue(config.is_format_enabled('markdown'))


class TestOutputConfigFromCLI(unittest.TestCase):
    """Test OutputConfig.from_cli_args method."""
    
    def test_from_cli_args_no_save_flag(self):
        """Test CLI args without save flag."""
        args = Mock(spec=[])  # No attributes at all, including save
        
        config = create_output_config_from_cli_args(args)
        
        self.assertFalse(config.save_output)
        self.assertEqual(config.enabled_formats, set())
        self.assertEqual(config.mode, MODE_BATCH)
    
    def test_from_cli_args_save_flag_no_formats(self):
        """Test --save with no format arguments (all formats)."""
        args = Mock()
        args.save = []  # Empty list means --save was used without args
        
        config = create_output_config_from_cli_args(args)
        
        self.assertTrue(config.save_output)
        self.assertEqual(config.enabled_formats, set(DEFAULT_FORMATS))
    
    def test_from_cli_args_save_flag_with_markdown(self):
        """Test --save markdown."""
        args = Mock()
        args.save = ['markdown']
        
        config = create_output_config_from_cli_args(args)
        
        self.assertTrue(config.save_output)
        self.assertEqual(config.enabled_formats, {FORMAT_MARKDOWN})
    
    def test_from_cli_args_save_flag_with_json(self):
        """Test --save json."""
        args = Mock()
        args.save = ['json']
        
        config = create_output_config_from_cli_args(args)
        
        self.assertTrue(config.save_output)
        self.assertEqual(config.enabled_formats, {FORMAT_JSON})
    
    def test_from_cli_args_save_flag_with_multiple_formats(self):
        """Test --save markdown json."""
        args = Mock()
        args.save = ['markdown', 'json']
        
        config = create_output_config_from_cli_args(args)
        
        self.assertTrue(config.save_output)
        self.assertEqual(config.enabled_formats, {FORMAT_MARKDOWN, FORMAT_JSON})
    
    def test_from_cli_args_save_flag_includes_jupyter(self):
        """Test --save jupyter is included in enabled formats."""
        args = Mock()
        args.save = ['markdown', 'jupyter', 'json']
        
        config = create_output_config_from_cli_args(args)
        
        self.assertTrue(config.save_output)
        # jupyter should be in formats (unified pipeline)
        self.assertEqual(config.enabled_formats, {FORMAT_MARKDOWN, FORMAT_JSON, FORMAT_NOTEBOOK})
    
    def test_from_cli_args_save_flag_none_value(self):
        """Test save attribute is None (not provided)."""
        args = Mock()
        args.save = None
        
        config = create_output_config_from_cli_args(args)
        
        self.assertFalse(config.save_output)
        self.assertEqual(config.enabled_formats, set())
    
    def test_from_cli_args_interactive_mode(self):
        """Test interactive mode detection."""
        args = Mock()
        args.save = []
        args.interactive = True
        
        config = create_output_config_from_cli_args(args)
        
        # Interactive flag means sequential mode
        self.assertEqual(config.mode, MODE_SEQUENTIAL)
    
    def test_from_cli_args_output_mode_specified(self):
        """Test explicit output_mode."""
        args = Mock()
        args.save = []
        args.interactive = False
        args.output_mode = MODE_SEQUENTIAL
        
        config = create_output_config_from_cli_args(args)
        
        self.assertEqual(config.mode, MODE_SEQUENTIAL)
    
    def test_from_cli_args_interactive_overrides_output_mode(self):
        """Test interactive flag overrides output_mode."""
        args = Mock()
        args.save = []
        args.interactive = True
        args.output_mode = MODE_SEQUENTIAL
        
        config = create_output_config_from_cli_args(args)
        
        # Interactive should take precedence - uses sequential mode
        self.assertEqual(config.mode, MODE_SEQUENTIAL)
    
    def test_from_cli_args_sequential_files_option(self):
        """Test sequential_files option."""
        args = Mock()
        args.save = []
        args.sequential_files = SEQUENTIAL_SINGLE
        
        config = create_output_config_from_cli_args(args)
        
        self.assertEqual(config.sequential_files, SEQUENTIAL_SINGLE)
    
    def test_from_cli_args_all_options_combined(self):
        """Test all CLI options together."""
        args = Mock()
        args.save = ['markdown', 'json']
        args.interactive = True
        args.output_mode = MODE_BATCH  # Should be overridden
        args.sequential_files = SEQUENTIAL_SINGLE
        
        config = create_output_config_from_cli_args(args)
        
        self.assertTrue(config.save_output)
        self.assertEqual(config.enabled_formats, {FORMAT_MARKDOWN, FORMAT_JSON})
        self.assertEqual(config.mode, MODE_SEQUENTIAL)  # Interactive uses sequential
        self.assertEqual(config.sequential_files, SEQUENTIAL_SINGLE)
    
    def test_from_cli_args_missing_attributes(self):
        """Test handling of missing attributes gracefully."""
        # Create args with only some attributes
        args = Mock(spec=['save'])  # Only has save attribute
        args.save = ['markdown']
        
        config = create_output_config_from_cli_args(args)
        
        self.assertTrue(config.save_output)
        self.assertEqual(config.enabled_formats, {FORMAT_MARKDOWN})
        self.assertEqual(config.mode, MODE_BATCH)  # Default
        self.assertEqual(config.sequential_files, SEQUENTIAL_MULTIPLE)  # Default
    
    def test_from_cli_args_empty_args_object(self):
        """Test with completely empty args object."""
        args = Mock(spec=[])  # No attributes at all
        
        config = create_output_config_from_cli_args(args)
        
        self.assertFalse(config.save_output)
        self.assertEqual(config.enabled_formats, set())
        self.assertEqual(config.mode, MODE_BATCH)
        self.assertEqual(config.sequential_files, SEQUENTIAL_MULTIPLE)
    
    def test_from_cli_args_unknown_format_ignored(self):
        """Test unknown formats are ignored."""
        args = Mock()
        args.save = ['markdown', 'unknown', 'json', 'pdf']
        
        config = create_output_config_from_cli_args(args)
        
        # Only recognized formats should be included
        self.assertEqual(config.enabled_formats, {FORMAT_MARKDOWN, FORMAT_JSON})


if __name__ == '__main__':
    unittest.main()