"""Tests for simplified output configuration."""

import unittest
from unittest.mock import Mock
from model_checker.output.config import OutputConfig, create_output_config


class TestOutputConfig(unittest.TestCase):
    """Test OutputConfig class."""
    
    def test_default_config(self):
        """Test default configuration."""
        config = OutputConfig()
        
        self.assertEqual(config.formats, ['markdown', 'json'])
        self.assertFalse(config.sequential)
        self.assertTrue(config.save_output)
    
    def test_config_with_sequential(self):
        """Test configuration with sequential mode enabled."""
        config = OutputConfig(sequential=True)
        
        self.assertTrue(config.sequential)
        self.assertTrue(config.save_output)
    
    def test_config_with_custom_formats(self):
        """Test configuration with custom formats."""
        config = OutputConfig(formats=['markdown'])
        
        self.assertEqual(config.formats, ['markdown'])
        self.assertTrue(config.is_format_enabled('markdown'))
        self.assertFalse(config.is_format_enabled('json'))
    
    def test_is_format_enabled(self):
        """Test format checking."""
        config = OutputConfig(formats=['markdown', 'notebook'])
        
        self.assertTrue(config.is_format_enabled('markdown'))
        self.assertTrue(config.is_format_enabled('notebook'))
        self.assertFalse(config.is_format_enabled('json'))


class TestCreateOutputConfig(unittest.TestCase):
    """Test create_output_config function."""
    
    def test_no_save_flag(self):
        """Test with no save flag."""
        args = Mock(spec=[])
        config = create_output_config(args)
        
        self.assertFalse(config.save_output)
        self.assertEqual(config.formats, [])
    
    def test_save_flag_no_formats(self):
        """Test --save with no format arguments."""
        args = Mock(spec=['save'])
        args.save = []  # Empty means all formats
        
        config = create_output_config(args)
        
        self.assertTrue(config.save_output)
        self.assertEqual(config.formats, ['markdown', 'json', 'notebook'])
    
    def test_save_flag_with_formats(self):
        """Test --save with specific formats."""
        args = Mock(spec=['save'])
        args.save = ['markdown', 'json']
        
        config = create_output_config(args)
        
        self.assertTrue(config.save_output)
        self.assertEqual(set(config.formats), {'markdown', 'json'})
    
    def test_sequential_flag(self):
        """Test --sequential flag."""
        args = Mock(spec=['save', 'sequential'])
        args.save = []
        args.sequential = True
        
        config = create_output_config(args)
        
        self.assertTrue(config.sequential)
    
    def test_sequential_setting(self):
        """Test sequential setting."""
        args = Mock(spec=['save'])
        args.save = []
        
        settings = {'sequential': True}
        config = create_output_config(args, settings)
        
        self.assertTrue(config.sequential)
    
    def test_sequential_flag_overrides_setting(self):
        """Test that CLI flag overrides setting."""
        args = Mock(spec=['save', 'sequential'])
        args.save = []
        args.sequential = True
        
        settings = {'sequential': False}  # Setting says no
        config = create_output_config(args, settings)
        
        # CLI flag should win
        self.assertTrue(config.sequential)
    
    def test_no_sequential_by_default(self):
        """Test that sequential mode is off by default."""
        args = Mock(spec=['save'])
        args.save = []
        
        config = create_output_config(args)
        
        self.assertFalse(config.sequential)


if __name__ == '__main__':
    unittest.main()