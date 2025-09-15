"""Tests for sequential setting in output configuration."""

import unittest
from unittest.mock import Mock
from model_checker.output.config import create_output_config_from_cli_args
from model_checker.output.constants import MODE_BATCH, MODE_SEQUENTIAL


class TestSequentialSettingConfig(unittest.TestCase):
    """Test that sequential setting is properly handled in configuration."""
    
    def test_no_setting_no_flag_defaults_to_batch(self):
        """Test that with no setting and no flag, mode defaults to batch."""
        args = Mock(spec=['save'])
        args.save = []
        
        # No general_settings provided
        config = create_output_config_from_cli_args(args, None)
        
        self.assertEqual(config.mode, MODE_BATCH)
    
    def test_sequential_setting_true_enables_sequential(self):
        """Test that sequential: True in settings enables sequential mode."""
        args = Mock(spec=['save'])
        args.save = []
        
        general_settings = {'sequential': True}
        config = create_output_config_from_cli_args(args, general_settings)
        
        # Sequential setting enables sequential mode
        self.assertEqual(config.mode, MODE_SEQUENTIAL)
    
    def test_sequential_setting_false_uses_batch(self):
        """Test that sequential: False in settings uses batch mode."""
        args = Mock(spec=['save'])
        args.save = []
        
        general_settings = {'sequential': False}
        config = create_output_config_from_cli_args(args, general_settings)
        
        self.assertEqual(config.mode, MODE_BATCH)
    
    def test_cli_flag_overrides_setting_false(self):
        """Test that --sequential flag overrides interactive: False setting."""
        args = Mock(spec=['save', 'interactive'])
        args.save = []
        args.sequential = True
        
        general_settings = {'sequential': False}  # Setting says false
        config = create_output_config_from_cli_args(args, general_settings)
        
        # CLI flag should win - interactive uses sequential mode
        self.assertEqual(config.mode, MODE_SEQUENTIAL)
    
    def test_cli_flag_overrides_setting_true(self):
        """Test that lack of --sequential flag with interactive: True still uses sequential."""
        args = Mock(spec=['save'])  # No interactive attribute
        args.save = []
        
        general_settings = {'sequential': True}
        config = create_output_config_from_cli_args(args, general_settings)
        
        # Setting should enable sequential mode
        self.assertEqual(config.mode, MODE_SEQUENTIAL)
    
    def test_output_mode_flag_with_interactive_setting(self):
        """Test that interactive setting takes precedence over --output-mode."""
        args = Mock(spec=['save', 'output_mode'])
        args.save = []
        args.output_mode = MODE_BATCH  # Try to set batch
        
        general_settings = {'sequential': True}  # Setting says interactive
        config = create_output_config_from_cli_args(args, general_settings)
        
        # Interactive setting means sequential mode
        self.assertEqual(config.mode, MODE_SEQUENTIAL)
    
    def test_interactive_flag_beats_output_mode_and_setting(self):
        """Test that --sequential flag has highest priority."""
        args = Mock(spec=['save', 'interactive', 'output_mode'])
        args.save = []
        args.sequential = True
        args.output_mode = MODE_BATCH  # Try to set batch
        
        general_settings = {'sequential': False}  # Also conflicts
        config = create_output_config_from_cli_args(args, general_settings)
        
        # --sequential flag should win - uses sequential mode
        self.assertEqual(config.mode, MODE_SEQUENTIAL)
    
    def test_setting_with_sequential_output_mode(self):
        """Test interaction between setting and sequential mode."""
        args = Mock(spec=['save', 'output_mode', 'sequential_files'])
        args.save = []
        args.output_mode = MODE_SEQUENTIAL
        args.sequential_files = 'single'
        
        general_settings = {'sequential': False}
        config = create_output_config_from_cli_args(args, general_settings)
        
        self.assertEqual(config.mode, MODE_SEQUENTIAL)
        self.assertEqual(config.sequential_files, 'single')
    
    def test_empty_settings_dict(self):
        """Test with empty settings dictionary."""
        args = Mock(spec=['save'])
        args.save = []
        
        general_settings = {}  # Empty dict
        config = create_output_config_from_cli_args(args, general_settings)
        
        # Should default to batch
        self.assertEqual(config.mode, MODE_BATCH)
    
    def test_none_settings_value(self):
        """Test with None value for interactive in settings."""
        args = Mock(spec=['save'])
        args.save = []
        
        general_settings = {'sequential': None}
        config = create_output_config_from_cli_args(args, general_settings)
        
        # None should be treated as False
        self.assertEqual(config.mode, MODE_BATCH)
    
    def test_priority_order_complete(self):
        """Test complete priority order: CLI > output_mode > setting > default."""
        # Test 1: Only setting
        args1 = Mock(spec=['save'])
        args1.save = []
        config1 = create_output_config_from_cli_args(args1, {'sequential': True})
        self.assertEqual(config1.mode, MODE_SEQUENTIAL)
        
        # Test 2: No interactive, output_mode works
        args2 = Mock(spec=['save', 'output_mode'])
        args2.save = []
        args2.output_mode = MODE_BATCH
        config2 = create_output_config_from_cli_args(args2, {'sequential': False})
        self.assertEqual(config2.mode, MODE_BATCH)
        
        # Test 3: Sequential flag wins over everything
        args3 = Mock(spec=['save', 'output_mode', 'sequential'])
        args3.save = []
        args3.output_mode = MODE_BATCH
        args3.sequential = True
        config3 = create_output_config_from_cli_args(args3, {'sequential': False})
        self.assertEqual(config3.mode, MODE_SEQUENTIAL)


if __name__ == '__main__':
    unittest.main()