"""Tests for interactive setting in output configuration."""

import unittest
from unittest.mock import Mock
from model_checker.output.config import create_output_config_from_cli_args
from model_checker.output.constants import MODE_BATCH, MODE_INTERACTIVE, MODE_SEQUENTIAL


class TestInteractiveSettingConfig(unittest.TestCase):
    """Test that interactive setting is properly handled in configuration."""
    
    def test_no_setting_no_flag_defaults_to_batch(self):
        """Test that with no setting and no flag, mode defaults to batch."""
        args = Mock(spec=['save'])
        args.save = []
        
        # No general_settings provided
        config = create_output_config_from_cli_args(args, None)
        
        self.assertEqual(config.mode, MODE_BATCH)
    
    def test_interactive_setting_true_enables_interactive(self):
        """Test that interactive: True in settings enables interactive mode."""
        args = Mock(spec=['save'])
        args.save = []
        
        general_settings = {'interactive': True}
        config = create_output_config_from_cli_args(args, general_settings)
        
        self.assertEqual(config.mode, MODE_INTERACTIVE)
    
    def test_interactive_setting_false_uses_batch(self):
        """Test that interactive: False in settings uses batch mode."""
        args = Mock(spec=['save'])
        args.save = []
        
        general_settings = {'interactive': False}
        config = create_output_config_from_cli_args(args, general_settings)
        
        self.assertEqual(config.mode, MODE_BATCH)
    
    def test_cli_flag_overrides_setting_false(self):
        """Test that --interactive flag overrides interactive: False setting."""
        args = Mock(spec=['save', 'interactive'])
        args.save = []
        args.interactive = True
        
        general_settings = {'interactive': False}  # Setting says false
        config = create_output_config_from_cli_args(args, general_settings)
        
        # CLI flag should win
        self.assertEqual(config.mode, MODE_INTERACTIVE)
    
    def test_cli_flag_overrides_setting_true(self):
        """Test that lack of --interactive flag with interactive: True still uses interactive."""
        args = Mock(spec=['save'])  # No interactive attribute
        args.save = []
        
        general_settings = {'interactive': True}
        config = create_output_config_from_cli_args(args, general_settings)
        
        # Setting should enable interactive
        self.assertEqual(config.mode, MODE_INTERACTIVE)
    
    def test_output_mode_flag_overrides_setting(self):
        """Test that --output-mode flag overrides interactive setting."""
        args = Mock(spec=['save', 'output_mode'])
        args.save = []
        args.output_mode = MODE_SEQUENTIAL
        
        general_settings = {'interactive': True}  # Setting says interactive
        config = create_output_config_from_cli_args(args, general_settings)
        
        # output_mode flag should win over setting (but not over --interactive)
        self.assertEqual(config.mode, MODE_SEQUENTIAL)
    
    def test_interactive_flag_beats_output_mode_and_setting(self):
        """Test that --interactive flag has highest priority."""
        args = Mock(spec=['save', 'interactive', 'output_mode'])
        args.save = []
        args.interactive = True
        args.output_mode = MODE_SEQUENTIAL  # Conflicts with interactive
        
        general_settings = {'interactive': False}  # Also conflicts
        config = create_output_config_from_cli_args(args, general_settings)
        
        # --interactive flag should win over everything
        self.assertEqual(config.mode, MODE_INTERACTIVE)
    
    def test_setting_with_sequential_output_mode(self):
        """Test interaction between setting and sequential mode."""
        args = Mock(spec=['save', 'output_mode', 'sequential_files'])
        args.save = []
        args.output_mode = MODE_SEQUENTIAL
        args.sequential_files = 'single'
        
        general_settings = {'interactive': False}
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
        
        general_settings = {'interactive': None}
        config = create_output_config_from_cli_args(args, general_settings)
        
        # None should be treated as False
        self.assertEqual(config.mode, MODE_BATCH)
    
    def test_priority_order_complete(self):
        """Test complete priority order: CLI > output_mode > setting > default."""
        # Test 1: Only setting
        args1 = Mock(spec=['save'])
        args1.save = []
        config1 = create_output_config_from_cli_args(args1, {'interactive': True})
        self.assertEqual(config1.mode, MODE_INTERACTIVE)
        
        # Test 2: Setting + output_mode (output_mode wins)
        args2 = Mock(spec=['save', 'output_mode'])
        args2.save = []
        args2.output_mode = MODE_SEQUENTIAL
        config2 = create_output_config_from_cli_args(args2, {'interactive': True})
        self.assertEqual(config2.mode, MODE_SEQUENTIAL)
        
        # Test 3: Setting + output_mode + interactive flag (interactive wins)
        args3 = Mock(spec=['save', 'output_mode', 'interactive'])
        args3.save = []
        args3.output_mode = MODE_SEQUENTIAL
        args3.interactive = True
        config3 = create_output_config_from_cli_args(args3, {'interactive': False})
        self.assertEqual(config3.mode, MODE_INTERACTIVE)


if __name__ == '__main__':
    unittest.main()