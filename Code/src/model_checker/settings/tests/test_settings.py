"""Unit tests for the settings module.
"""

import unittest
from model_checker.settings.settings import SettingsManager

class MockSemantics:
    """Mock semantics for testing."""
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'max_time': 1,
        'expectation': None,
    }
    
    DEFAULT_GENERAL_SETTINGS = {
        'print_z3': False,
        'save_output': False,
    }

class MockFlags:
    """Mock flags for testing."""
    def __init__(self, **kwargs):
        for key, value in kwargs.items():
            setattr(self, key, value)

class TestSettingsManager(unittest.TestCase):
    """Test the SettingsManager class."""
    
    def setUp(self):
        """Set up test cases."""
        self.semantic_theory = {
            'semantics': MockSemantics
        }
        self.settings_manager = SettingsManager(self.semantic_theory)
    
    def test_validate_general_settings(self):
        """Test validating general settings."""
        # Test with None
        settings = self.settings_manager.validate_general_settings(None)
        self.assertEqual(settings, MockSemantics.DEFAULT_GENERAL_SETTINGS)
        
        # Test with valid settings
        user_settings = {'print_z3': True}
        settings = self.settings_manager.validate_general_settings(user_settings)
        self.assertEqual(settings['print_z3'], True)
        
        # Test with unknown settings (should print warning but include valid ones)
        user_settings = {'print_z3': True, 'unknown': 'value'}
        settings = self.settings_manager.validate_general_settings(user_settings)
        self.assertEqual(settings['print_z3'], True)
        self.assertNotIn('unknown', settings)
    
    def test_validate_example_settings(self):
        """Test validating example settings."""
        # Test with None
        settings = self.settings_manager.validate_example_settings(None)
        self.assertEqual(settings, MockSemantics.DEFAULT_EXAMPLE_SETTINGS)
        
        # Test with valid settings
        user_settings = {'N': 5}
        settings = self.settings_manager.validate_example_settings(user_settings)
        self.assertEqual(settings['N'], 5)
        
        # Test with unknown settings
        user_settings = {'N': 5, 'unknown': 'value'}
        settings = self.settings_manager.validate_example_settings(user_settings)
        self.assertEqual(settings['N'], 5)
        self.assertNotIn('unknown', settings)
    
    def test_apply_flag_overrides(self):
        """Test applying flag overrides."""
        settings = {'print_z3': False, 'N': 3}
        flags = MockFlags(print_z3=True, unknown=True)
        
        result = self.settings_manager.apply_flag_overrides(settings, flags)
        self.assertEqual(result['print_z3'], True)
        self.assertEqual(result['N'], 3)
    
    def test_get_complete_settings(self):
        """Test getting complete settings."""
        general_settings = {'print_z3': True}
        example_settings = {'N': 5}
        flags = MockFlags(save_output=True)
        
        result = self.settings_manager.get_complete_settings(
            general_settings, example_settings, flags
        )
        
        # Check all levels of settings are applied in correct order
        self.assertEqual(result['print_z3'], True)  # From general_settings
        self.assertEqual(result['N'], 5)  # From example_settings
        self.assertEqual(result['save_output'], True)  # From flags
        self.assertEqual(result['expectation'], None)  # From DEFAULT_EXAMPLE_SETTINGS

if __name__ == '__main__':
    unittest.main()