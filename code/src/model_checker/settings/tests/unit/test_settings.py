"""Unit tests for the settings module.
"""

import unittest
from model_checker.settings.settings import SettingsManager
from model_checker.settings.errors import ValidationError

class MockSemantics:
    """Mock semantics for testing."""
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'max_time': 1,
        'expectation': None,
        'solver': 'z3',  # Required for solver validation tests
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
        # Now uses SemanticDefaults general settings
        from model_checker.models.semantic import SemanticDefaults
        self.assertEqual(settings, SemanticDefaults.DEFAULT_GENERAL_SETTINGS)
        
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


class TestSolverValidation(unittest.TestCase):
    """Test solver field validation in settings."""

    def setUp(self):
        """Set up test cases."""
        self.semantic_theory = {
            'semantics': MockSemantics
        }
        self.settings_manager = SettingsManager(self.semantic_theory)

    def test_validate_solver_z3(self):
        """Test that solver='z3' is valid."""
        settings = self.settings_manager.validate_example_settings({'solver': 'z3'})
        self.assertEqual(settings['solver'], 'z3')

    def test_validate_solver_cvc5(self):
        """Test that solver='cvc5' is valid."""
        settings = self.settings_manager.validate_example_settings({'solver': 'cvc5'})
        self.assertEqual(settings['solver'], 'cvc5')

    def test_validate_solver_default(self):
        """Test that default solver is 'z3'."""
        settings = self.settings_manager.validate_example_settings(None)
        self.assertEqual(settings['solver'], 'z3')

    def test_validate_solver_invalid_raises(self):
        """Test that invalid solver value raises ValidationError."""
        with self.assertRaises(ValidationError) as context:
            self.settings_manager.validate_example_settings({'solver': 'invalid'})
        self.assertIn('invalid', str(context.exception))
        self.assertIn("('z3', 'cvc5')", str(context.exception))

    def test_solver_in_complete_settings(self):
        """Test that solver is included in complete settings."""
        result = self.settings_manager.get_complete_settings(
            user_general_settings={},
            user_example_settings={'solver': 'cvc5'},
            module_flags=None
        )
        self.assertEqual(result['solver'], 'cvc5')


if __name__ == '__main__':
    unittest.main()