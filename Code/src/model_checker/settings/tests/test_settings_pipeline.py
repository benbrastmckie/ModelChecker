"""End-to-end test for the settings pipeline.

This script tests the SettingsManager directly with custom mock objects.
"""

import unittest
from model_checker.settings.settings import SettingsManager

class MockSemantics:
    """Mock semantics for testing."""
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'contingent': False,
        'max_time': 1,
    }
    
    DEFAULT_GENERAL_SETTINGS = {
        'print_z3': False,
        'print_constraints': False,
    }

class MockBuildModule:
    """Mock BuildModule for testing."""
    def __init__(self, general_settings=None):
        self.general_settings = general_settings or {}

class MockFlags:
    """Mock module flags for testing."""
    def __init__(self, **kwargs):
        for key, value in kwargs.items():
            setattr(self, key, value)

class TestSettingsPipeline(unittest.TestCase):
    """Test the settings pipeline with mock objects."""
    
    def test_complete_settings_flow(self):
        """Test the complete settings flow from defaults to flags."""
        # Setup mock objects
        semantic_theory = {'semantics': MockSemantics}
        settings_manager = SettingsManager(semantic_theory)
        
        # 1. Test with just defaults (no user settings or flags)
        result1 = settings_manager.get_complete_settings(None, None, None)
        self.assertEqual(result1['N'], 3)  # From DEFAULT_EXAMPLE_SETTINGS
        self.assertEqual(result1['print_z3'], False)  # From DEFAULT_GENERAL_SETTINGS
        
        # 2. Test with user general settings overriding defaults
        general_settings = {'print_z3': True}
        result2 = settings_manager.get_complete_settings(general_settings, None, None)
        self.assertEqual(result2['print_z3'], True)  # From user general_settings
        
        # 3. Test with example settings overriding general settings
        example_settings = {'N': 5}
        result3 = settings_manager.get_complete_settings(general_settings, example_settings, None)
        self.assertEqual(result3['N'], 5)  # From example_settings
        self.assertEqual(result3['print_z3'], True)  # From general_settings
        
        # 4. Test with flags overriding everything
        flags = MockFlags(print_z3=False, print_constraints=True)
        result4 = settings_manager.get_complete_settings(general_settings, example_settings, flags)
        self.assertEqual(result4['N'], 5)  # From example_settings (not affected by flags)
        self.assertEqual(result4['print_z3'], False)  # From flags (overrides general_settings)
        self.assertEqual(result4['print_constraints'], True)  # From flags
    
    def test_validation_warnings(self):
        """Test that unknown settings trigger warnings but are ignored."""
        import io
        import sys
        from contextlib import redirect_stdout
        
        # Setup mock objects
        semantic_theory = {'semantics': MockSemantics}
        settings_manager = SettingsManager(semantic_theory)
        
        # Create settings with unknown keys
        general_settings = {'print_z3': True, 'unknown_general': 'value'}
        example_settings = {'N': 5, 'unknown_example': 'value'}
        
        # Capture stdout to check for warnings
        f = io.StringIO()
        with redirect_stdout(f):
            result = settings_manager.get_complete_settings(general_settings, example_settings, None)
        
        # Check that result doesn't contain unknown settings
        self.assertNotIn('unknown_general', result)
        self.assertNotIn('unknown_example', result)
        
        # Check that warnings were printed
        output = f.getvalue()
        self.assertIn("Warning: Unknown general setting 'unknown_general'", output)
        self.assertIn("Warning: Unknown example setting 'unknown_example'", output)

if __name__ == '__main__':
    unittest.main()
