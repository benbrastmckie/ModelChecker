"""Test error handling in the settings package."""

import unittest
from unittest.mock import MagicMock
from model_checker.settings.settings import SettingsManager
from model_checker.settings.errors import (
    SettingsError, ValidationError, TypeConversionError,
    RangeError, MissingRequiredError, UnknownSettingError,
    TheoryCompatibilityError
)


class TestErrorHandling(unittest.TestCase):
    """Test custom error handling in SettingsManager."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Create a mock semantic theory
        mock_semantics = MagicMock()
        mock_semantics.DEFAULT_GENERAL_SETTINGS = {
            "print_impossible": False,
            "print_constraints": False,
            "timeout": 300,
            "iterate": 1,
        }
        mock_semantics.DEFAULT_EXAMPLE_SETTINGS = {
            "proposition_letters": [],
            "formula": None,
            "max_depth": 10,
        }
        
        self.semantic_theory = {"semantics": mock_semantics}
        
    def test_strict_mode_raises_on_unknown_setting(self):
        """Test that strict mode raises UnknownSettingError for unknown settings."""
        manager = SettingsManager(
            self.semantic_theory, 
            theory_name="TestTheory",
            strict_mode=True
        )
        
        # Test unknown general setting
        with self.assertRaises(UnknownSettingError) as context:
            manager.validate_general_settings({"unknown_setting": True})
        
        error = context.exception
        self.assertEqual(error.setting, "unknown_setting")
        self.assertIsNotNone(error.suggestion)
        
        # Test unknown example setting
        with self.assertRaises(UnknownSettingError) as context:
            manager.validate_example_settings({"bad_setting": "value"})
        
        error = context.exception
        self.assertEqual(error.setting, "bad_setting")
        self.assertIsNotNone(error.suggestion)
    
    def test_non_strict_mode_warns_only(self):
        """Test that non-strict mode only warns, doesn't raise."""
        manager = SettingsManager(
            self.semantic_theory,
            theory_name="TestTheory",
            strict_mode=False
        )
        
        # Should not raise, just warn
        result = manager.validate_general_settings({"unknown_setting": True})
        self.assertIsInstance(result, dict)
        self.assertNotIn("unknown_setting", result)
        
        result = manager.validate_example_settings({"bad_setting": "value"})
        self.assertIsInstance(result, dict)
        self.assertNotIn("bad_setting", result)
    
    def test_type_conversion_error(self):
        """Test TypeConversionError is raised for invalid type conversions."""
        manager = SettingsManager(self.semantic_theory, strict_mode=True)
        
        # Test invalid conversion
        with self.assertRaises(TypeConversionError) as context:
            manager._validate_setting_type("iterate", "not_a_number", int)
        
        error = context.exception
        self.assertEqual(error.setting, "iterate")
        self.assertEqual(error.expected_type, int)
        self.assertIn("int", error.suggestion)
    
    def test_type_conversion_success(self):
        """Test successful type conversions."""
        manager = SettingsManager(self.semantic_theory)
        
        # Test various conversions
        self.assertEqual(manager._validate_setting_type("test", "123", int), 123)
        self.assertEqual(manager._validate_setting_type("test", "45.6", float), 45.6)
        self.assertEqual(manager._validate_setting_type("test", "true", bool), True)
        self.assertEqual(manager._validate_setting_type("test", "false", bool), False)
        self.assertEqual(manager._validate_setting_type("test", "yes", bool), True)
        self.assertEqual(manager._validate_setting_type("test", "no", bool), False)
        self.assertEqual(manager._validate_setting_type("test", "1", bool), True)
        self.assertEqual(manager._validate_setting_type("test", "0", bool), False)
        self.assertEqual(manager._validate_setting_type("test", 123, str), "123")
    
    def test_range_error(self):
        """Test RangeError is raised for out-of-range values."""
        manager = SettingsManager(self.semantic_theory)
        
        # Test min violation
        with self.assertRaises(RangeError) as context:
            manager._validate_setting_range("iterate", 0, min_value=1)
        
        error = context.exception
        self.assertEqual(error.setting, "iterate")
        self.assertEqual(error.value, 0)
        self.assertEqual(error.min_value, 1)
        self.assertIn(">= 1", error.suggestion)
        
        # Test max violation
        with self.assertRaises(RangeError) as context:
            manager._validate_setting_range("max_depth", 1000, max_value=100)
        
        error = context.exception
        self.assertEqual(error.setting, "max_depth")
        self.assertEqual(error.value, 1000)
        self.assertEqual(error.max_value, 100)
        self.assertIn("<= 100", error.suggestion)
        
        # Test range violation - value outside both bounds
        with self.assertRaises(RangeError) as context:
            manager._validate_setting_range("timeout", 5000, min_value=1, max_value=3600)
        
        error = context.exception
        self.assertEqual(error.setting, "timeout")
        self.assertIn("<= 3600", error.suggestion)  # Will hit max violation first
    
    def test_range_validation_success(self):
        """Test successful range validations."""
        manager = SettingsManager(self.semantic_theory)
        
        # Should not raise
        manager._validate_setting_range("iterate", 5, min_value=1, max_value=100)
        manager._validate_setting_range("timeout", 300, min_value=1)
        manager._validate_setting_range("max_depth", 10, max_value=1000)
    
    def test_error_str_formatting(self):
        """Test error message formatting."""
        # Test basic error
        error = SettingsError("Basic error message")
        self.assertEqual(str(error), "Basic error message")
        
        # Test error with setting
        error = SettingsError("Value error", setting="my_setting")
        self.assertEqual(str(error), "Setting 'my_setting': Value error")
        
        # Test error with suggestion
        error = SettingsError("Error", suggestion="Try this instead")
        self.assertEqual(str(error), "Error\nSuggestion: Try this instead")
        
        # Test error with both
        error = SettingsError("Error", setting="test", suggestion="Fix it")
        self.assertEqual(str(error), "Setting 'test': Error\nSuggestion: Fix it")
    
    def test_unknown_setting_error_suggestions(self):
        """Test that UnknownSettingError provides helpful suggestions."""
        # Test with similar settings
        error = UnknownSettingError("print_constrains", 
                                   ["print_constraints", "print_impossible", "save_output"])
        self.assertIn("print_constraints", error.suggestion)
        
        # Test with no similar settings
        error = UnknownSettingError("xyz", ["timeout", "iterate", "verbose"])
        self.assertIn("Available settings", error.suggestion)
    
    def test_theory_compatibility_error(self):
        """Test TheoryCompatibilityError formatting."""
        error = TheoryCompatibilityError(
            "maximize",
            "MinimalTheory",
            "This theory doesn't support maximization",
            suggestion="Remove the maximize setting"
        )
        
        self.assertEqual(error.theory_name, "MinimalTheory")
        self.assertEqual(error.reason, "This theory doesn't support maximization")
        self.assertIn("incompatible with MinimalTheory", str(error))
        self.assertIn("Remove the maximize setting", str(error))
    
    def test_missing_required_error(self):
        """Test MissingRequiredError."""
        # Test with default suggestion
        error = MissingRequiredError("formula")
        self.assertIn("Required setting 'formula' is missing", str(error))
        self.assertIn("Add 'formula' to your settings", error.suggestion)
        
        # Test with custom suggestion
        error = MissingRequiredError("api_key", suggestion="Set API_KEY environment variable")
        self.assertIn("Set API_KEY environment variable", error.suggestion)
    
    def test_extracted_method_integration(self):
        """Test that extracted methods work together correctly."""
        manager = SettingsManager(self.semantic_theory)
        
        # Create mock flags object
        mock_flags = MagicMock()
        mock_flags._parsed_args = ["--contingent", "--verbose", "true"]
        mock_flags.contingent = True
        mock_flags.verbose = True
        
        # Test is_mock_object
        self.assertFalse(manager._is_mock_object(mock_flags))
        
        mock_without_parsed = MagicMock(spec=[])
        self.assertTrue(manager._is_mock_object(mock_without_parsed))
        
        # Test extract_user_provided_flags
        flags = manager._extract_user_provided_flags(mock_flags, False)
        self.assertIn("iterate", flags)
        self.assertIn("verbose", flags)
        
        # Test apply_overrides integration
        settings = {"iterate": 1, "verbose": False, "timeout": 300}
        manager._apply_overrides(settings, mock_flags, flags, False)
        self.assertEqual(settings["iterate"], 5)
        self.assertEqual(settings["verbose"], True)
        self.assertEqual(settings["timeout"], 300)  # Unchanged


if __name__ == "__main__":
    unittest.main()