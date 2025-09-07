"""Unit tests for settings validation with parameterization.

This module validates settings dictionaries using parameterized
tests for comprehensive coverage.
"""

import pytest
from tests.utils.assertions import assert_settings_valid


class TestSettingsValidation:
    """Test settings validation with parameterized inputs."""
    
    @pytest.mark.parametrize("n_value,valid", [
        (1, True),
        (2, True),
        (32, True),
        (64, True),
        (0, False),
        (-1, False),
        (65, False),
        (100, False),
        (1.5, False),
        ("2", False),
    ])
    def test_n_value_validation(self, n_value, valid):
        """Test N value validation."""
        settings = {'N': n_value}
        
        if valid:
            assert_settings_valid(settings)
        else:
            with pytest.raises(AssertionError):
                assert_settings_valid(settings)
    
    @pytest.mark.parametrize("max_time,valid", [
        (1, True),
        (10, True),
        (60.5, True),
        (0.1, True),
        (0, False),
        (-1, False),
        (-10.5, False),
        ("10", False),
        (None, False),
    ])
    def test_max_time_validation(self, max_time, valid):
        """Test max_time validation."""
        settings = {'max_time': max_time}
        
        if valid:
            assert_settings_valid(settings)
        else:
            with pytest.raises(AssertionError):
                assert_settings_valid(settings)
    
    @pytest.mark.parametrize("bool_setting", [
        'print_constraints',
        'print_z3',
        'save_output',
        'print_impossible',
        'maximize',
        'contingent',
        'disjoint',
        'non_empty',
        'non_null'
    ])
    @pytest.mark.parametrize("value,valid", [
        (True, True),
        (False, True),
        (1, False),
        (0, False),
        ("true", False),
        ("false", False),
        (None, False),
    ])
    def test_boolean_settings(self, bool_setting, value, valid):
        """Test boolean setting validation."""
        settings = {bool_setting: value}
        
        if valid:
            assert_settings_valid(settings)
        else:
            with pytest.raises(AssertionError):
                assert_settings_valid(settings)
    
    @pytest.mark.parametrize("settings_combo", [
        {'N': 3, 'max_time': 10, 'print_constraints': True},
        {'N': 5, 'contingent': True, 'non_empty': True},
        {'max_time': 30, 'save_output': True, 'print_z3': False},
        {'N': 2, 'disjoint': True, 'non_null': True, 'maximize': False},
    ])
    def test_valid_settings_combinations(self, settings_combo):
        """Test valid combinations of settings."""
        assert_settings_valid(settings_combo)
    
    @pytest.mark.parametrize("settings_combo", [
        {'N': 0, 'max_time': 10},  # Invalid N
        {'N': 3, 'max_time': -5},  # Invalid max_time
        {'print_constraints': "yes"},  # Invalid boolean
        {'N': "three", 'contingent': 1},  # Multiple invalid
    ])
    def test_invalid_settings_combinations(self, settings_combo):
        """Test invalid combinations of settings."""
        with pytest.raises(AssertionError):
            assert_settings_valid(settings_combo)
    
    def test_empty_settings(self):
        """Test that empty settings are valid."""
        assert_settings_valid({})
    
    def test_unknown_settings_ignored(self):
        """Test that unknown settings don't cause validation failure."""
        settings = {
            'N': 3,
            'unknown_setting': 'value',
            'another_unknown': 123
        }
        # Should validate only known settings
        assert_settings_valid(settings)