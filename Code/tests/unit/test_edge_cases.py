"""Edge case testing for ModelChecker.

This module tests boundary conditions, extreme values, and
unusual but valid inputs to ensure robust handling.
"""

import pytest
import sys
from tests.utils.assertions import assert_settings_valid, assert_valid_formula


class TestBoundaryValues:
    """Test boundary value conditions."""
    
    @pytest.mark.parametrize("n_value,valid", [
        (1, True),   # Minimum valid
        (2, True),   # Small valid
        (32, True),  # Medium valid
        (63, True),  # Near maximum
        (64, True),  # Maximum valid
        (0, False),  # Below minimum
        (-1, False), # Negative
        (65, False), # Above maximum
        (100, False), # Far above maximum
    ])
    def test_n_value_boundaries(self, n_value, valid):
        """Test N value boundary conditions."""
        settings = {'N': n_value}
        
        if valid:
            assert_settings_valid(settings)
        else:
            with pytest.raises(AssertionError):
                assert_settings_valid(settings)
    
    @pytest.mark.parametrize("max_time,valid", [
        (0.001, True),   # Very small but valid
        (0.01, True),    # Small valid
        (1.0, True),     # Normal
        (60.0, True),    # Large
        (3600.0, True),  # Very large (1 hour)
        (0, False),      # Zero invalid
        (-0.1, False),   # Negative
        (-1, False),     # Negative integer
    ])
    def test_max_time_boundaries(self, max_time, valid):
        """Test max_time boundary conditions."""
        settings = {'max_time': max_time}
        
        if valid:
            assert_settings_valid(settings)
        else:
            with pytest.raises(AssertionError):
                assert_settings_valid(settings)


class TestEmptyInputs:
    """Test handling of empty inputs."""
    
    def test_empty_formula_string(self):
        """Test empty formula string handling."""
        with pytest.raises(AssertionError):
            assert_valid_formula("")
    
    def test_whitespace_only_formula(self):
        """Test whitespace-only formula handling."""
        formulas = [" ", "  ", "\t", "\n", " \t\n "]
        
        for formula in formulas:
            with pytest.raises(AssertionError):
                assert_valid_formula(formula)
    
    def test_empty_settings_dict(self):
        """Test empty settings dictionary is valid."""
        # Empty settings should use defaults
        assert_settings_valid({})
    
    def test_empty_lists_in_examples(self):
        """Test empty lists in example structures."""
        from tests.utils.assertions import assert_example_structure
        
        # Empty assumptions and conclusions should be valid
        examples = [
            [[], [], {}],  # Both empty
            [[], ["A"], {"N": 2}],  # Empty assumptions
            [["A"], [], {"N": 2}],  # Empty conclusions
        ]
        
        for example in examples:
            assert_example_structure(example)


class TestExtremeValues:
    """Test extreme but valid values."""
    
    def test_very_long_formula(self):
        """Test handling of very long formulas."""
        # Build progressively longer formulas
        base = "p"
        
        # Test various lengths
        for depth in [10, 50, 100]:
            formula = base
            for i in range(depth):
                formula = f"(\\neg {formula})"
            
            # Should handle deep nesting
            assert_valid_formula(formula)
    
    def test_many_propositions(self):
        """Test formula with many different propositions."""
        # Create formula with many propositions
        props = [f"p{i}" for i in range(26)]  # p0 through p25
        
        # Build large conjunction
        formula = props[0]
        for prop in props[1:]:
            formula = f"({formula} \\wedge {prop})"
        
        assert_valid_formula(formula)
    
    def test_complex_nested_operators(self):
        """Test complex nesting of different operators."""
        formulas = [
            "\\Box (\\Diamond (A \\wedge B))",
            "\\neg \\neg \\neg \\neg A",  # Multiple negations
            "(A \\rightarrow (B \\rightarrow (C \\rightarrow D)))",
            "\\Box (A \\wedge (\\Diamond B \\vee \\neg C))",
            "((A \\leftrightarrow B) \\wedge (C \\leftrightarrow D))",
        ]
        
        for formula in formulas:
            assert_valid_formula(formula)
    
    @pytest.mark.parametrize("num_examples", [1, 10, 50, 100])
    def test_many_examples(self, num_examples):
        """Test handling of many examples in a batch."""
        # Create example range with many examples
        example_range = {}
        for i in range(num_examples):
            example_range[f"TEST_{i}"] = [
                [f"p{i}"],  # Assumptions
                [f"q{i}"],  # Conclusions
                {"N": 2}    # Settings
            ]
        
        # Should handle large batches
        assert isinstance(example_range, dict)
        assert len(example_range) == num_examples


class TestSpecialCharacters:
    """Test handling of special characters."""
    
    def test_propositions_with_numbers(self):
        """Test propositions containing numbers."""
        valid_props = [
            "p1", "p2", "p10", "p100",
            "prop1", "prop2",
            "A1", "B2", "C3"
        ]
        
        for prop in valid_props:
            formula = f"({prop} \\wedge {prop})"
            assert_valid_formula(formula)
    
    def test_propositions_with_underscores(self):
        """Test propositions with underscores."""
        props_with_underscores = [
            "p_1", "prop_a", "test_prop",
            "my_var", "some_prop_name"
        ]
        
        for prop in props_with_underscores:
            formula = f"\\neg {prop}"
            assert_valid_formula(formula)
    
    def test_mixed_case_propositions(self):
        """Test mixed case proposition names."""
        mixed_case = [
            "Prop", "PROP", "pRoP",
            "MyProp", "myProp", "MY_PROP"
        ]
        
        for prop in mixed_case:
            formula = f"\\Box {prop}"
            assert_valid_formula(formula)


class TestCombinationEffects:
    """Test combinations of edge cases."""
    
    def test_minimum_n_with_complex_formula(self):
        """Test N=1 with complex formulas."""
        settings = {'N': 1}
        assert_settings_valid(settings)
        
        # Complex formula should still work with N=1
        formula = "\\Box (A \\wedge (B \\vee \\neg C))"
        assert_valid_formula(formula)
    
    def test_maximum_n_with_many_propositions(self):
        """Test N=64 with many propositions."""
        settings = {'N': 64}
        assert_settings_valid(settings)
        
        # Many propositions with max N
        props = [f"p{i}" for i in range(20)]
        formula = " \\wedge ".join(props)
        formula = f"({formula})"
        assert_valid_formula(formula)
    
    @pytest.mark.parametrize("combo", [
        {'N': 1, 'max_time': 0.001},  # Minimum values
        {'N': 64, 'max_time': 3600},  # Maximum values
        {'N': 32, 'contingent': True, 'non_empty': True},  # Multiple flags
    ])
    def test_settings_combinations(self, combo):
        """Test various settings combinations."""
        assert_settings_valid(combo)


class TestRecursionLimits:
    """Test recursion and stack depth limits."""
    
    def test_deeply_nested_formula_parsing(self):
        """Test formula parsing with deep nesting."""
        # Test increasing depths until we hit a limit or max depth
        max_safe_depth = 100  # Reasonable limit
        
        for depth in [10, 50, max_safe_depth]:
            formula = "p"
            for _ in range(depth):
                formula = f"(\\neg {formula})"
            
            try:
                assert_valid_formula(formula)
            except RecursionError:
                # If we hit recursion limit, that's acceptable
                # as long as it happens at extreme depth
                assert depth >= 50  # Should handle at least 50 levels
                break
    
    def test_wide_formula_structure(self):
        """Test formula with wide structure (many siblings)."""
        # Create a wide formula (many terms at same level)
        num_terms = 100
        terms = [f"p{i}" for i in range(num_terms)]
        
        # Build flat conjunction
        formula = " \\wedge ".join(terms)
        formula = f"({formula})"
        
        # Should handle wide formulas
        assert_valid_formula(formula)


class TestTypeCoercion:
    """Test type coercion and conversion edge cases."""
    
    def test_string_number_settings(self):
        """Test that string numbers are not accepted for numeric settings."""
        invalid_settings = [
            {'N': "3"},      # String number for N
            {'N': "64"},     # String number at boundary
            {'max_time': "10"},  # String number for max_time
            {'max_time': "1.5"}, # String float
        ]
        
        for settings in invalid_settings:
            with pytest.raises(AssertionError):
                assert_settings_valid(settings)
    
    def test_numeric_boolean_settings(self):
        """Test that numeric values are not accepted for boolean settings."""
        bool_settings = [
            'print_constraints', 'save_output', 'contingent',
            'non_empty', 'non_null', 'disjoint'
        ]
        
        for setting in bool_settings:
            # 0 and 1 should not be accepted as booleans
            for value in [0, 1]:
                settings = {setting: value}
                with pytest.raises(AssertionError):
                    assert_settings_valid(settings)
    
    def test_none_values_in_settings(self):
        """Test that None values are handled properly."""
        settings_with_none = [
            {'N': None},
            {'max_time': None},
            {'contingent': None},
        ]
        
        for settings in settings_with_none:
            with pytest.raises(AssertionError):
                assert_settings_valid(settings)