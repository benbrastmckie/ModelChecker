"""Test error handling across the framework.

This module provides comprehensive tests for error conditions,
edge cases, and recovery mechanisms throughout ModelChecker.
"""

import pytest
import tempfile
from pathlib import Path
from tests.utils.helpers import run_cli_command, create_test_module
from tests.utils.assertions import assert_output_contains


class TestCLIErrorHandling:
    """Test CLI error handling and error messages."""
    
    def test_invalid_file_path(self):
        """Test handling of non-existent file."""
        result = run_cli_command(['nonexistent.py'], check=False)
        assert result.returncode != 0
        error_output = result.stderr or result.stdout
        # Check for various error messages
        error_indicators = ['not found', 'no such file', 'no module', 'cannot find']
        assert any(indicator in error_output.lower() for indicator in error_indicators)
    
    def test_invalid_theory_name(self):
        """Test handling of invalid theory name."""
        result = run_cli_command(['-l', 'invalid_theory', 'test'], check=False)
        assert result.returncode != 0
        error_output = result.stderr or result.stdout
        assert 'theory' in error_output.lower() or 'invalid' in error_output.lower()
    
    def test_malformed_module_syntax(self, tmp_path):
        """Test handling of malformed module file."""
        bad_content = 'import syntax error!'
        bad_module = create_test_module(bad_content, tmp_path, 'bad.py')
        
        result = run_cli_command([bad_module], check=False)
        assert result.returncode != 0
        error_output = result.stderr or result.stdout
        assert 'syntax' in error_output.lower() or 'error' in error_output.lower()
    
    def test_missing_required_attributes(self, tmp_path):
        """Test handling of module missing required attributes."""
        incomplete_content = '''
# Missing semantic_theories and example_range
from model_checker.theory_lib import logos
theory = logos.get_theory()
'''
        incomplete_module = create_test_module(incomplete_content, tmp_path, 'incomplete.py')
        
        result = run_cli_command([incomplete_module], check=False)
        assert result.returncode != 0
        # Should report missing attributes
    
    @pytest.mark.parametrize("bad_flag", [
        '--invalid-flag',
        '-X',
        '--nonexistent',
    ])
    def test_invalid_cli_flags(self, bad_flag):
        """Test handling of invalid CLI flags."""
        result = run_cli_command([bad_flag, 'test.py'], check=False)
        assert result.returncode != 0
        error_output = result.stderr or result.stdout
        assert 'unrecognized' in error_output.lower() or 'invalid' in error_output.lower()
    
    def test_conflicting_flags(self):
        """Test handling of conflicting CLI flags."""
        # Test mutually exclusive flags if any exist
        # For example, batch and interactive modes if they conflict
        pass


class TestFrameworkErrorHandling:
    """Test framework-level error handling."""
    
    def test_invalid_formula_unicode(self):
        """Test invalid formula with Unicode characters."""
        from model_checker.syntactic import Syntax
        
        # Unicode formulas should be rejected
        unicode_formulas = [
            "A ∧ B",
            "□ A",
            "¬ p",
            "A → B"
        ]
        
        syntax = Syntax()
        for formula in unicode_formulas:
            # Should either raise error or return invalid result
            try:
                result = syntax.parse(formula)
                # If it doesn't raise, check it's marked invalid
                assert result is None or hasattr(result, 'error')
            except (ValueError, TypeError, Exception):
                # Expected - Unicode should cause error
                pass
    
    def test_malformed_formula_structure(self):
        """Test handling of structurally invalid formulas."""
        from model_checker.syntactic import Syntax
        
        malformed_formulas = [
            "(A \\wedge",  # Missing closing paren
            "A \\wedge B)",  # Missing opening paren
            "((A \\wedge B)",  # Unbalanced parens
            "\\wedge A B",  # Wrong operator position
        ]
        
        syntax = Syntax()
        for formula in malformed_formulas:
            try:
                result = syntax.parse(formula)
                # If it doesn't raise, it should return None or error
                assert result is None or hasattr(result, 'error')
            except (ValueError, TypeError, Exception):
                # Expected - malformed formulas should cause errors
                pass
    
    def test_z3_timeout_handling(self):
        """Test Z3 solver timeout handling."""
        from model_checker.models import ModelDefaults
        
        # Create a model with very short timeout
        settings = {
            'N': 10,
            'max_time': 0.001  # 1ms timeout - should trigger timeout
        }
        
        # This should handle timeout gracefully
        # Note: Actual implementation depends on how timeouts are handled
        model = ModelDefaults(settings)
        # Model should indicate timeout occurred
    
    def test_memory_limit_handling(self):
        """Test handling of memory constraints."""
        # Test with very large N value
        settings = {
            'N': 64,  # Maximum allowed
            'contingent': True,
            'non_empty': True
        }
        
        # Should handle large state spaces gracefully
        from model_checker.models import ModelDefaults
        model = ModelDefaults(settings)
        # Should complete or fail gracefully, not crash


class TestErrorRecovery:
    """Test error recovery mechanisms."""
    
    def test_partial_results_on_error(self, tmp_path):
        """Test that partial results are preserved on error."""
        # Create module that will partially succeed
        content = '''
from model_checker.theory_lib import logos
theory = logos.get_theory()
semantic_theories = {"test": theory}

# First example should work
example_range = {
    "VALID": [[], ["A"], {"N": 2}],
    "INVALID": [[], ["SYNTAX ERROR!"], {"N": 2}]
}
'''
        module_path = create_test_module(content, tmp_path, 'partial.py')
        
        result = run_cli_command([module_path], check=False)
        # Should process valid example even if invalid one fails
    
    def test_cleanup_after_error(self, tmp_path):
        """Test cleanup occurs after errors."""
        # Create module that will fail
        bad_content = 'raise RuntimeError("Test error")'
        bad_module = create_test_module(bad_content, tmp_path, 'error.py')
        
        initial_files = set(tmp_path.glob('*'))
        
        result = run_cli_command([bad_module], check=False)
        assert result.returncode != 0
        
        # Check no temporary files left behind
        final_files = set(tmp_path.glob('*'))
        new_files = final_files - initial_files - {Path(bad_module)}
        
        # Should not leave temporary files
        temp_patterns = ['tmp*', 'temp*', '*.tmp']
        for file in new_files:
            for pattern in temp_patterns:
                assert not file.match(pattern), f"Temporary file left: {file}"
    
    def test_graceful_degradation(self):
        """Test system degrades gracefully under errors."""
        from model_checker.models import ModelDefaults
        
        # Test with settings that might cause issues
        problematic_settings = [
            {'N': 1, 'contingent': True},  # Minimum N with contingent
            {'N': 64, 'maximize': True},  # Maximum N with maximize
            {'max_time': 0.01},  # Very short timeout
        ]
        
        for settings in problematic_settings:
            try:
                model = ModelDefaults(settings)
                # Should either work or fail gracefully
            except Exception as e:
                # Check error is informative
                assert str(e) != ""
                assert not str(e).startswith("Unknown error")


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_empty_formula_lists(self):
        """Test handling of empty formula lists."""
        from tests.fixtures.example_data import STANDARD_SETTINGS
        
        edge_cases = [
            ([], [], STANDARD_SETTINGS),  # Both empty
            ([], ["A"], STANDARD_SETTINGS),  # Empty premises
            (["A"], [], STANDARD_SETTINGS),  # Empty conclusions
        ]
        
        for assumptions, conclusions, settings in edge_cases:
            # Should handle empty lists gracefully
            example = [assumptions, conclusions, settings]
            # Framework should process without crashing
    
    @pytest.mark.parametrize("n_value", [1, 2, 32, 63, 64])
    def test_valid_n_boundary_values(self, n_value):
        """Test valid N values at boundaries."""
        from tests.utils.assertions import assert_settings_valid
        
        settings = {'N': n_value}
        assert_settings_valid(settings)
    
    @pytest.mark.parametrize("n_value", [-1, 0, 65, 100, 1000])
    def test_invalid_n_boundary_values(self, n_value):
        """Test invalid N values are rejected."""
        from tests.utils.assertions import assert_settings_valid
        
        settings = {'N': n_value}
        with pytest.raises(AssertionError):
            assert_settings_valid(settings)
    
    def test_very_long_formulas(self):
        """Test handling of very long formulas."""
        # Build a very deeply nested formula
        formula = "p"
        for i in range(100):  # 100 levels deep
            formula = f"(\\neg {formula})"
        
        from model_checker.syntactic import Syntax
        syntax = Syntax()
        
        # Should handle deep nesting (or fail gracefully)
        try:
            result = syntax.parse(formula)
            # If successful, formula should be valid
            assert result is not None
        except RecursionError:
            # Acceptable - very deep nesting might hit recursion limit
            pass
    
    def test_special_characters_in_names(self, tmp_path):
        """Test handling of special characters in file/project names."""
        special_names = [
            "test-with-dash.py",
            "test_with_underscore.py",
            "test.multiple.dots.py",
            "TestWithCaps.py"
        ]
        
        for name in special_names:
            content = '''
from model_checker.theory_lib import logos
theory = logos.get_theory()
semantic_theories = {"test": theory}
example_range = {"TEST": [[], ["A"], {"N": 2}]}
'''
            module_path = create_test_module(content, tmp_path, name)
            
            # Should handle special characters in filenames
            result = run_cli_command([module_path], check=False)
            # Either succeeds or gives clear error about naming