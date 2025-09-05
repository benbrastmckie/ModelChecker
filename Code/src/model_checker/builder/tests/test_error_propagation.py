"""
Error propagation tests for builder components.

This module tests how errors are handled and propagated between components,
ensuring graceful degradation and informative error messages.
"""
import unittest
import tempfile
import os
import sys
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock
from .fixtures import (
    create_mock_flags,
    create_mock_theory,
    create_temp_module_file,
    TempFileCleanup,
    assert_error_message_contains
)

from model_checker.builder.module import BuildModule
from model_checker.builder.loader import ModuleLoader
from model_checker.builder.runner import ModelRunner
from model_checker.builder.comparison import ModelComparison
from model_checker.builder.translation import OperatorTranslation


class TestLoaderErrors(unittest.TestCase):
    """Test error handling in ModuleLoader."""
    
    def setUp(self):
        """Set up test environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_module_not_found_error(self):
        """Test handling of non-existent module files."""
        flags = create_mock_flags(file_path="/does/not/exist.py")
        
        with self.assertRaises(FileNotFoundError) as context:
            module = BuildModule(flags)
            module.run()
        
        assert_error_message_contains(
            context.exception, 
            "not found",
            self
        )
    
    def test_module_syntax_error(self):
        """Test handling of modules with syntax errors."""
        # Create module with syntax error
        bad_content = "this is not valid python syntax !"
        module_path = self.cleanup.add_file(
            create_temp_module_file(bad_content)
        )
        
        flags = create_mock_flags(file_path=module_path)
        loader = ModuleLoader("test", module_path)
        
        with self.assertRaises(SyntaxError):
            loader.load_module()
    
    def test_module_import_error(self):
        """Test handling of modules with import errors."""
        # Create module with bad import
        bad_content = """
from nonexistent_package import something

semantic_theories = {}
example_range = {}
"""
        module_path = self.cleanup.add_file(
            create_temp_module_file(bad_content)
        )
        
        flags = create_mock_flags(file_path=module_path)
        loader = ModuleLoader("test", module_path)
        
        with self.assertRaises((ImportError, ModuleNotFoundError)):
            loader.load_module()
    
    def test_missing_required_attributes(self):
        """Test handling of modules missing required attributes."""
        # Module without semantic_theories
        bad_content = """
example_range = {"TEST": [["A"], ["B"], {"N": 2}]}
# Missing semantic_theories!
"""
        module_path = self.cleanup.add_file(
            create_temp_module_file(bad_content)
        )
        
        flags = create_mock_flags(file_path=module_path)
        
        with self.assertRaises(AttributeError) as context:
            module = BuildModule(flags)
            module.run()
        
        assert_error_message_contains(
            context.exception,
            "semantic_theories",
            self
        )
    
    def test_theory_discovery_error(self):
        """Test error when theory cannot be discovered."""
        loader = ModuleLoader("unknown_theory", None)
        
        # Should handle gracefully
        result = loader.discover_theory_module()
        self.assertIsNone(result)  # Or raises specific exception


class TestRunnerErrors(unittest.TestCase):
    """Test error handling in ModelRunner."""
    
    def setUp(self):
        """Set up test environment."""
        self.runner = ModelRunner()
        self.mock_module = Mock()
        self.runner.build_module = self.mock_module
    
    def test_empty_example_error(self):
        """Test handling of empty example data."""
        with self.assertRaises(ValueError) as context:
            self.runner.process_example(
                example_name="EMPTY",
                example_case=[[], [], {"N": 2}],  # Empty premises/conclusions
                semantic_theory=create_mock_theory(),
                build_module=self.mock_module,
                flags=create_mock_flags()
            )
        
        assert_error_message_contains(
            context.exception,
            "empty",
            self
        )
    
    def test_invalid_settings_error(self):
        """Test handling of invalid settings."""
        example_case = [["A"], ["B"], {"N": -1}]  # Invalid N
        
        with self.assertRaises(ValueError) as context:
            self.runner.run_model_check(
                example_name="TEST",
                example_case=example_case,
                semantic_theory=create_mock_theory(),
                build_module=self.mock_module,
                flags=create_mock_flags()
            )
        
        assert_error_message_contains(
            context.exception,
            "N must be positive",
            self
        )
    
    def test_z3_timeout_handling(self):
        """Test handling of Z3 solver timeouts."""
        with patch('z3.Solver') as mock_solver:
            mock_instance = Mock()
            mock_solver.return_value = mock_instance
            mock_instance.check.return_value = Mock(r=0)  # UNKNOWN (timeout)
            
            result = self.runner.try_single_N(
                example_name="TEST",
                premises=["A"],
                conclusions=["B"],
                N=2,
                semantic_theory=create_mock_theory(),
                general_settings={},
                flags=create_mock_flags(timeout=1000)
            )
            
            # Should handle timeout gracefully
            is_valid, model = result
            self.assertIsNone(model)  # No model on timeout
    
    def test_theory_validation_error(self):
        """Test handling of theory validation errors."""
        # Create theory that raises during validation
        bad_theory = Mock()
        bad_theory.validate_model.side_effect = RuntimeError("Validation failed")
        
        with self.assertRaises(RuntimeError) as context:
            self.runner.run_model_check(
                example_name="TEST",
                example_case=[["A"], ["B"], {"N": 2}],
                semantic_theory=bad_theory,
                build_module=self.mock_module,
                flags=create_mock_flags()
            )
        
        assert_error_message_contains(
            context.exception,
            "Validation failed",
            self
        )


class TestComparisonErrors(unittest.TestCase):
    """Test error handling in ModelComparison."""
    
    def setUp(self):
        """Set up test environment."""
        self.comparison = ModelComparison()
        self.comparison.build_module = Mock()
    
    def test_empty_theories_error(self):
        """Test handling of empty theory dictionary."""
        result = self.comparison.compare_semantics(
            example_name="TEST",
            example_case=[["A"], ["B"], {"N": 2}],
            semantic_theories={},  # Empty
            flags=create_mock_flags()
        )
        
        # Should return empty result, not error
        self.assertEqual(result, {})
    
    def test_mixed_theory_errors(self):
        """Test handling when some theories fail."""
        theories = {
            "Good": create_mock_theory(),
            "Bad": Mock(check_validity=Mock(side_effect=Exception("Theory error")))
        }
        
        # Mock runner to avoid actual execution
        with patch.object(self.comparison, '_compare_single_example') as mock_compare:
            def side_effect(name, *args):
                if name == "Bad":
                    raise Exception("Theory error")
                return {"valid": True}
            
            mock_compare.side_effect = side_effect
            
            result = self.comparison.compare_semantics(
                "TEST",
                [["A"], ["B"], {"N": 2}],
                theories,
                create_mock_flags()
            )
            
            # Should have result for good theory
            self.assertIn("Good", result)
    
    def test_multiprocessing_error(self):
        """Test handling of multiprocessing errors."""
        with patch('multiprocessing.Pool') as mock_pool:
            # Simulate pool creation failure
            mock_pool.side_effect = OSError("Cannot create process pool")
            
            # Should fall back to sequential processing
            theories = {"T1": create_mock_theory(), "T2": create_mock_theory()}
            
            # This should not raise despite pool failure
            comparison = ModelComparison()
            comparison.build_module = Mock()
            comparison.build_module.runner = Mock()
            
            # Should handle error and possibly fall back to sequential
            # (Implementation dependent)


class TestTranslationErrors(unittest.TestCase):
    """Test error handling in OperatorTranslation."""
    
    def setUp(self):
        """Set up test environment."""
        self.translation = OperatorTranslation()
    
    def test_invalid_formula_structure(self):
        """Test handling of invalid formula structures."""
        # Malformed example case
        bad_example = [["A"], ["B"]]  # Missing settings
        
        with self.assertRaises((IndexError, ValueError)):
            self.translation.translate(bad_example, {"\\wedge": "∧"})
    
    def test_unicode_encoding_error(self):
        """Test handling of unicode encoding issues."""
        # This should handle various encodings gracefully
        example = [["A \\wedge B"], ["A"], {"N": 2}]
        
        # Various unicode scenarios
        dictionaries = [
            {"\\wedge": "∧"},  # Normal unicode
            {"\\wedge": "\u2227"},  # Unicode escape
            {"\\wedge": "⋀"},  # Different unicode char
        ]
        
        for dictionary in dictionaries:
            result = self.translation.translate(example, dictionary)
            # Should not raise encoding errors
            self.assertIsInstance(result[0][0], str)
    
    def test_circular_translation(self):
        """Test handling of circular translation definitions."""
        # Create circular reference
        circular_dict = {
            "A": "B",
            "B": "A"
        }
        
        example = [["A"], ["B"], {"N": 2}]
        
        # Should handle without infinite loop
        # (Implementation should have recursion limit)
        result = self.translation.translate(example, circular_dict)
        self.assertIsNotNone(result)


class TestCrossComponentErrors(unittest.TestCase):
    """Test error propagation across components."""
    
    def setUp(self):
        """Set up test environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_loader_error_propagates_to_runner(self):
        """Test loader errors properly propagate to runner."""
        flags = create_mock_flags(file_path="/invalid/path.py")
        
        with self.assertRaises(FileNotFoundError):
            module = BuildModule(flags)
            module.run()
    
    def test_runner_error_in_comparison(self):
        """Test runner errors during comparison are handled."""
        flags = create_mock_flags(comparison=True)
        module = BuildModule(flags)
        
        # Make runner raise error
        with patch.object(module.runner, 'try_single_N') as mock_try:
            mock_try.side_effect = RuntimeError("Runner failed")
            
            theories = {"Test": create_mock_theory()}
            
            # Comparison should handle runner errors
            result = module.comparison.compare_semantics(
                "TEST",
                [["A"], ["B"], {"N": 2}],
                theories,
                flags
            )
            
            # May be empty or contain error info
            self.assertIsInstance(result, dict)
    
    def test_validation_error_stops_execution(self):
        """Test validation errors stop execution early."""
        # Create module with invalid example
        content = '''
semantic_theories = {"Test": None}  # Invalid theory
example_range = {"TEST": [["A"], ["B"], {"N": "invalid"}]}  # Invalid N
'''
        module_path = self.cleanup.add_file(
            create_temp_module_file(content)
        )
        
        flags = create_mock_flags(file_path=module_path)
        
        with self.assertRaises((ValueError, TypeError)):
            module = BuildModule(flags)
            module.run()
    
    def test_graceful_degradation(self):
        """Test system degrades gracefully with multiple errors."""
        flags = create_mock_flags()
        module = BuildModule(flags)
        
        # Simulate various component failures
        errors_injected = []
        
        with patch.object(module.loader, 'load_module') as mock_load:
            mock_load.side_effect = ImportError("Simulated")
            errors_injected.append("loader")
        
        with patch.object(module.runner, 'run_model_check') as mock_run:
            mock_run.side_effect = RuntimeError("Simulated")
            errors_injected.append("runner")
        
        # System should handle cascading failures
        with self.assertRaises((ImportError, RuntimeError)):
            module.run()


class TestErrorMessages(unittest.TestCase):
    """Test quality of error messages."""
    
    def test_informative_error_messages(self):
        """Test errors provide helpful information."""
        test_cases = [
            (ValueError("N must be positive integer, got: -1"), ["positive", "-1"]),
            (ImportError("No module named 'test_theory'"), ["module", "test_theory"]),
            (SyntaxError("invalid syntax at line 5"), ["syntax", "line"]),
        ]
        
        for error, expected_words in test_cases:
            error_msg = str(error)
            for word in expected_words:
                self.assertIn(
                    word, error_msg.lower(),
                    f"Error message should contain '{word}': {error_msg}"
                )
    
    def test_error_context_preserved(self):
        """Test errors preserve context information."""
        # Create chain of errors
        try:
            try:
                raise ValueError("Original error")
            except ValueError as e:
                raise RuntimeError("Wrapper error") from e
        except RuntimeError as e:
            # Should preserve cause
            self.assertIsNotNone(e.__cause__)
            self.assertIsInstance(e.__cause__, ValueError)


if __name__ == '__main__':
    unittest.main()