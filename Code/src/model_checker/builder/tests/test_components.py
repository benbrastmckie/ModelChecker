"""
Consolidated component tests for builder package.

This module combines tests for all extracted components (runner, comparison, translation)
to ensure they work correctly both individually and through BuildModule delegation.
"""
import unittest
import tempfile
import os
from unittest.mock import Mock, patch, MagicMock
from .fixtures import (
    create_mock_flags, 
    create_mock_theory, 
    create_mock_module,
    create_temp_module_file,
    TempFileCleanup,
    VALID_FORMULAS,
    EXAMPLE_MODULE_CONTENT
)

from model_checker.builder.module import BuildModule
from model_checker.builder.runner import ModelRunner
from model_checker.builder.comparison import ModelComparison  
from model_checker.builder.translation import OperatorTranslation


class TestComponentsBase(unittest.TestCase):
    """Base class with common setup for component tests."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create mock flags
        self.flags = create_mock_flags()
        
        # Create test module file
        self.module_path = self.cleanup.add_file(
            create_temp_module_file(EXAMPLE_MODULE_CONTENT)
        )
        self.flags.file_path = self.module_path


class TestRunnerComponent(TestComponentsBase):
    """Test ModelRunner component functionality."""
    
    def test_runner_initialization(self):
        """Test ModelRunner can be initialized."""
        runner = ModelRunner()
        self.assertIsNotNone(runner)
    
    def test_runner_has_required_methods(self):
        """Test ModelRunner has all required methods."""
        runner = ModelRunner()
        required_methods = [
            'run_model_check',
            'try_single_N', 
            'process_example',
            'process_iterations'
        ]
        for method in required_methods:
            self.assertTrue(
                hasattr(runner, method),
                f"ModelRunner missing required method: {method}"
            )
    
    @patch('model_checker.builder.runner.BuildModule')
    def test_run_model_check_basic(self, mock_build_module):
        """Test basic model checking functionality."""
        runner = ModelRunner()
        
        # Configure mock
        mock_module = create_mock_module()
        mock_build_module.return_value = mock_build_module
        mock_build_module.loaded_module = mock_module
        
        # Run model check
        result = runner.run_model_check(
            example_name="TEST",
            example_case=[["A"], ["B"], {"N": 2}],
            semantic_theory=create_mock_theory(),
            build_module=mock_build_module,
            flags=self.flags
        )
        
        # Verify result structure
        self.assertIsInstance(result, dict)
        self.assertIn('example', result)
        self.assertIn('status', result)
    
    def test_runner_delegation_from_build_module(self):
        """Test runner methods work through BuildModule delegation."""
        module = BuildModule(self.flags)
        
        # Test delegation exists
        self.assertTrue(hasattr(module, 'runner'))
        self.assertIsInstance(module.runner, ModelRunner)
        
        # Test delegated methods
        self.assertTrue(hasattr(module.runner, 'run_model_check'))
        self.assertTrue(hasattr(module.runner, 'process_example'))


class TestComparisonComponent(TestComponentsBase):
    """Test ModelComparison component functionality."""
    
    def test_comparison_initialization(self):
        """Test ModelComparison can be initialized."""
        comparison = ModelComparison()
        self.assertIsNotNone(comparison)
    
    def test_comparison_has_required_methods(self):
        """Test ModelComparison has all required methods."""
        comparison = ModelComparison()
        required_methods = [
            'compare_semantics',
            'run_comparison',
            '_find_max_N',
            '_compare_single_example'
        ]
        for method in required_methods:
            self.assertTrue(
                hasattr(comparison, method),
                f"ModelComparison missing required method: {method}"
            )
    
    def test_compare_semantics_basic(self):
        """Test basic semantic comparison."""
        comparison = ModelComparison()
        
        # Create test data
        theories = {
            "Theory1": create_mock_theory(),
            "Theory2": create_mock_theory()
        }
        example_case = [["A"], ["B"], {"N": 2}]
        
        # Run comparison
        result = comparison.compare_semantics(
            example_name="TEST",
            example_case=example_case,
            semantic_theories=theories,
            flags=self.flags
        )
        
        # Verify result structure
        self.assertIsInstance(result, dict)
        self.assertIn("Theory1", result)
        self.assertIn("Theory2", result)
    
    def test_comparison_delegation_from_build_module(self):
        """Test comparison methods work through BuildModule delegation."""
        module = BuildModule(self.flags)
        
        # Test delegation exists
        self.assertTrue(hasattr(module, 'comparison'))
        self.assertIsInstance(module.comparison, ModelComparison)
        
        # Test delegated methods
        self.assertTrue(hasattr(module.comparison, 'compare_semantics'))
        self.assertTrue(hasattr(module.comparison, 'run_comparison'))
    
    def test_backward_compatible_delegation(self):
        """Test BuildModule provides backward-compatible delegation."""
        module = BuildModule(self.flags)
        
        # These methods should be delegated for backward compatibility
        self.assertTrue(hasattr(module, 'compare_semantics'))
        self.assertTrue(hasattr(module, 'run_comparison'))


class TestTranslationComponent(TestComponentsBase):
    """Test OperatorTranslation component functionality."""
    
    def test_translation_initialization(self):
        """Test OperatorTranslation can be initialized."""
        translation = OperatorTranslation()
        self.assertIsNotNone(translation)
    
    def test_translation_has_required_methods(self):
        """Test OperatorTranslation has all required methods."""
        translation = OperatorTranslation()
        required_methods = [
            'translate',
            'translate_formula', 
            'translate_example'
        ]
        for method in required_methods:
            self.assertTrue(
                hasattr(translation, method),
                f"OperatorTranslation missing required method: {method}"
            )
    
    def test_translate_basic(self):
        """Test basic translation functionality."""
        translation = OperatorTranslation()
        
        # Test data
        example_case = [
            ["A \\wedge B"],  # premises
            ["A"],  # conclusions
            {"N": 2}  # settings
        ]
        
        dictionary = {
            "\\wedge": "∧",
            "\\vee": "∨",
            "\\rightarrow": "→"
        }
        
        # Run translation
        result = translation.translate(example_case, dictionary)
        
        # Verify translation
        self.assertIsInstance(result, list)
        self.assertEqual(len(result), 3)
        self.assertIn("∧", result[0][0])
    
    def test_translation_delegation_from_build_module(self):
        """Test translation methods work through BuildModule delegation."""
        module = BuildModule(self.flags)
        
        # Test delegation exists
        self.assertTrue(hasattr(module, 'translation'))
        self.assertIsInstance(module.translation, OperatorTranslation)
        
        # Test delegated methods
        self.assertTrue(hasattr(module.translation, 'translate'))
        self.assertTrue(hasattr(module.translation, 'translate_example'))
    
    def test_backward_compatible_delegation(self):
        """Test BuildModule provides backward-compatible delegation."""
        module = BuildModule(self.flags)
        
        # These methods should be delegated for backward compatibility
        self.assertTrue(hasattr(module, 'translate'))
        self.assertTrue(hasattr(module, 'translate_example'))


class TestComponentInteractions(TestComponentsBase):
    """Test interactions between components."""
    
    def test_all_components_initialized(self):
        """Test BuildModule initializes all components."""
        module = BuildModule(self.flags)
        
        # Verify all components exist
        self.assertTrue(hasattr(module, 'runner'))
        self.assertTrue(hasattr(module, 'comparison'))
        self.assertTrue(hasattr(module, 'translation'))
        self.assertTrue(hasattr(module, 'loader'))
        
        # Verify types
        self.assertIsInstance(module.runner, ModelRunner)
        self.assertIsInstance(module.comparison, ModelComparison)
        self.assertIsInstance(module.translation, OperatorTranslation)
    
    def test_components_share_references(self):
        """Test components can access shared resources through BuildModule."""
        module = BuildModule(self.flags)
        
        # Components should have reference to parent module
        self.assertEqual(module.runner.build_module, module)
        self.assertEqual(module.comparison.build_module, module)
        self.assertEqual(module.translation.build_module, module)
    
    @patch('model_checker.builder.loader.ModuleLoader.load_module')
    def test_runner_comparison_workflow(self, mock_load):
        """Test workflow involving both runner and comparison."""
        # Setup
        mock_module = create_mock_module()
        mock_load.return_value = mock_module
        
        flags = create_mock_flags(comparison=True)
        module = BuildModule(flags)
        
        # This should trigger comparison workflow
        with patch.object(module.comparison, 'run_comparison') as mock_comp:
            module.run()
            mock_comp.assert_called_once()
    
    def test_translation_in_runner_workflow(self):
        """Test translation is available during runner workflow."""
        module = BuildModule(self.flags)
        
        # Runner should be able to access translation
        self.assertTrue(
            hasattr(module.runner, 'build_module'),
            "Runner should have reference to BuildModule"
        )
        
        # Through build_module, runner can access translation
        self.assertIsInstance(
            module.runner.build_module.translation,
            OperatorTranslation
        )


class TestComponentEdgeCases(TestComponentsBase):
    """Test edge cases and error handling in components."""
    
    def test_runner_handles_empty_example(self):
        """Test runner handles empty example gracefully."""
        runner = ModelRunner()
        
        with self.assertRaises(ValueError) as context:
            runner.process_example(
                example_name="EMPTY",
                example_case=[[], [], {}],
                semantic_theory=create_mock_theory(),
                build_module=Mock(),
                flags=self.flags
            )
        
        self.assertIn("empty", str(context.exception).lower())
    
    def test_comparison_handles_no_theories(self):
        """Test comparison handles no theories gracefully."""
        comparison = ModelComparison()
        
        result = comparison.compare_semantics(
            example_name="TEST",
            example_case=[["A"], ["B"], {"N": 2}],
            semantic_theories={},  # No theories
            flags=self.flags
        )
        
        self.assertEqual(result, {})
    
    def test_translation_handles_no_operators(self):
        """Test translation handles empty dictionary."""
        translation = OperatorTranslation()
        
        example = [["A \\wedge B"], ["A"], {"N": 2}]
        result = translation.translate(example, {})  # Empty dictionary
        
        # Should return unchanged
        self.assertEqual(result[0][0], "A \\wedge B")
    
    def test_components_handle_none_flags(self):
        """Test components handle None flags gracefully."""
        # Components should provide defaults
        runner = ModelRunner()
        comparison = ModelComparison()
        translation = OperatorTranslation()
        
        # Should not raise exceptions
        self.assertIsNotNone(runner)
        self.assertIsNotNone(comparison)
        self.assertIsNotNone(translation)


if __name__ == '__main__':
    unittest.main()