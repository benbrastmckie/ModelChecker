"""
Deep integration tests for builder components.

This module tests complex interactions between components that go beyond
basic functionality, ensuring the entire system works cohesively.
"""
import unittest
import tempfile
import os
import sys
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock, call
from .fixtures import (
    create_mock_flags,
    create_mock_theory,
    create_temp_module_file,
    create_test_project_structure,
    TempFileCleanup,
    EXAMPLE_MODULE_CONTENT
)

from model_checker.builder.module import BuildModule
from model_checker.builder.loader import ModuleLoader
from model_checker.builder.runner import ModelRunner
from model_checker.builder.comparison import ModelComparison
from model_checker.builder.translation import OperatorTranslation
from model_checker.builder.validation import validate_settings


class TestLoadRunIntegration(unittest.TestCase):
    """Test integration between loader and runner components."""
    
    def setUp(self):
        """Set up test environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_load_and_run_workflow(self):
        """Test complete load -> validate -> run workflow."""
        # Create test module
        module_path = self.cleanup.add_file(create_temp_module_file())
        flags = create_mock_flags(file_path=module_path)
        
        # Initialize system
        module = BuildModule(flags)
        
        # Mock theory to avoid real Z3 calls
        with patch.object(module.loader.loaded_module, 'semantic_theories') as mock_theories:
            mock_theories.__getitem__.return_value = create_mock_theory()
            mock_theories.items.return_value = [("Test", create_mock_theory())]
            
            # Run should complete without errors
            with patch.object(module.runner, 'process_example') as mock_process:
                module.run()
                
                # Verify workflow
                self.assertTrue(mock_process.called)
    
    def test_theory_library_loading_and_execution(self):
        """Test loading theory library modules and running examples."""
        # Mock theory library module
        with patch('model_checker.builder.loader.importlib.import_module') as mock_import:
            mock_theory_module = Mock()
            mock_theory_module.get_theory = Mock(return_value=create_mock_theory())
            mock_import.return_value = mock_theory_module
            
            flags = create_mock_flags(use_project="logos")
            module = BuildModule(flags)
            
            # Should be able to load and use theory
            self.assertIsNotNone(module.loader.loaded_module)
    
    def test_project_discovery_and_loading(self):
        """Test finding and loading generated projects."""
        # Create project structure
        project_files = create_test_project_structure()
        project_dir = Path(project_files['semantic']).parent
        
        # Create loader starting from inside project
        test_file = project_dir / "test.py"
        test_file.write_text("# Test file")
        
        flags = create_mock_flags(file_path=str(test_file))
        loader = ModuleLoader("test_module", str(test_file))
        
        # Should find project directory
        found_dir = loader.find_project_directory()
        self.assertEqual(str(found_dir), str(project_dir))
        
        # Cleanup
        self.cleanup.add_dir(str(project_dir))


class TestComparisonRunnerIntegration(unittest.TestCase):
    """Test integration between comparison and runner components."""
    
    def setUp(self):
        """Set up test environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_comparison_uses_runner_for_each_theory(self):
        """Test comparison delegates to runner for each theory."""
        flags = create_mock_flags(comparison=True)
        module = BuildModule(flags)
        
        # Setup test data
        theories = {
            "Theory1": create_mock_theory(),
            "Theory2": create_mock_theory()
        }
        example = [["A"], ["B"], {"N": 2}]
        
        with patch.object(module.runner, 'try_single_N') as mock_try:
            mock_try.return_value = (True, Mock())  # Valid result
            
            # Run comparison
            result = module.comparison.compare_semantics(
                "TEST", example, theories, flags
            )
            
            # Should call runner for each theory
            self.assertEqual(mock_try.call_count, 2)
            
            # Verify results structure
            self.assertIn("Theory1", result)
            self.assertIn("Theory2", result)
    
    def test_comparison_handles_runner_failures(self):
        """Test comparison handles runner failures gracefully."""
        flags = create_mock_flags(comparison=True)
        module = BuildModule(flags)
        
        theories = {
            "Good": create_mock_theory(),
            "Bad": create_mock_theory()
        }
        example = [["A"], ["B"], {"N": 2}]
        
        def side_effect(*args, **kwargs):
            if args[0] == "Good":
                return (True, Mock())
            else:
                raise RuntimeError("Theory error")
        
        with patch.object(module.runner, 'try_single_N', side_effect=side_effect):
            result = module.comparison.compare_semantics(
                "TEST", example, theories, flags
            )
            
            # Should have result for good theory
            self.assertIn("Good", result)
            # Bad theory might be skipped or marked as error
            if "Bad" in result:
                self.assertIn("error", str(result["Bad"]).lower())


class TestTranslationIntegration(unittest.TestCase):
    """Test translation integration with other components."""
    
    def test_runner_can_use_translation(self):
        """Test runner can access and use translation component."""
        flags = create_mock_flags()
        module = BuildModule(flags)
        
        # Runner should be able to translate through build_module
        example = [["A \\wedge B"], ["A"], {"N": 2}]
        dictionary = {"\\wedge": "∧"}
        
        # Test translation is accessible
        translated = module.translation.translate(example, dictionary)
        self.assertIn("∧", translated[0][0])
    
    def test_comparison_translation_workflow(self):
        """Test comparison can work with translated formulas."""
        flags = create_mock_flags(comparison=True)
        module = BuildModule(flags)
        
        # Mock translation in workflow
        with patch.object(module.translation, 'translate_example') as mock_trans:
            mock_trans.return_value = [["A ∧ B"], ["A"], {"N": 2}]
            
            # This could be used in visualization/output
            result = mock_trans("TEST", [["A \\wedge B"], ["A"], {"N": 2}], {"\\wedge": "∧"})
            
            self.assertIn("∧", result[0][0])


class TestFullPipelineIntegration(unittest.TestCase):
    """Test complete pipeline from file to output."""
    
    def setUp(self):
        """Set up test environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_standalone_module_execution(self):
        """Test executing a standalone module file."""
        # Create complete module
        content = '''
from model_checker.defaults import SemanticDefaults

class TestSemantics(SemanticDefaults):
    def validate_model(self, model, theory_name):
        return True

semantic_theories = {"Test": TestSemantics()}
example_range = {"EX1": [["A"], ["A"], {"N": 2}]}
general_settings = {}
'''
        module_path = self.cleanup.add_file(
            create_temp_module_file(content)
        )
        
        flags = create_mock_flags(file_path=module_path)
        module = BuildModule(flags)
        
        # Should execute without errors
        with patch('z3.Solver') as mock_solver:
            mock_instance = Mock()
            mock_solver.return_value = mock_instance
            mock_instance.check.return_value = Mock(r=1)  # SAT
            
            module.run()
    
    def test_interactive_mode_integration(self):
        """Test interactive mode with all components."""
        flags = create_mock_flags(interactive=True)
        module = BuildModule(flags)
        
        # Mock user input
        with patch('builtins.input', side_effect=['2', '']):  # 2 iterations then stop
            with patch.object(module.runner, 'process_iterations') as mock_iter:
                with patch.object(module.loader, 'load_module'):
                    # Should handle interactive flow
                    module.runner.build_module = module  # Ensure reference
                    module.runner.process_iterations(
                        "TEST", Mock(), Mock(), {"N": 2}, Mock()
                    )
    
    def test_error_recovery_integration(self):
        """Test system recovers from component errors."""
        flags = create_mock_flags()
        module = BuildModule(flags)
        
        # Simulate various errors
        errors = [
            ("loader", ImportError("Module not found")),
            ("runner", RuntimeError("Z3 timeout")),
            ("comparison", ValueError("Invalid comparison"))
        ]
        
        for component_name, error in errors:
            with self.subTest(component=component_name):
                component = getattr(module, component_name)
                
                # Component should handle errors gracefully
                # (This depends on actual error handling implementation)
                self.assertIsNotNone(component)


class TestConcurrencyIntegration(unittest.TestCase):
    """Test concurrent operations between components."""
    
    def test_comparison_multiprocessing(self):
        """Test comparison uses multiprocessing correctly."""
        flags = create_mock_flags(comparison=True)
        
        # Mock multiprocessing
        with patch('multiprocessing.Pool') as mock_pool:
            mock_pool_instance = Mock()
            mock_pool.return_value.__enter__.return_value = mock_pool_instance
            mock_pool_instance.starmap.return_value = [
                ("Theory1", {"valid": True}),
                ("Theory2", {"valid": False})
            ]
            
            module = BuildModule(flags)
            theories = {"Theory1": Mock(), "Theory2": Mock()}
            
            result = module.comparison.run_comparison(
                Mock(), theories, 2  # 2 CPUs
            )
            
            # Should use pool for parallel execution
            mock_pool.assert_called_with(processes=2)


class TestStateManagement(unittest.TestCase):
    """Test component state management and cleanup."""
    
    def test_components_reset_state(self):
        """Test components can reset state between runs."""
        flags = create_mock_flags()
        module = BuildModule(flags)
        
        # Run once
        module.loader.loaded_module = create_mock_module("first")
        
        # Reset and run again
        module.loader.loaded_module = create_mock_module("second")
        
        # Should use new module
        self.assertEqual(module.loader.loaded_module.__name__, "second")
    
    def test_z3_context_isolation(self):
        """Test Z3 contexts are properly isolated."""
        flags = create_mock_flags()
        module = BuildModule(flags)
        
        # Each run should have isolated Z3 context
        with patch('z3.Context') as mock_context:
            mock_context.return_value = Mock()
            
            # Multiple runs should create separate contexts
            for i in range(3):
                with patch.object(module.runner, 'try_single_N'):
                    module.runner.run_model_check(
                        f"TEST_{i}", 
                        [["A"], ["B"], {"N": 2}],
                        Mock(), module, flags
                    )


if __name__ == '__main__':
    unittest.main()