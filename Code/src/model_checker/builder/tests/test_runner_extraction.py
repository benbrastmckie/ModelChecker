"""Tests for extracted runner module functionality."""

import unittest
import tempfile
import os
from unittest.mock import Mock, patch, MagicMock

# Test the new runner module before it exists (TDD)
try:
    from model_checker.builder.runner import ModelRunner
except ImportError:
    # Module doesn't exist yet - that's expected in TDD
    ModelRunner = None

from model_checker.builder.module import BuildModule


class TestRunnerExtraction(unittest.TestCase):
    """Test that runner functionality works after extraction."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.addCleanup(lambda: __import__('shutil').rmtree(self.temp_dir))
        
        # Create a simple test module
        self.create_test_module()
    
    def create_test_module(self):
        """Create a test module file."""
        self.module_path = os.path.join(self.temp_dir, "test_examples.py")
        content = '''
from model_checker.theory_lib import logos

theory = logos.get_theory(['extensional'])

semantic_theories = {
    "Logos": theory
}

example_range = {
    "TEST_1": [
        ["p"],  # premises
        ["(p \\\\vee \\\\neg p)"],  # conclusions - tautology
        {"N": 2, "max_time": 1}
    ]
}

general_settings = {
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
}
'''
        with open(self.module_path, 'w') as f:
            f.write(content)
    
    @unittest.skipIf(ModelRunner is None, "ModelRunner not yet implemented")
    def test_runner_exists(self):
        """Test that ModelRunner class exists."""
        self.assertIsNotNone(ModelRunner)
    
    @unittest.skipIf(ModelRunner is None, "ModelRunner not yet implemented")
    def test_runner_initialization(self):
        """Test ModelRunner can be initialized."""
        mock_build_module = Mock()
        mock_build_module.general_settings = {'N': 2, 'max_time': 1}
        
        runner = ModelRunner(mock_build_module)
        self.assertIsNotNone(runner)
        self.assertEqual(runner.build_module, mock_build_module)
    
    @unittest.skipIf(ModelRunner is None, "ModelRunner not yet implemented") 
    def test_run_model_check_method(self):
        """Test run_model_check method exists and works."""
        mock_build_module = Mock()
        mock_build_module.general_settings = {'N': 2, 'max_time': 1}
        mock_build_module.translation = Mock()
        mock_build_module.translation.translate = Mock(return_value=[["p"], ["q"], {"N": 2}])
        
        runner = ModelRunner(mock_build_module)
        
        # Test method exists
        self.assertTrue(hasattr(runner, 'run_model_check'))
        
        # Test basic call with mocked BuildExample
        with patch('model_checker.builder.example.BuildExample') as mock_be:
            example_case = [["p"], ["q"], {"N": 2}]
            semantic_theory = {"dictionary": None}
            
            result = runner.run_model_check(
                example_case, "test", "TestTheory", semantic_theory
            )
            
            # Verify BuildExample was created
            mock_be.assert_called_once()
            
            # Verify it returns the BuildExample
            self.assertEqual(result, mock_be.return_value)
    
    @unittest.skipIf(ModelRunner is None, "ModelRunner not yet implemented")
    def test_try_single_N_method(self):
        """Test try_single_N method exists."""
        mock_build_module = Mock()
        runner = ModelRunner(mock_build_module)
        
        self.assertTrue(hasattr(runner, 'try_single_N'))
        self.assertTrue(callable(getattr(runner, 'try_single_N')))
    
    @unittest.skipIf(ModelRunner is None, "ModelRunner not yet implemented")
    def test_process_example_method(self):
        """Test process_example method exists."""
        mock_build_module = Mock()
        runner = ModelRunner(mock_build_module)
        
        self.assertTrue(hasattr(runner, 'process_example'))
    
    def test_build_module_delegates_to_runner(self):
        """Test BuildModule delegates to runner after refactoring."""
        # This tests that BuildModule properly delegates after we implement runner
        
        mock_flags = Mock()
        mock_flags.file_path = self.module_path
        mock_flags.print_constraints = False
        mock_flags.print_z3 = False
        mock_flags.save_output = False
        mock_flags._parsed_args = []
        mock_flags.comparison = False
        
        build_module = BuildModule(mock_flags)
        
        # Check if runner attribute exists (will after refactoring)
        if hasattr(build_module, 'runner'):
            self.assertIsNotNone(build_module.runner)
            # After refactoring, run_model_check is accessed via runner
            self.assertTrue(hasattr(build_module.runner, 'run_model_check'))


if __name__ == '__main__':
    unittest.main()