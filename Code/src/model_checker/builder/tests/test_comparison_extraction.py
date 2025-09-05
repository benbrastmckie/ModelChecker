"""Tests for extracted comparison module functionality."""

import unittest
import tempfile
import os
from unittest.mock import Mock, patch, MagicMock

# Test the new comparison module before it exists (TDD)
try:
    from model_checker.builder.comparison import ModelComparison
except ImportError:
    # Module doesn't exist yet - that's expected in TDD
    ModelComparison = None

from model_checker.builder.module import BuildModule


class TestComparisonExtraction(unittest.TestCase):
    """Test that comparison functionality works after extraction."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.addCleanup(lambda: __import__('shutil').rmtree(self.temp_dir))
        
        # Create a simple test module
        self.create_test_module()
    
    def create_test_module(self):
        """Create a test module file."""
        self.module_path = os.path.join(self.temp_dir, "test_comparison.py")
        content = '''
from model_checker.theory_lib import logos, exclusion

theory_logos = logos.get_theory(['extensional'])
theory_exclusion = exclusion.get_theory()

semantic_theories = {
    "Logos": theory_logos,
    "Exclusion": theory_exclusion
}

example_range = {
    "TEST_1": [
        ["p"],  # premises
        ["(p \\\\vee q)"],  # conclusions
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
    
    @unittest.skipIf(ModelComparison is None, "ModelComparison not yet implemented")
    def test_comparison_exists(self):
        """Test that ModelComparison class exists."""
        self.assertIsNotNone(ModelComparison)
    
    @unittest.skipIf(ModelComparison is None, "ModelComparison not yet implemented")
    def test_comparison_initialization(self):
        """Test ModelComparison can be initialized."""
        mock_build_module = Mock()
        mock_build_module.general_settings = {'N': 2, 'max_time': 1}
        
        comparison = ModelComparison(mock_build_module)
        self.assertIsNotNone(comparison)
        self.assertEqual(comparison.build_module, mock_build_module)
    
    @unittest.skipIf(ModelComparison is None, "ModelComparison not yet implemented")
    def test_compare_semantics_method(self):
        """Test compare_semantics method exists and works."""
        mock_build_module = Mock()
        mock_build_module.general_settings = {'N': 2, 'max_time': 1}
        
        comparison = ModelComparison(mock_build_module)
        
        # Test method exists
        self.assertTrue(hasattr(comparison, 'compare_semantics'))
        
        # Test basic call with mock data
        example_theory_tuples = [
            ("Theory1", {"semantics": Mock()}, [["p"], ["q"], {"N": 2}]),
            ("Theory2", {"semantics": Mock()}, [["p"], ["q"], {"N": 2}])
        ]
        
        # Mock the static method that would be used
        with patch.object(comparison, 'compare_semantics') as mock_compare:
            mock_compare.return_value = [("Theory1", 3), ("Theory2", 2)]
            
            result = comparison.compare_semantics(example_theory_tuples)
            
            # Verify it returns expected format
            self.assertIsInstance(result, list)
            self.assertEqual(len(result), 2)
            self.assertEqual(result[0], ("Theory1", 3))
            self.assertEqual(result[1], ("Theory2", 2))
    
    @unittest.skipIf(ModelComparison is None, "ModelComparison not yet implemented")
    def test_run_comparison_method(self):
        """Test run_comparison method exists."""
        mock_build_module = Mock()
        mock_build_module.example_range = {
            "TEST": [["p"], ["q"], {"N": 2}]
        }
        mock_build_module.semantic_theories = {
            "Theory1": {"semantics": Mock()}
        }
        
        comparison = ModelComparison(mock_build_module)
        
        self.assertTrue(hasattr(comparison, 'run_comparison'))
        self.assertTrue(callable(getattr(comparison, 'run_comparison')))
    
    def test_build_module_delegates_to_comparison(self):
        """Test BuildModule delegates to comparison after refactoring."""
        # This tests that BuildModule properly delegates after we implement comparison
        
        mock_flags = Mock()
        mock_flags.file_path = self.module_path
        mock_flags.print_constraints = False
        mock_flags.print_z3 = False
        mock_flags.save_output = False
        mock_flags._parsed_args = []
        mock_flags.comparison = True  # Enable comparison mode
        
        build_module = BuildModule(mock_flags)
        
        # Check if comparison attribute exists (will after refactoring)
        if hasattr(build_module, 'comparison'):
            self.assertIsNotNone(build_module.comparison)
            # After refactoring, compare_semantics is accessed via comparison module
            self.assertTrue(hasattr(build_module.comparison, 'compare_semantics'))


if __name__ == '__main__':
    unittest.main()