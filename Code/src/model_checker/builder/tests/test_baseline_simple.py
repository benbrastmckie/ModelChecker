"""Simple baseline tests before refactoring - focus on key behaviors."""

import unittest
import os
from pathlib import Path
from model_checker.builder.module import BuildModule


class SimpleBaselineTests(unittest.TestCase):
    """Test essential behavior we must preserve during refactoring."""
    
    def test_late_imports_exist(self):
        """Verify late imports still exist in refactored module."""
        module_path = Path(__file__).parent.parent / "module.py"
        with open(module_path, 'r') as f:
            content = f.read()
        
        # Check that key imports still exist (not by line number anymore)
        self.assertIn('from model_checker.settings import', content)
        self.assertIn('from model_checker.output import', content)
        
        # Check component imports exist
        self.assertIn('from model_checker.builder.runner import ModelRunner', content)
        self.assertIn('from model_checker.builder.comparison import ModelComparison', content)
        self.assertIn('from model_checker.builder.translation import OperatorTranslation', content)
        self.assertIn('from model_checker.builder.loader import ModuleLoader', content)
    
    def test_method_count(self):
        """Verify BuildModule has reduced number of methods after refactoring."""
        methods = [name for name in dir(BuildModule) 
                   if callable(getattr(BuildModule, name)) 
                   and not name.startswith('__')
                   and not name.startswith('_')]
        
        # After refactoring, should have very few public methods (most moved to components)
        # We have: run_examples, run_comparison, translate, translate_example
        self.assertGreaterEqual(len(methods), 1)  # At least run_examples
        self.assertLessEqual(len(methods), 4)    # Only essential public methods
    
    def test_essential_components_exist(self):
        """Verify key components exist on BuildModule after refactoring."""
        # These tests now check for components, not methods
        import tempfile
        import os
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            f.write("""
class TestSemantics:
    DEFAULT_EXAMPLE_SETTINGS = {"N": 2}
    DEFAULT_GENERAL_SETTINGS = {
        "save_output": False,
        "print_constraints": False,
        "print_z3": False
    }

semantic_theories = {
    "Test": {
        "semantics": TestSemantics,
        "operators": {},
        "model": object,
        "proposition": object
    }
}
example_range = {
    "TEST_EXAMPLE": [
        [],  # assumptions
        ["A"],  # formula
        {"N": 2}  # settings
    ]
}
general_settings = {"save_output": False}
""")
            temp_file = f.name
        
        try:
            from unittest.mock import Mock
            mock_flags = Mock()
            mock_flags.file_path = temp_file
            mock_flags.module_name = "test_module"
            mock_flags.module_path = None
            mock_flags.comparison = False
            mock_flags._parsed_args = []  # Required by SettingsManager
            
            # Create module instance
            module = BuildModule(mock_flags)
            
            # Check essential components exist
            self.assertTrue(hasattr(module, 'runner'), "Runner component missing")
            self.assertTrue(hasattr(module, 'translation'), "Translation component missing")
            self.assertTrue(hasattr(module, 'loader'), "Loader component missing")
            
            # Verify runner has the moved methods
            self.assertTrue(hasattr(module.runner, 'run_model_check'))
            self.assertTrue(hasattr(module.runner, 'try_single_N'))
            self.assertTrue(hasattr(module.runner, 'process_example'))
            self.assertTrue(hasattr(module.runner, 'process_iterations'))
            
            # Verify translation has its method
            self.assertTrue(hasattr(module.translation, 'translate'))
            
            # Verify loader has its methods
            self.assertTrue(hasattr(module.loader, 'load_module'))
            self.assertTrue(hasattr(module.loader, 'discover_theory_module'))
        
        finally:
            os.unlink(temp_file)


if __name__ == '__main__':
    unittest.main()