"""Simple baseline tests before refactoring - focus on key behaviors."""

import unittest
import os
from pathlib import Path
from model_checker.builder.module import BuildModule


class SimpleBaselineTests(unittest.TestCase):
    """Test essential behavior we must preserve during refactoring."""
    
    def test_late_imports_exist(self):
        """Verify late imports are where spec says they are."""
        module_path = Path(__file__).parent.parent / "module.py"
        with open(module_path, 'r') as f:
            lines = f.readlines()
        
        # Check key late imports by line number (0-indexed)
        self.assertIn('from model_checker.settings import', lines[98])
        self.assertIn('from model_checker.output import', lines[133])
        
        # Check BuildExample imports (multiple locations)
        be_imports = [i for i, line in enumerate(lines) 
                      if 'from model_checker.builder.example import BuildExample' in line]
        self.assertGreater(len(be_imports), 2)  # At least 3 locations
        
        # Check ModelConstraints imports
        mc_imports = [i for i, line in enumerate(lines) 
                      if 'from model_checker.models.constraints import ModelConstraints' in line]
        self.assertGreater(len(mc_imports), 2)  # Multiple locations
    
    def test_method_count(self):
        """Verify BuildModule has expected number of methods."""
        methods = [name for name in dir(BuildModule) 
                   if callable(getattr(BuildModule, name)) 
                   and not name.startswith('__')
                   and not name.startswith('_')]
        
        # Should have approximately 11 public methods (many are private with _)
        self.assertGreater(len(methods), 8)
        self.assertLess(len(methods), 15)
    
    def test_essential_methods_exist(self):
        """Verify key methods exist that will be moved."""
        essential_methods = [
            'run_model_check',
            'try_single_N', 
            'try_single_N_static',
            'process_example',
            'compare_semantics',
            'run_comparison',
            'translate',
            'translate_example',
            'run_examples',
            '_capture_and_save_output',
            '_load_module',
            '_is_generated_project',
            '_discover_theory_module'
        ]
        
        for method in essential_methods:
            self.assertTrue(hasattr(BuildModule, method),
                            f"Missing essential method: {method}")


if __name__ == '__main__':
    unittest.main()