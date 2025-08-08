"""Test that iterator preserves countermodel properties across all models.

This test suite verifies that MODEL 2+ maintain the fundamental countermodel
requirements: premises remain true and conclusions remain false at the
evaluation world.
"""

import unittest
import os
import sys

# Add project root to path
project_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(__file__)))))
sys.path.insert(0, project_root)

from model_checker.builder.module import BuildModule


class TestConstraintPreservation(unittest.TestCase):
    """Test that iterator preserves countermodel properties."""
    
    def setUp(self):
        """Set up test environment."""
        self.test_dir = os.path.dirname(__file__)
        
    def _create_test_file(self, premises, conclusions, iterate=3):
        """Create a temporary test file with given premises and conclusions."""
        content = f"""
from model_checker.theory_lib.logos import get_theory

# Test case for constraint preservation
premises = {premises}
conclusions = {conclusions}
iterate = {iterate}
settings = {{
    'N': 2,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'max_time': 10
}}
semantic_theory = get_theory()
"""
        
        # Write to temporary file
        test_file = os.path.join(self.test_dir, 'test_constraint_temp.py')
        with open(test_file, 'w') as f:
            f.write(content)
            
        return test_file
    
    def tearDown(self):
        """Clean up test files."""
        test_file = os.path.join(self.test_dir, 'test_constraint_temp.py')
        if os.path.exists(test_file):
            os.remove(test_file)
    
    def test_premises_remain_true_in_all_models(self):
        """All MODEL 2+ must have true premises at evaluation world."""
        # Create test file
        test_file = self._create_test_file(['A'], [], iterate=3)
        
        # Build module
        build_module = BuildModule(test_file)
        build_module.run()
        
        # Check all models
        self.assertTrue(build_module.countermodel_found, "Should find countermodel")
        
        if hasattr(build_module, 'example_results'):
            for example_name, example in build_module.example_results.items():
                if hasattr(example, 'iterator') and example.iterator:
                    models = example.iterator.get_all_models()
                    
                    # Verify we have multiple models
                    self.assertGreater(len(models), 1, f"Should have multiple models for {example_name}")
                    
                    # Check each model
                    for i, model in enumerate(models):
                        with self.subTest(model=i+1, example=example_name):
                            # Get evaluation world
                            eval_world = model.main_point['world']
                            
                            # Check all premises are true at evaluation world
                            for premise in model.premises:
                                premise_truth = model.evaluate_at_world(premise, eval_world)
                                self.assertTrue(premise_truth,
                                    f"Premise {premise} should be true in MODEL {i+1} at world {eval_world}")
    
    def test_conclusions_remain_false_in_all_models(self):
        """All MODEL 2+ must have false conclusions at evaluation world."""
        # Create test file
        test_file = self._create_test_file(['(A \\\\wedge B)'], ['C'], iterate=3)
        
        # Build module
        build_module = BuildModule(test_file)
        build_module.run()
        
        # Check all models
        self.assertTrue(build_module.countermodel_found, "Should find countermodel")
        
        if hasattr(build_module, 'example_results'):
            for example_name, example in build_module.example_results.items():
                if hasattr(example, 'iterator') and example.iterator:
                    models = example.iterator.get_all_models()
                    
                    # Verify we have multiple models
                    self.assertGreater(len(models), 1, f"Should have multiple models for {example_name}")
                    
                    # Check each model
                    for i, model in enumerate(models):
                        with self.subTest(model=i+1, example=example_name):
                            # Get evaluation world
                            eval_world = model.main_point['world']
                            
                            # Check all conclusions are false at evaluation world
                            for conclusion in model.conclusions:
                                conclusion_truth = model.evaluate_at_world(conclusion, eval_world)
                                self.assertFalse(conclusion_truth,
                                    f"Conclusion {conclusion} should be false in MODEL {i+1} at world {eval_world}")
    
    def test_complex_example(self):
        """Test with more complex premises and conclusions."""
        # Create test file
        test_file = self._create_test_file(
            ['(A \\\\vee B)', '(C \\\\rightarrow A)'],
            ['(B \\\\wedge C)', 'A'],
            iterate=2
        )
        
        # Build module
        build_module = BuildModule(test_file)
        build_module.run()
        
        # Check all models
        self.assertTrue(build_module.countermodel_found, "Should find countermodel")
        
        if hasattr(build_module, 'example_results'):
            for example_name, example in build_module.example_results.items():
                if hasattr(example, 'iterator') and example.iterator:
                    models = example.iterator.get_all_models()
                    
                    # Check each model
                    for i, model in enumerate(models):
                        with self.subTest(model=i+1, example=example_name):
                            # Get evaluation world
                            eval_world = model.main_point['world']
                            
                            # All premises should be true
                            for premise in model.premises:
                                premise_truth = model.evaluate_at_world(premise, eval_world)
                                self.assertTrue(premise_truth,
                                    f"Premise {premise} should be true in MODEL {i+1}")
                            
                            # All conclusions should be false
                            for conclusion in model.conclusions:
                                conclusion_truth = model.evaluate_at_world(conclusion, eval_world)
                                self.assertFalse(conclusion_truth,
                                    f"Conclusion {conclusion} should be false in MODEL {i+1}")


class TestVerifyFalsifyExtraction(unittest.TestCase):
    """Test extraction of verify/falsify state from models."""
    
    def test_extract_state_method_exists(self):
        """Test that extract_verify_falsify_state method will be added."""
        from model_checker.models.structure import ModelStructure
        
        # This should fail initially - method doesn't exist yet
        self.assertTrue(
            hasattr(ModelStructure, 'extract_verify_falsify_state'),
            "ModelStructure should have extract_verify_falsify_state method"
        )


if __name__ == '__main__':
    unittest.main()