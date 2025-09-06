"""Simplified unit tests for BuildExample functionality.

This module provides focused unit tests for the BuildExample class using
minimal mocking and real components where appropriate.
"""

import unittest
import sys
import tempfile
import os
from io import StringIO
from unittest.mock import Mock, patch

from model_checker.builder.example import BuildExample
from model_checker.builder.module import BuildModule
from model_checker.builder.error_types import ValidationError


class TestBuildExampleBasic(unittest.TestCase):
    """Test BuildExample basic functionality with real components."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.test_file = self._create_test_module()
        
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        if os.path.exists(self.temp_dir):
            shutil.rmtree(self.temp_dir)
    
    def _create_test_module(self):
        """Create a simple test module file."""
        content = """
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {"SIMPLE": [["A"], ["B"], {"N": 2}]}
general_settings = {}
"""
        test_file = os.path.join(self.temp_dir, "test_module.py")
        with open(test_file, 'w') as f:
            f.write(content)
        return test_file
    
    def test_build_example_initialization(self):
        """Test that BuildExample can be initialized with valid inputs."""
        # Create a real BuildModule
        flags = Mock(
            file_path=self.test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            _parsed_args=[]
        )
        
        build_module = BuildModule(flags)
        
        # Get the theory and example
        theory = build_module.semantic_theories["Test"]
        example = list(build_module.example_range.values())[0]
        
        # Create BuildExample
        build_example = BuildExample(build_module, theory, example, "Test")
        
        # Verify it was created
        self.assertIsNotNone(build_example)
        self.assertEqual(build_example.build_module, build_module)
        self.assertEqual(build_example.premises, ["A"])
        self.assertEqual(build_example.conclusions, ["B"])
    
    def test_build_example_get_result(self):
        """Test that BuildExample can get results after model checking."""
        # Create a real BuildModule
        flags = Mock(
            file_path=self.test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            _parsed_args=[]
        )
        
        build_module = BuildModule(flags)
        
        # Get the theory and example
        theory = build_module.semantic_theories["Test"]
        example = list(build_module.example_range.values())[0]
        
        # Create BuildExample
        build_example = BuildExample(build_module, theory, example, "Test")
        
        # Get result
        result = build_example.get_result()
        
        # Verify result structure
        self.assertIsInstance(result, dict)
        self.assertIn("model_found", result)
        self.assertIn("runtime", result)
        self.assertIn("model_structure", result)
        self.assertIsInstance(result["model_found"], bool)
        self.assertIsInstance(result["runtime"], (int, float))
    
    def test_build_example_print_model(self):
        """Test that BuildExample can print model output."""
        # Create a real BuildModule
        flags = Mock(
            file_path=self.test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            _parsed_args=[]
        )
        
        build_module = BuildModule(flags)
        
        # Get the theory and example
        theory = build_module.semantic_theories["Test"]
        example = list(build_module.example_range.values())[0]
        
        # Create BuildExample
        build_example = BuildExample(build_module, theory, example, "Test")
        
        # Capture output
        output = StringIO()
        
        # Print model
        build_example.print_model(
            example_name="TEST",
            theory_name="Test",
            output=output
        )
        
        # Verify something was printed
        output_text = output.getvalue()
        self.assertTrue(len(output_text) > 0,
                       "Should print some output")
    
    def test_build_example_with_no_model(self):
        """Test BuildExample when no model is found."""
        # Create a module with unsatisfiable example
        content = """
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
# Contradiction: A and not A
example_range = {"UNSAT": [["A", "\\\\neg A"], ["B"], {"N": 2}]}
general_settings = {}
"""
        test_file = os.path.join(self.temp_dir, "unsat_module.py")
        with open(test_file, 'w') as f:
            f.write(content)
        
        flags = Mock(
            file_path=test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            _parsed_args=[]
        )
        
        build_module = BuildModule(flags)
        
        # Get the theory and example
        theory = build_module.semantic_theories["Test"]
        example = list(build_module.example_range.values())[0]
        
        # Create BuildExample
        build_example = BuildExample(build_module, theory, example, "Test")
        
        # Get result
        result = build_example.get_result()
        
        # Should find no model due to contradiction
        self.assertFalse(result["model_found"],
                        "Should not find model for contradictory premises")
    
    def test_build_example_comparison_mode(self):
        """Test BuildExample in comparison mode."""
        # Create a module with multiple theories
        content = """
from model_checker.theory_lib.logos import get_theory

theory1 = get_theory(['extensional'])
theory2 = get_theory(['modal'])
semantic_theories = {"Ext": theory1, "Modal": theory2}
example_range = {"TEST": [["A"], ["B"], {"N": 2}]}
general_settings = {}
"""
        test_file = os.path.join(self.temp_dir, "comparison_module.py")
        with open(test_file, 'w') as f:
            f.write(content)
        
        flags = Mock(
            file_path=test_file,
            comparison=True,
            interactive=False,
            iterations=False,
            quiet=True,
            _parsed_args=[]
        )
        
        build_module = BuildModule(flags)
        
        # Build module should have multiple theories
        self.assertEqual(len(build_module.semantic_theories), 2)
        
        # Get first theory and example
        theory = build_module.semantic_theories["Ext"]
        example = list(build_module.example_range.values())[0]
        
        # Create BuildExample in comparison mode
        build_example = BuildExample(build_module, theory, example, "Ext")
        
        # Verify it was created
        self.assertIsNotNone(build_example)
        
        # Settings manager should know it's in comparison mode
        self.assertTrue(hasattr(build_example, 'settings_manager'))


class TestBuildExampleErrorHandling(unittest.TestCase):
    """Test BuildExample error handling."""
    
    def test_get_result_without_model_check(self):
        """Test get_result raises error when called before model checking."""
        # Create a BuildExample without proper initialization
        example = BuildExample.__new__(BuildExample)
        
        # Should raise RuntimeError
        with self.assertRaises(RuntimeError) as context:
            example.get_result()
        
        self.assertIn("no model check", str(context.exception).lower(),
                     "Should indicate model check not performed")
    
    def test_invalid_theory_structure(self):
        """Test BuildExample handles invalid theory structure."""
        from model_checker.builder.validation import validate_semantic_theory
        
        # Test with invalid theory structure
        invalid_theory = {"invalid": "structure"}
        
        with self.assertRaises(ValidationError) as context:
            validate_semantic_theory(invalid_theory)
        
        # Check for either "invalid" or "missing" in error message
        error_msg = str(context.exception).lower()
        self.assertTrue("missing" in error_msg or "invalid" in error_msg,
                       f"Should indicate invalid or missing component: {error_msg}")
    
    def test_invalid_example_structure(self):
        """Test BuildExample handles invalid example structure."""
        from model_checker.builder.validation import validate_example_case
        
        # Test with invalid example structure
        invalid_example = ["not", "enough"]  # Missing settings
        
        with self.assertRaises((ValueError, ValidationError)) as context:
            validate_example_case(invalid_example)
        
        # Check that error mentions the issue
        error_msg = str(context.exception).lower()
        self.assertTrue("must be" in error_msg or "exactly 3" in error_msg,
                       f"Should indicate structure issue: {error_msg}")


class TestBuildExampleIntegration(unittest.TestCase):
    """Test BuildExample integration with real theories."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        if os.path.exists(self.temp_dir):
            shutil.rmtree(self.temp_dir)
    
    def test_logos_extensional_theory(self):
        """Test BuildExample with logos extensional theory."""
        content = """
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Extensional": theory}
# Simple test without complex operators
example_range = {"SIMPLE": [["A"], ["B"], {"N": 2}]}
general_settings = {}
"""
        test_file = os.path.join(self.temp_dir, "logos_test.py")
        with open(test_file, 'w') as f:
            f.write(content)
        
        flags = Mock(
            file_path=test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            _parsed_args=[]
        )
        
        build_module = BuildModule(flags)
        
        # Run the example
        theory = build_module.semantic_theories["Extensional"]
        example = list(build_module.example_range.values())[0]
        
        build_example = BuildExample(build_module, theory, example, "Extensional")
        result = build_example.get_result()
        
        # Simple example A premises, B conclusion - should find a countermodel
        self.assertTrue(result["model_found"],
                       "Should find countermodel where A is true but B is false")
    
    def test_find_next_model_basic(self):
        """Test find_next_model with a simple example."""
        content = """
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
# Simple satisfiable example - just A as premise, no conclusions
example_range = {"SAT": [["A"], [], {"N": 2}]}
general_settings = {}
"""
        test_file = os.path.join(self.temp_dir, "next_model_test.py")
        with open(test_file, 'w') as f:
            f.write(content)
        
        flags = Mock(
            file_path=test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            _parsed_args=[]
        )
        
        build_module = BuildModule(flags)
        
        theory = build_module.semantic_theories["Test"]
        example = list(build_module.example_range.values())[0]
        
        build_example = BuildExample(build_module, theory, example, "Test")
        
        # Should find initial model
        result = build_example.get_result()
        self.assertTrue(result["model_found"],
                       "Should find initial model for A")
        
        # Try to find next model
        # Note: find_next_model may or may not find another model
        # depending on the constraint solver
        found_next = build_example.find_next_model()
        # Just verify it returns a boolean
        self.assertIsInstance(found_next, bool,
                            "find_next_model should return boolean")


if __name__ == '__main__':
    unittest.main()