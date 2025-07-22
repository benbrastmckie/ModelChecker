"""Tests for the BuildModule class with focus on logos and exclusion theories."""

import unittest
import tempfile
import os
from unittest.mock import Mock, patch, MagicMock
from pathlib import Path

from model_checker.builder.module import BuildModule


class TestBuildModule(unittest.TestCase):
    """Test the BuildModule class focusing on logos and exclusion theory integration."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.addCleanup(lambda: __import__('shutil').rmtree(self.temp_dir))
        
        # Mock module flags with proper structure for settings manager
        self.mock_flags = Mock()
        self.mock_flags.file_path = os.path.join(self.temp_dir, "test_examples.py")
        self.mock_flags.print_constraints = False
        self.mock_flags.print_z3 = False
        self.mock_flags.save_output = False
        # Add _parsed_args for compatibility with settings manager
        self.mock_flags._parsed_args = []
        
        # Create a basic example module file
        self.create_test_module_file()
    
    def create_test_module_file(self, theory_type="logos"):
        """Create a test module file for testing."""
        if theory_type == "logos":
            module_content = '''
from model_checker.theory_lib import logos

# Get logos theory components
theory = logos.get_theory(['extensional'])

semantic_theories = {
    "Logos": theory
}

example_range = {
    "LOGOS_TEST_1": [
        [],  # premises
        ["p"],  # conclusions
        {"N": 2, "max_time": 1, "expectation": False}  # settings
    ]
}

general_settings = {
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
}
'''
        elif theory_type == "exclusion":
            module_content = '''
from model_checker.theory_lib import exclusion

semantic_theories = {
    "Exclusion": {
        "semantics": exclusion.WitnessSemantics,
        "proposition": exclusion.WitnessProposition,
        "model": exclusion.WitnessStructure,
        "operators": exclusion.witness_operators
    }
}

example_range = {
    "EXCLUSION_TEST_1": [
        [],  # premises
        ["p"],  # conclusions
        {"N": 2, "max_time": 1, "expectation": False}  # settings
    ]
}

general_settings = {
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
}
'''
        
        with open(self.mock_flags.file_path, 'w') as f:
            f.write(module_content)
    
    def test_module_initialization_logos(self):
        """Test that BuildModule initializes properly with logos theory."""
        self.create_test_module_file("logos")
        
        build_module = BuildModule(self.mock_flags)
        
        # Test basic initialization
        self.assertIsNotNone(build_module.module)
        self.assertIsNotNone(build_module.semantic_theories)
        self.assertIsNotNone(build_module.example_range)
        self.assertIsNotNone(build_module.general_settings)
        
        # Test logos-specific attributes
        self.assertIn("Logos", build_module.semantic_theories)
        self.assertIn("LOGOS_TEST_1", build_module.example_range)
        
        # Test that logos theory components are loaded
        logos_theory = build_module.semantic_theories["Logos"]
        self.assertIn("semantics", logos_theory)
        self.assertIn("operators", logos_theory)
        self.assertIn("model", logos_theory)
        self.assertIn("proposition", logos_theory)
    
    def test_module_initialization_exclusion(self):
        """Test that BuildModule initializes properly with exclusion theory."""
        self.create_test_module_file("exclusion")
        
        build_module = BuildModule(self.mock_flags)
        
        # Test basic initialization
        self.assertIsNotNone(build_module.module)
        self.assertIsNotNone(build_module.semantic_theories)
        self.assertIsNotNone(build_module.example_range)
        self.assertIsNotNone(build_module.general_settings)
        
        # Test exclusion-specific attributes
        self.assertIn("Exclusion", build_module.semantic_theories)
        self.assertIn("EXCLUSION_TEST_1", build_module.example_range)
        
        # Test that exclusion theory components are loaded
        exclusion_theory = build_module.semantic_theories["Exclusion"]
        self.assertIn("semantics", exclusion_theory)
        self.assertIn("operators", exclusion_theory)
        self.assertIn("model", exclusion_theory)
        self.assertIn("proposition", exclusion_theory)
    
    def test_module_missing_attributes(self):
        """Test error handling when module is missing required attributes."""
        # Create a module file missing semantic_theories
        module_content = '''
example_range = {}
general_settings = {}
'''
        with open(self.mock_flags.file_path, 'w') as f:
            f.write(module_content)
        
        with self.assertRaises(AttributeError) as context:
            BuildModule(self.mock_flags)
        
        self.assertIn("semantic_theories", str(context.exception))
    
    def test_translate_example_method(self):
        """Test the translate_example method works with logos/exclusion."""
        self.create_test_module_file("logos")
        build_module = BuildModule(self.mock_flags)
        
        # Test example case
        example_case = [[], ["p"], {"N": 2}]
        
        # Test translation (logos doesn't have translation dict by default)
        result = build_module.translate_example(example_case, build_module.semantic_theories)
        
        self.assertIsInstance(result, list)
        self.assertEqual(len(result), len(build_module.semantic_theories))
        
        # Each result should be a tuple (theory_name, semantic_theory, translated_case)
        for theory_name, semantic_theory, translated_case in result:
            self.assertIsInstance(theory_name, str)
            self.assertIsInstance(semantic_theory, dict)
            self.assertIsInstance(translated_case, list)
    
    def test_translate_method(self):
        """Test the translate method for operator substitution."""
        self.create_test_module_file("logos")
        build_module = BuildModule(self.mock_flags)
        
        # Test case with operator to be translated
        example_case = [
            ["p \\wedge q"],  # premises
            ["p"],  # conclusions
            {"N": 2}  # settings
        ]
        
        # Translation dictionary
        translation_dict = {"\\wedge": "\\land"}
        
        result = build_module.translate(example_case, translation_dict)
        
        # Check that translation occurred
        self.assertEqual(result[0], ["p \\land q"])  # premises should be translated
        self.assertEqual(result[1], ["p"])  # conclusions unchanged
        self.assertEqual(result[2], {"N": 2})  # settings unchanged
    
    @patch('model_checker.builder.example.BuildExample')
    def test_run_model_check_logos(self, mock_build_example):
        """Test run_model_check method with logos theory."""
        self.create_test_module_file("logos")
        build_module = BuildModule(self.mock_flags)
        
        # Mock BuildExample
        mock_example = Mock()
        mock_build_example.return_value = mock_example
        
        example_case = [[], ["p"], {"N": 2, "max_time": 1}]
        example_name = "test_example"
        theory_name = "Logos"
        semantic_theory = build_module.semantic_theories[theory_name]
        
        result = build_module.run_model_check(example_case, example_name, theory_name, semantic_theory)
        
        # Verify BuildExample was called
        mock_build_example.assert_called_once()
        self.assertEqual(result, mock_example)
    
    @patch('model_checker.builder.example.BuildExample')
    def test_run_model_check_exclusion(self, mock_build_example):
        """Test run_model_check method with exclusion theory."""
        self.create_test_module_file("exclusion")
        build_module = BuildModule(self.mock_flags)
        
        # Mock BuildExample
        mock_example = Mock()
        mock_build_example.return_value = mock_example
        
        example_case = [[], ["p"], {"N": 2, "max_time": 1}]
        example_name = "test_example"
        theory_name = "Exclusion"
        semantic_theory = build_module.semantic_theories[theory_name]
        
        result = build_module.run_model_check(example_case, example_name, theory_name, semantic_theory)
        
        # Verify BuildExample was called
        mock_build_example.assert_called_once()
        self.assertEqual(result, mock_example)
    
    def test_flag_overrides(self):
        """Test that module flags properly override general settings."""
        # Set flags
        self.mock_flags.print_constraints = True
        self.mock_flags.print_z3 = True
        
        self.create_test_module_file("logos")
        build_module = BuildModule(self.mock_flags)
        
        # Test that flags overrode the module settings
        self.assertTrue(build_module.print_constraints)
        self.assertTrue(build_module.print_z3)
    
    def test_process_example_error_handling(self):
        """Test error handling in process_example method."""
        self.create_test_module_file("logos")
        build_module = BuildModule(self.mock_flags)
        
        # Test with malformed example case
        with patch('model_checker.builder.module.BuildExample') as mock_build_example:
            mock_build_example.side_effect = ValueError("Test error")
            
            example_case = [[], ["p"], {"N": 2, "max_time": 1}]
            example_name = "test_example"
            theory_name = "Logos"
            semantic_theory = build_module.semantic_theories[theory_name]
            
            # Should handle the error gracefully
            with patch('builtins.print') as mock_print:
                with self.assertRaises(ValueError):
                    build_module.process_example(example_name, example_case, theory_name, semantic_theory)
    
    def test_generated_project_detection(self):
        """Test detection of generated projects."""
        # Create a project directory structure
        project_dir = os.path.join(self.temp_dir, "project_test_theory")
        os.makedirs(project_dir)
        
        self.mock_flags.file_path = os.path.join(project_dir, "examples.py")
        
        # Create test content
        self.create_test_module_file("logos")
        
        build_module = BuildModule(self.mock_flags)
        
        # Test that it detects generated project correctly
        is_generated = build_module._is_generated_project(project_dir)
        self.assertTrue(is_generated)
    
    def test_package_detection(self):
        """Test detection of regular Python packages."""
        # Create a package structure
        package_dir = os.path.join(self.temp_dir, "test_package")
        os.makedirs(package_dir)
        
        # Create __init__.py to make it a package
        init_file = os.path.join(package_dir, "__init__.py")
        with open(init_file, 'w') as f:
            f.write("# Package init")
        
        self.mock_flags.file_path = os.path.join(package_dir, "examples.py")
        self.create_test_module_file("logos")
        
        build_module = BuildModule(self.mock_flags)
        
        # Should handle package imports correctly
        self.assertIsNotNone(build_module.module)


class TestBuildModuleIntegration(unittest.TestCase):
    """Integration tests for BuildModule with real logos and exclusion theories."""
    
    def setUp(self):
        """Set up integration test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.addCleanup(lambda: __import__('shutil').rmtree(self.temp_dir))
    
    def test_logos_theory_integration(self):
        """Test integration with real logos theory."""
        # Create a minimal logos example module
        module_content = '''
try:
    from model_checker.theory_lib import logos
    
    # Get logos theory with extensional operators
    theory = logos.get_theory(['extensional'])
    
    semantic_theories = {
        "Logos": theory
    }
    
    example_range = {
        "LOGOS_INTEGRATION_TEST": [
            [],  # premises
            ["p"],  # conclusions
            {"N": 2, "max_time": 1, "expectation": False}  # settings
        ]
    }
    
    general_settings = {
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
    }
except ImportError:
    # Fallback for test environments where logos might not be available
    semantic_theories = {}
    example_range = {}
    general_settings = {}
'''
        
        module_path = os.path.join(self.temp_dir, "logos_test.py")
        with open(module_path, 'w') as f:
            f.write(module_content)
        
        # Create mock flags
        mock_flags = Mock()
        mock_flags.file_path = module_path
        mock_flags.print_constraints = False
        mock_flags.print_z3 = False
        mock_flags.save_output = False
        mock_flags._parsed_args = []
        
        try:
            build_module = BuildModule(mock_flags)
            
            if build_module.semantic_theories:  # Only test if logos is available
                self.assertIn("Logos", build_module.semantic_theories)
                self.assertIn("LOGOS_INTEGRATION_TEST", build_module.example_range)
                
                # Test that we can access theory components
                logos_theory = build_module.semantic_theories["Logos"]
                self.assertIn("semantics", logos_theory)
                self.assertIn("operators", logos_theory)
        except (ImportError, AttributeError):
            # Skip test if logos theory is not available in test environment
            self.skipTest("Logos theory not available in test environment")
    
    def test_exclusion_theory_integration(self):
        """Test integration with real exclusion theory."""
        # Create a minimal exclusion example module
        module_content = '''
try:
    from model_checker.theory_lib import exclusion
    
    semantic_theories = {
        "Exclusion": {
            "semantics": exclusion.WitnessSemantics,
            "proposition": exclusion.WitnessProposition,
            "model": exclusion.WitnessStructure,
            "operators": exclusion.witness_operators
        }
    }
    
    example_range = {
        "EXCLUSION_INTEGRATION_TEST": [
            [],  # premises
            ["p"],  # conclusions
            {"N": 2, "max_time": 1, "expectation": False}  # settings
        ]
    }
    
    general_settings = {
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
    }
except ImportError:
    # Fallback for test environments where exclusion might not be available
    semantic_theories = {}
    example_range = {}
    general_settings = {}
'''
        
        module_path = os.path.join(self.temp_dir, "exclusion_test.py")
        with open(module_path, 'w') as f:
            f.write(module_content)
        
        # Create mock flags
        mock_flags = Mock()
        mock_flags.file_path = module_path
        mock_flags.print_constraints = False
        mock_flags.print_z3 = False
        mock_flags.save_output = False
        mock_flags._parsed_args = []
        
        try:
            build_module = BuildModule(mock_flags)
            
            if build_module.semantic_theories:  # Only test if exclusion is available
                self.assertIn("Exclusion", build_module.semantic_theories)
                self.assertIn("EXCLUSION_INTEGRATION_TEST", build_module.example_range)
                
                # Test that we can access theory components
                exclusion_theory = build_module.semantic_theories["Exclusion"]
                self.assertIn("semantics", exclusion_theory)
                self.assertIn("operators", exclusion_theory)
        except (ImportError, AttributeError):
            # Skip test if exclusion theory is not available in test environment
            self.skipTest("Exclusion theory not available in test environment")


if __name__ == "__main__":
    unittest.main()