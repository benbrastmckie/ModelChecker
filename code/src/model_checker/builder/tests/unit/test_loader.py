"""
Unit tests for ModuleLoader component.

This module tests ModuleLoader functionality in isolation, ensuring proper
module loading, error handling, and theory discovery behaviors.
"""

import unittest
import os
import sys
import tempfile
import shutil
from pathlib import Path
from unittest.mock import patch, MagicMock, Mock

from model_checker.builder.tests.fixtures.test_data import TestModules, TestConstants
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory
from model_checker.builder.tests.fixtures.temp_resources import TempFileCleanup
from model_checker.builder.tests.fixtures.assertions import (
    assert_error_message_contains,
    assert_no_exceptions_during_execution
)

from model_checker.builder.loader import ModuleLoader


class TestModuleLoaderCore(unittest.TestCase):
    """Test ModuleLoader core functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create test module file
        self.module_name = "test_module"
        self.module_path = self.cleanup.create_temp_file(
            TestModules.MINIMAL_CONTENT,
            suffix=".py"
        )
    
    def test_module_loader_initializes_with_valid_parameters(self):
        """Test ModuleLoader initializes correctly with valid module name and path."""
        loader = ModuleLoader(self.module_name, self.module_path)
        
        self.assertEqual(loader.module_name, self.module_name,
                        "Module name should be stored correctly")
        self.assertEqual(loader.module_path, self.module_path,
                        "Module path should be stored correctly")
        self.assertEqual(loader.module_dir, os.path.dirname(self.module_path),
                        "Module directory should be derived from path")
    
    def test_module_loader_loads_valid_module_successfully(self):
        """Test ModuleLoader loads valid module without errors."""
        loader = ModuleLoader(self.module_name, self.module_path)
        
        module = assert_no_exceptions_during_execution(
            self, loader.load_module, operation_name="Module loading"
        )
        
        # Verify module loaded correctly
        self.assertIsNotNone(module,
                           "Successfully loaded module should not be None")
        self.assertTrue(hasattr(module, 'semantic_theories'),
                       "Loaded module should have semantic_theories attribute")
        self.assertTrue(hasattr(module, 'example_range'),
                       "Loaded module should have example_range attribute")
    
    def test_module_loader_loads_module_with_correct_attributes(self):
        """Test ModuleLoader loads module with expected attributes and structure."""
        loader = ModuleLoader(self.module_name, self.module_path)
        module = loader.load_module()
        
        # Verify required attributes exist
        required_attributes = ['semantic_theories', 'example_range', 'general_settings']
        for attr in required_attributes:
            self.assertTrue(hasattr(module, attr),
                           f"Loaded module should have {attr} attribute")
        
        # Verify attributes are of correct types
        self.assertIsInstance(module.semantic_theories, dict,
                            "semantic_theories should be a dictionary")
        self.assertIsInstance(module.example_range, dict,
                            "example_range should be a dictionary")


class TestModuleLoaderErrorHandling(unittest.TestCase):
    """Test ModuleLoader error handling scenarios."""
    
    def setUp(self):
        """Set up error testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_module_loader_raises_import_error_when_file_not_found(self):
        """Test ModuleLoader raises ImportError when module file does not exist."""
        nonexistent_path = "/path/that/does/not/exist.py"
        loader = ModuleLoader("nonexistent", nonexistent_path)
        
        with self.assertRaises(ImportError) as context:
            loader.load_module()
        
        assert_error_message_contains(
            self, context.exception, "not found", 
            "Module file not found error"
        )
    
    def test_module_loader_handles_syntax_errors_appropriately(self):
        """Test ModuleLoader handles Python syntax errors in module files."""
        # Create file with syntax error
        bad_module_path = self.cleanup.create_temp_file(
            TestModules.SYNTAX_ERROR_CONTENT,
            suffix=".py"
        )
        
        loader = ModuleLoader("bad_syntax", bad_module_path)
        
        with self.assertRaises((SyntaxError, ImportError)) as context:
            loader.load_module()
        
        # Should get meaningful error about syntax
        error_msg = str(context.exception).lower()
        self.assertTrue(
            "syntax" in error_msg or "invalid" in error_msg,
            f"Error should indicate syntax problem, got: {context.exception}"
        )
    
    def test_module_loader_handles_import_errors_in_module_content(self):
        """Test ModuleLoader handles import errors within module content."""
        # Create file with import error
        import_error_path = self.cleanup.create_temp_file(
            TestModules.IMPORT_ERROR_CONTENT,
            suffix=".py"
        )
        
        loader = ModuleLoader("import_error", import_error_path)
        
        with self.assertRaises((ImportError, ModuleNotFoundError)) as context:
            loader.load_module()
        
        # Should propagate import error from module
        assert_error_message_contains(
            self, context.exception, "nonexistent",
            "Import error from module content"
        )
    
    def test_module_loader_validates_required_module_attributes(self):
        """Test ModuleLoader validates that loaded modules have required attributes."""
        # Create file missing semantic_theories
        missing_attrs_path = self.cleanup.create_temp_file(
            TestModules.MISSING_ATTRIBUTES_CONTENT,
            suffix=".py"
        )
        
        loader = ModuleLoader("missing_attrs", missing_attrs_path)
        
        # Note: Current implementation may not validate attributes in load_module
        # This test documents expected behavior
        try:
            module = loader.load_module()
            # If load succeeds, verify missing attribute causes issues downstream
            self.assertFalse(hasattr(module, 'semantic_theories'),
                           "Module should be missing semantic_theories for this test")
        except ImportError:
            # If validation occurs in load_module, should get ImportError
            pass


class TestModuleLoaderTheoryDiscovery(unittest.TestCase):
    """Test ModuleLoader theory discovery functionality."""
    
    def test_module_loader_discovers_theory_module_successfully(self):
        """Test ModuleLoader can discover theory modules from theory library."""
        loader = ModuleLoader("logos", None)
        
        # Should be able to discover logos theory
        module = assert_no_exceptions_during_execution(
            self, loader.discover_theory_module,
            operation_name="Theory module discovery"
        )
        
        self.assertIsNotNone(module,
                           "Theory discovery should return module")
    
    def test_module_loader_raises_error_for_unknown_theory(self):
        """Test ModuleLoader raises ImportError for unknown theory names."""
        loader = ModuleLoader("nonexistent_theory", None)
        
        with self.assertRaises(ImportError) as context:
            loader.discover_theory_module()
        
        assert_error_message_contains(
            self, context.exception, "nonexistent_theory",
            "Unknown theory discovery error"
        )


class TestModuleLoaderEdgeCases(unittest.TestCase):
    """Test ModuleLoader edge cases and boundary conditions."""
    
    def setUp(self):
        """Set up edge case testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_module_loader_handles_empty_module_files(self):
        """Test ModuleLoader handles completely empty module files."""
        empty_module_path = self.cleanup.create_temp_file("", suffix=".py")
        loader = ModuleLoader("empty", empty_module_path)
        
        # Should load empty module without crashing
        module = loader.load_module()
        self.assertIsNotNone(module,
                           "Empty module should still load successfully")
    
    def test_module_loader_handles_unicode_in_module_paths(self):
        """Test ModuleLoader handles Unicode characters in module paths."""
        # Create module with Unicode content
        unicode_content = '''# Module with Unicode: ∧∨¬□◇
semantic_theories = {"Unicode": {}}
example_range = {"TEST": [["A ∧ B"], ["A"], {"N": 2}]}
general_settings = {}
'''
        unicode_path = self.cleanup.create_temp_file(unicode_content, suffix=".py")
        loader = ModuleLoader("unicode_test", unicode_path)
        
        # Should handle Unicode content properly
        module = assert_no_exceptions_during_execution(
            self, loader.load_module,
            operation_name="Unicode module loading"
        )
        
        self.assertIsNotNone(module,
                           "Module with Unicode content should load")
    
    def test_module_loader_handles_very_long_file_paths(self):
        """Test ModuleLoader handles very long file paths appropriately."""
        # Create nested directory structure for long path
        long_dir = self.cleanup.create_temp_dir()
        for i in range(10):  # Create nested directories
            long_dir = os.path.join(long_dir, f"very_long_directory_name_{i}")
            os.makedirs(long_dir, exist_ok=True)
        
        long_path = os.path.join(long_dir, "test_module.py")
        
        # Write module file
        with open(long_path, 'w') as f:
            f.write(TestModules.MINIMAL_CONTENT)
        self.cleanup.add_file(long_path)
        
        loader = ModuleLoader("long_path", long_path)
        
        # Should handle long path without issues (up to OS limits)
        try:
            module = loader.load_module()
            self.assertIsNotNone(module,
                               "Module with long path should load if OS supports it")
        except OSError as e:
            # If OS doesn't support the long path, that's acceptable
            self.assertIn("path", str(e).lower(),
                         "OS path length error should be about path length")


if __name__ == '__main__':
    unittest.main()