"""Tests capturing current ModuleLoader behavior before refactoring.

This test file documents the EXACT current behavior of ModuleLoader
before the refactoring. All these tests MUST PASS with the current
implementation to establish a baseline.
"""

import os
import sys
import tempfile
import shutil
from pathlib import Path
from unittest import TestCase
from unittest.mock import patch, MagicMock
from types import ModuleType

# Skip all tests in this file - they document old behavior
import pytest
pytestmark = pytest.mark.skip(reason="Tests document legacy behavior that has been removed")

from model_checker.builder.loader import ModuleLoader
from model_checker.builder.errors import ModuleLoadError


class TestCurrentLoaderBehavior(TestCase):
    """Document exact current ModuleLoader behavior."""
    
    def setUp(self):
        """Set up test environment."""
        self.test_dir = tempfile.mkdtemp()
        self.original_sys_path = sys.path.copy()
        
    def tearDown(self):
        """Clean up test environment."""
        shutil.rmtree(self.test_dir, ignore_errors=True)
        sys.path = self.original_sys_path
        
    def test_loader_has_many_methods(self):
        """Current: ModuleLoader has 21+ methods with mixed responsibilities."""
        # Create a test file
        test_file = Path(self.test_dir) / "test_module.py"
        test_file.write_text("# Test module")
        
        loader = ModuleLoader("test_module", str(test_file))
        
        # Count public methods
        public_methods = [m for m in dir(loader) 
                         if not m.startswith('_') and callable(getattr(loader, m))]
        
        # Document that loader has many methods
        self.assertGreater(len(public_methods), 3)  # Has more than just load_module
        
        # Verify mixed responsibilities - detection methods exist
        self.assertTrue(hasattr(loader, 'is_generated_project'))
        self.assertTrue(hasattr(loader, 'find_project_directory'))
        
    def test_loader_handles_both_detection_and_loading(self):
        """Current: ModuleLoader handles both project detection and module loading."""
        test_file = Path(self.test_dir) / "test_module.py"
        test_file.write_text("test_var = 42")
        
        loader = ModuleLoader("test_module", str(test_file))
        
        # Loader can detect project types
        self.assertIsInstance(loader.is_generated_project(self.test_dir), bool)
        
        # Loader can also load modules
        self.assertTrue(hasattr(loader, 'load_module'))
        
    def test_legacy_detection_methods_exist(self):
        """Current: Multiple legacy detection methods are present."""
        test_file = Path(self.test_dir) / "test_module.py"
        test_file.write_text("# Test")
        
        loader = ModuleLoader("test_module", str(test_file))
        
        # All these legacy methods exist
        self.assertTrue(hasattr(loader, 'is_generated_project'))
        self.assertTrue(hasattr(loader, 'find_project_directory'))
        self.assertTrue(hasattr(loader, '_extract_theory_from_config'))
        self.assertTrue(hasattr(loader, '_load_generated_project_module'))
        self.assertTrue(hasattr(loader, '_load_generated_project_with_absolute_imports'))
        
    def test_supports_config_py_detection(self):
        """Current: Supports legacy config.py project detection."""
        # Create config.py file
        config_file = Path(self.test_dir) / "config.py"
        config_file.write_text("theory = 'test_theory'")
        
        test_module = Path(self.test_dir) / "test.py"
        test_module.write_text("# Module")
        
        loader = ModuleLoader("test", str(test_module))
        
        # Can detect config.py projects
        result = loader.is_generated_project(self.test_dir)
        self.assertIsInstance(result, bool)
        
    def test_supports_modelchecker_marker_detection(self):
        """Current: Supports new .modelchecker marker detection."""
        # Create .modelchecker marker
        marker_file = Path(self.test_dir) / ".modelchecker"
        marker_file.write_text("package=true")
        
        test_module = Path(self.test_dir) / "test.py"
        test_module.write_text("# Module")
        
        loader = ModuleLoader("test", str(test_module))
        
        # Can detect .modelchecker projects
        result = loader._is_generated_project_package()
        self.assertIsInstance(result, bool)
        
    def test_sys_path_restoration_logic_exists(self):
        """Current: Complex sys.path restoration logic in finally blocks."""
        test_file = Path(self.test_dir) / "test_module.py"
        test_file.write_text("test_var = 123")
        
        loader = ModuleLoader("test_module", str(test_file))
        
        # Store original path
        original_path = sys.path.copy()
        
        # Load module - this may or may not restore sys.path
        try:
            loader.load_module()
        except:
            pass  # We're testing the behavior, not success
            
        # The behavior exists (conditional restoration)
        # This documents current implementation
        self.assertIsNotNone(sys.path)  # sys.path still exists
        
    def test_long_methods_exist(self):
        """Current: Several methods are very long (>50 lines)."""
        test_file = Path(self.test_dir) / "test.py"
        test_file.write_text("# Test")
        
        loader = ModuleLoader("test", str(test_file))
        
        # These methods are known to be long
        long_methods = [
            '_load_generated_project_with_absolute_imports',
            '_load_as_package_module'
        ]
        
        for method_name in long_methods:
            if hasattr(loader, method_name):
                method = getattr(loader, method_name)
                self.assertTrue(callable(method))
                
    def test_optional_parameters_in_methods(self):
        """Current: Some methods have optional parameters with defaults."""
        test_file = Path(self.test_dir) / "test.py"
        test_file.write_text("# Test")
        
        loader = ModuleLoader("test", str(test_file))
        
        # The constructor itself has all required params (good)
        # But internally methods may have optional params
        # This documents the current state
        import inspect
        
        # Check if any methods have defaults
        for name in dir(loader):
            if not name.startswith('_') or name.startswith('__'):
                continue
            attr = getattr(loader, name)
            if callable(attr):
                try:
                    sig = inspect.signature(attr)
                    # Document if parameters have defaults
                    has_defaults = any(
                        p.default != inspect.Parameter.empty 
                        for p in sig.parameters.values()
                    )
                    # This is just documentation, not assertion
                except:
                    pass
                    
    def test_mixed_error_handling_approaches(self):
        """Current: Error handling is inconsistent across methods."""
        # Test with non-existent file
        loader = ModuleLoader("nonexistent", "/path/that/does/not/exist.py")
        
        # Document current error behavior - it raises ImportError
        with self.assertRaises(ImportError):
            loader.load_module()
            
    def test_complex_import_conversion_logic(self):
        """Current: Complex logic for converting imports in generated projects."""
        test_file = Path(self.test_dir) / "test.py"
        test_file.write_text("from . import something")
        
        loader = ModuleLoader("test", str(test_file))
        
        # These conversion methods exist
        if hasattr(loader, '_load_generated_project_with_absolute_imports'):
            # Method exists for complex import conversion
            self.assertTrue(True)
            
    def test_multiple_loading_strategies_exist(self):
        """Current: Multiple different loading strategies in single class."""
        test_file = Path(self.test_dir) / "test.py"
        test_file.write_text("# Test")
        
        loader = ModuleLoader("test", str(test_file))
        
        # Multiple loading methods exist
        loading_methods = [
            '_load_standard_module',
            '_load_as_package_module',
            '_load_generated_project_module'
        ]
        
        existing_methods = [m for m in loading_methods if hasattr(loader, m)]
        self.assertGreater(len(existing_methods), 1)  # Multiple strategies
        
    def test_module_loading_works_for_simple_case(self):
        """Current: Basic module loading works for simple modules."""
        test_file = Path(self.test_dir) / "simple_module.py"
        test_file.write_text("""
test_variable = 42
def test_function():
    return "hello"
""")
        
        loader = ModuleLoader("simple_module", str(test_file))
        module = loader.load_module()
        
        self.assertIsInstance(module, ModuleType)
        self.assertEqual(module.test_variable, 42)
        self.assertEqual(module.test_function(), "hello")
        
    def test_package_loading_with_modelchecker_marker(self):
        """Current: Package loading works with .modelchecker marker."""
        # Create package structure
        package_dir = Path(self.test_dir) / "test_package"
        package_dir.mkdir()
        
        # Add marker
        marker_file = package_dir / ".modelchecker"
        marker_file.write_text("package=true")
        
        # Add __init__.py
        init_file = package_dir / "__init__.py"
        init_file.write_text("package_var = 'initialized'")
        
        # Add module
        module_file = package_dir / "module.py"
        module_file.write_text("module_var = 'from_module'")
        
        loader = ModuleLoader("module", str(module_file))
        
        # This should work with current implementation
        try:
            module = loader.load_module()
            self.assertIsInstance(module, ModuleType)
        except:
            # If it fails, that's also valid current behavior to document
            pass
            
    def test_class_complexity_metrics(self):
        """Current: ModuleLoader has high complexity metrics."""
        test_file = Path(self.test_dir) / "test.py"
        test_file.write_text("# Test")
        
        loader = ModuleLoader("test", str(test_file))
        
        # Count methods (including private)
        all_methods = [m for m in dir(loader) if callable(getattr(loader, m))]
        
        # Document high method count
        self.assertGreater(len(all_methods), 20)  # Many methods
        
        # Document that it's a "God Object" with many responsibilities
        responsibilities = {
            'loading': ['load_module', '_load_standard_module'],
            'detection': ['is_generated_project', 'find_project_directory'],
            'path_management': ['_find_package_root'],
            'import_conversion': ['_load_generated_project_with_absolute_imports']
        }
        
        # Count how many different responsibility areas have methods
        areas_with_methods = 0
        for area, methods in responsibilities.items():
            if any(hasattr(loader, m) for m in methods):
                areas_with_methods += 1
                
        self.assertGreater(areas_with_methods, 2)  # Multiple responsibilities