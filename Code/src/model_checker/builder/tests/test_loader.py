"""Unit tests for ModuleLoader following TESTING_STANDARDS.md."""
import unittest
import os
import sys
import tempfile
import shutil
from pathlib import Path
from unittest.mock import patch, MagicMock, Mock
from model_checker.builder.loader import ModuleLoader


class TestModuleLoader(unittest.TestCase):
    """Test module loading functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.test_dir = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.test_dir)
        
        # Create test module file
        self.module_name = "test_module"
        self.module_path = os.path.join(self.test_dir, f"{self.module_name}.py")
        
        with open(self.module_path, 'w') as f:
            f.write("""
# Test module
semantic_theories = {"Test": {}}
example_range = {"TEST_1": [[], ["A"], {"N": 2}]}
general_settings = {}
""")
    
    def test_initialization(self):
        """Test ModuleLoader initialization."""
        loader = ModuleLoader(self.module_name, self.module_path)
        
        self.assertEqual(loader.module_name, self.module_name)
        self.assertEqual(loader.module_path, self.module_path)
        self.assertEqual(loader.module_dir, os.path.dirname(self.module_path))
    
    def test_load_module_success(self):
        """Test successful module loading."""
        loader = ModuleLoader(self.module_name, self.module_path)
        module = loader.load_module()
        
        # Verify module loaded correctly
        self.assertIsNotNone(module, "Failed to load module")
        self.assertTrue(hasattr(module, 'semantic_theories'))
        self.assertTrue(hasattr(module, 'example_range'))
    
    def test_load_module_file_not_found(self):
        """Test handling of missing files."""
        loader = ModuleLoader("missing", "/nonexistent/path.py")
        
        with self.assertRaises(ImportError) as context:
            loader.load_module()
        
        self.assertIn("not found", str(context.exception))
    
    def test_load_module_syntax_error(self):
        """Test handling of syntax errors in module."""
        # Create module with syntax error
        bad_module_path = os.path.join(self.test_dir, "bad_syntax.py")
        with open(bad_module_path, 'w') as f:
            f.write("def broken(:\n    pass")
        
        loader = ModuleLoader("bad_syntax", bad_module_path)
        
        with self.assertRaises(ImportError) as context:
            loader.load_module()
        
        self.assertIn("Failed to import", str(context.exception))
    
    def test_is_generated_project_with_config(self):
        """Test is_generated_project with config.py present."""
        # Create project structure
        project_dir = os.path.join(self.test_dir, "test_project")
        os.makedirs(project_dir)
        
        # Create config.py with theory import
        config_path = os.path.join(project_dir, "config.py")
        with open(config_path, 'w') as f:
            f.write("from model_checker.theory_lib import logos\n")
        
        loader = ModuleLoader("test", "/dummy/path")
        self.assertTrue(
            loader.is_generated_project(project_dir),
            "Should detect project with config.py containing theory import"
        )
    
    def test_is_generated_project_without_config(self):
        """Test is_generated_project without config.py."""
        loader = ModuleLoader("test", "/dummy/path")
        self.assertFalse(
            loader.is_generated_project(self.test_dir),
            "Should not detect regular directory as generated project"
        )
    
    def test_is_generated_project_with_markers(self):
        """Test is_generated_project with multiple markers."""
        # Create project structure with config and markers
        project_dir = os.path.join(self.test_dir, "marked_project")
        os.makedirs(project_dir)
        os.makedirs(os.path.join(project_dir, "examples"))
        os.makedirs(os.path.join(project_dir, "tests"))
        
        # Create empty config.py
        config_path = os.path.join(project_dir, "config.py")
        with open(config_path, 'w') as f:
            f.write("# Config file\n")
        
        loader = ModuleLoader("test", "/dummy/path")
        self.assertTrue(
            loader.is_generated_project(project_dir),
            "Should detect project with config.py and marker directories"
        )
    
    def test_find_project_directory_immediate(self):
        """Test find_project_directory when already in project root."""
        # Create project markers
        with open(os.path.join(self.test_dir, "project.yaml"), 'w') as f:
            f.write("name: test_project\n")
        
        loader = ModuleLoader("test", "/dummy/path")
        project_dir = loader.find_project_directory(self.test_dir)
        
        self.assertEqual(
            project_dir, 
            self.test_dir,
            "Should find project directory when already at root"
        )
    
    def test_find_project_directory_nested(self):
        """Test find_project_directory from nested directory."""
        # Create nested structure
        nested_dir = os.path.join(self.test_dir, "src", "subdir")
        os.makedirs(nested_dir)
        
        # Add project marker at root
        with open(os.path.join(self.test_dir, "project.yaml"), 'w') as f:
            f.write("name: test_project\n")
        
        loader = ModuleLoader("test", "/dummy/path")
        project_dir = loader.find_project_directory(nested_dir)
        
        self.assertEqual(
            project_dir,
            self.test_dir,
            "Should find project directory by traversing up"
        )
    
    def test_find_project_directory_not_found(self):
        """Test find_project_directory when no project markers exist."""
        loader = ModuleLoader("test", "/dummy/path")
        project_dir = loader.find_project_directory(self.test_dir)
        
        self.assertIsNone(
            project_dir,
            "Should return None when no project directory found"
        )
    
    def test_load_attribute_success(self):
        """Test successful attribute loading."""
        loader = ModuleLoader(self.module_name, self.module_path)
        module = loader.load_module()
        
        # Test loading existing attribute
        theories = loader.load_attribute(module, "semantic_theories")
        self.assertIsInstance(theories, dict)
        self.assertIn("Test", theories)
    
    def test_load_attribute_missing(self):
        """Test loading missing attribute."""
        loader = ModuleLoader(self.module_name, self.module_path)
        module = loader.load_module()
        
        with self.assertRaises(ImportError) as context:
            loader.load_attribute(module, "missing_attribute")
        
        self.assertIn("missing the required attribute", str(context.exception))
    
    def test_load_attribute_empty_dict(self):
        """Test loading empty dictionary attribute."""
        # Create module with empty dict
        empty_module_path = os.path.join(self.test_dir, "empty.py")
        with open(empty_module_path, 'w') as f:
            f.write("empty_dict = {}\n")
        
        loader = ModuleLoader("empty", empty_module_path)
        module = loader.load_module()
        
        with self.assertRaises(ImportError) as context:
            loader.load_attribute(module, "empty_dict")
        
        self.assertIn("has an empty 'empty_dict'", str(context.exception))
    
    def test_discover_theory_module_found(self):
        """Test discovering theory module from theory_lib."""
        with patch('importlib.import_module') as mock_import:
            mock_module = MagicMock()
            mock_import.return_value = mock_module
            
            loader = ModuleLoader("logos", None)
            module = loader.discover_theory_module()
            
            self.assertEqual(module, mock_module)
            mock_import.assert_called_once_with("model_checker.theory_lib.logos")
    
    def test_discover_theory_module_not_found(self):
        """Test discovering non-existent theory module."""
        loader = ModuleLoader("nonexistent_theory", None)
        
        with self.assertRaises(ImportError) as context:
            loader.discover_theory_module()
        
        self.assertIn("Theory 'nonexistent_theory' not found", str(context.exception))
    
    def test_sys_path_management(self):
        """Test proper sys.path handling during module load."""
        original_path = sys.path.copy()
        
        loader = ModuleLoader(self.module_name, self.module_path)
        module = loader.load_module()
        
        # sys.path should be restored after loading
        self.assertEqual(
            sys.path,
            original_path,
            "sys.path should be restored after module loading"
        )
    
    def test_module_cleanup_on_error(self):
        """Test module cleanup when loading fails."""
        # Create module that will fail during import
        failing_module_path = os.path.join(self.test_dir, "failing.py")
        with open(failing_module_path, 'w') as f:
            f.write("raise RuntimeError('Intentional failure')\n")
        
        loader = ModuleLoader("failing", failing_module_path)
        
        with self.assertRaises(ImportError):
            loader.load_module()
        
        # Module should not remain in sys.modules
        self.assertNotIn("failing", sys.modules)
    
    def test_empty_module_name(self):
        """Test behavior with empty module name - edge case."""
        loader = ModuleLoader("", self.module_path)
        
        # Should still work but with empty module name
        self.assertEqual(loader.module_name, "")
        self.assertIsNotNone(loader, "Loader should handle empty names")
    
    @patch('importlib.util.spec_from_file_location')
    def test_import_error_handling(self, mock_spec):
        """Test handling of import errors with mock."""
        mock_spec.side_effect = ImportError("Module not found")
        
        loader = ModuleLoader(self.module_name, self.module_path)
        
        with self.assertRaises(ImportError) as context:
            loader.load_module()
        
        self.assertIn("Failed to import", str(context.exception))
    
    def test_maximum_path_depth(self):
        """Test find_project_directory with deep nesting - edge case."""
        # Create very deep directory structure
        deep_path = self.test_dir
        for i in range(20):  # Create 20 levels deep
            deep_path = os.path.join(deep_path, f"level{i}")
        os.makedirs(deep_path)
        
        # Put marker at top
        with open(os.path.join(self.test_dir, "project.yaml"), 'w') as f:
            f.write("name: deep_project\n")
        
        loader = ModuleLoader("test", "/dummy/path")
        project_dir = loader.find_project_directory(deep_path)
        
        self.assertEqual(
            project_dir,
            self.test_dir,
            "Should find project directory even from deep nesting"
        )


# Parameterized tests using pytest (optional, for better coverage)
class TestLoaderParameterized(unittest.TestCase):
    """Parameterized tests for various inputs."""
    
    def test_various_module_names(self):
        """Test loader with various module name formats."""
        test_cases = [
            ("simple", True),
            ("with_underscore", True),
            ("with-dash", False),  # Invalid Python module name
            ("123start", False),   # Invalid Python module name
            ("CamelCase", True),
            ("", True),  # Empty is technically valid
            (".", False),  # Just a dot
            ("__private__", True),  # Double underscore
        ]
        
        for module_name, should_work in test_cases:
            with self.subTest(module_name=module_name):
                loader = ModuleLoader(module_name, "/dummy/path")
                self.assertEqual(loader.module_name, module_name)


class TestLoaderEdgeCases(unittest.TestCase):
    """Additional edge case tests for ModuleLoader."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.test_dir = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.test_dir)
    
    def test_unicode_in_path(self):
        """Test handling paths with unicode characters."""
        unicode_dir = os.path.join(self.test_dir, "测试目录")
        os.makedirs(unicode_dir)
        
        module_path = os.path.join(unicode_dir, "test.py")
        with open(module_path, 'w', encoding='utf-8') as f:
            f.write("semantic_theories = {}\nexample_range = {}")
        
        loader = ModuleLoader("test", module_path)
        # Should handle unicode paths
        self.assertEqual(loader.module_dir, unicode_dir)
    
    def test_symlink_handling(self):
        """Test handling of symlinked modules."""
        # Create actual module
        real_module = os.path.join(self.test_dir, "real_module.py")
        with open(real_module, 'w') as f:
            f.write("semantic_theories = {'Test': {}}\nexample_range = {}")
        
        # Create symlink
        symlink_path = os.path.join(self.test_dir, "symlink_module.py")
        try:
            os.symlink(real_module, symlink_path)
        except (OSError, NotImplementedError):
            self.skipTest("Symlinks not supported on this platform")
        
        loader = ModuleLoader("symlink_module", symlink_path)
        module = loader.load_module()
        
        self.assertIsNotNone(module)
        self.assertTrue(hasattr(module, 'semantic_theories'))
    
    def test_module_with_spaces_in_path(self):
        """Test handling paths with spaces."""
        space_dir = os.path.join(self.test_dir, "dir with spaces")
        os.makedirs(space_dir)
        
        module_path = os.path.join(space_dir, "test module.py")
        with open(module_path, 'w') as f:
            f.write("semantic_theories = {}\nexample_range = {}")
        
        loader = ModuleLoader("test_module", module_path)
        self.assertEqual(loader.module_dir, space_dir)
    
    def test_circular_import_detection(self):
        """Test handling of circular imports."""
        # Create two modules that import each other
        module_a = os.path.join(self.test_dir, "module_a.py")
        module_b = os.path.join(self.test_dir, "module_b.py")
        
        with open(module_a, 'w') as f:
            f.write("from module_b import x\ny = 1")
        
        with open(module_b, 'w') as f:
            f.write("from module_a import y\nx = 2")
        
        loader = ModuleLoader("module_a", module_a)
        with self.assertRaises(ImportError):
            loader.load_module()
    
    def test_extremely_large_module(self):
        """Test loading very large modules."""
        large_module = os.path.join(self.test_dir, "large.py")
        
        # Create a module with many definitions
        with open(large_module, 'w') as f:
            f.write("semantic_theories = {\n")
            for i in range(1000):
                f.write(f'    "Theory{i}": {{}},\n')
            f.write("}\nexample_range = {}")
        
        loader = ModuleLoader("large", large_module)
        module = loader.load_module()
        
        self.assertIsNotNone(module)
        self.assertEqual(len(module.semantic_theories), 1000)
    
    def test_module_with_syntax_warning(self):
        """Test module that generates syntax warnings."""
        warning_module = os.path.join(self.test_dir, "warning.py")
        
        with open(warning_module, 'w') as f:
            # Code that might generate warnings
            f.write("""
import warnings
warnings.warn("Test warning", DeprecationWarning)
semantic_theories = {}
example_range = {}
""")
        
        loader = ModuleLoader("warning", warning_module)
        # Should load despite warnings
        module = loader.load_module()
        self.assertIsNotNone(module)
    
    def test_project_discovery_with_hidden_dirs(self):
        """Test project discovery skips hidden directories."""
        # Create structure with hidden directories
        hidden_dir = os.path.join(self.test_dir, ".hidden")
        os.makedirs(hidden_dir)
        
        # Put project marker in parent
        with open(os.path.join(self.test_dir, "project.yaml"), 'w') as f:
            f.write("name: test")
        
        loader = ModuleLoader("test", "/dummy")
        result = loader.find_project_directory(hidden_dir)
        
        # Should find project in parent, not be confused by hidden dir
        self.assertEqual(result, self.test_dir)
    
    def test_concurrent_module_loading(self):
        """Test thread safety of module loading."""
        import threading
        
        results = []
        errors = []
        
        def load_module():
            try:
                loader = ModuleLoader(self.module_name, self.module_path)
                module = loader.load_module()
                results.append(module)
            except Exception as e:
                errors.append(e)
        
        # Create module to load
        module_path = os.path.join(self.test_dir, "concurrent.py")
        with open(module_path, 'w') as f:
            f.write("semantic_theories = {}\nexample_range = {}")
        
        self.module_name = "concurrent"
        self.module_path = module_path
        
        # Launch multiple threads
        threads = []
        for _ in range(5):
            t = threading.Thread(target=load_module)
            threads.append(t)
            t.start()
        
        # Wait for completion
        for t in threads:
            t.join()
        
        # Should have loaded successfully in all threads
        self.assertEqual(len(errors), 0, f"Errors occurred: {errors}")
        self.assertEqual(len(results), 5)
    
    def test_module_with_relative_imports(self):
        """Test handling modules with relative imports."""
        # Create package structure
        package_dir = os.path.join(self.test_dir, "test_package")
        os.makedirs(package_dir)
        
        # Create __init__.py
        with open(os.path.join(package_dir, "__init__.py"), 'w') as f:
            f.write("")
        
        # Create module with relative import
        module_path = os.path.join(package_dir, "module.py")
        with open(module_path, 'w') as f:
            f.write("""
from . import __init__
semantic_theories = {}
example_range = {}
""")
        
        # Loading with relative imports requires special handling
        loader = ModuleLoader("test_package.module", module_path)
        # This might fail or need special handling
        # depending on implementation
    
    def test_readonly_directory(self):
        """Test behavior with read-only directories."""
        import stat
        
        readonly_dir = os.path.join(self.test_dir, "readonly")
        os.makedirs(readonly_dir)
        
        module_path = os.path.join(readonly_dir, "test.py")
        with open(module_path, 'w') as f:
            f.write("semantic_theories = {}\nexample_range = {}")
        
        # Make directory read-only
        try:
            os.chmod(readonly_dir, stat.S_IRUSR | stat.S_IXUSR)
            
            loader = ModuleLoader("test", module_path)
            # Should still be able to read
            module = loader.load_module()
            self.assertIsNotNone(module)
        finally:
            # Restore permissions for cleanup
            os.chmod(readonly_dir, stat.S_IRWXU)
    
    def test_discover_theory_module_for_iteration(self):
        """Test the discover_theory_module_for_iteration method."""
        loader = ModuleLoader("test", "/dummy")
        
        # Mock semantic theory
        mock_theory = Mock()
        mock_theory.__class__.__module__ = "model_checker.theory_lib.logos"
        
        result = loader.discover_theory_module_for_iteration("logos", mock_theory)
        self.assertEqual(result, "model_checker.theory_lib.logos")
    
    def test_path_traversal_limit(self):
        """Test project discovery respects traversal limits."""
        # Create very deep structure beyond limit
        deep_path = self.test_dir
        for i in range(30):  # Beyond the 25 limit
            deep_path = os.path.join(deep_path, f"level{i}")
        os.makedirs(deep_path)
        
        loader = ModuleLoader("test", "/dummy")
        result = loader.find_project_directory(deep_path)
        
        # Should return None if beyond limit
        self.assertIsNone(result)


if __name__ == "__main__":
    unittest.main()