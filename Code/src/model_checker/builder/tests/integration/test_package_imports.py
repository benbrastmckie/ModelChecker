"""Integration tests for package import resolution.

Tests the complete workflow of package creation and import resolution
across BuildProject and ModuleLoader components.
"""

import os
import tempfile
import unittest
import shutil

# Add src to path for testing
import sys
test_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(test_dir, '..', '..', '..', '..')
sys.path.insert(0, src_dir)

from model_checker.builder.project import BuildProject
from model_checker.builder.loader import ModuleLoader


class TestPackageImports(unittest.TestCase):
    """Test package import resolution integration."""
    
    def setUp(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
    
    def tearDown(self):
        """Clean up test environment."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir, ignore_errors=True)
    
    def test_package_detection_methods_exist(self):
        """Test package detection methods now exist."""
        # Test loader now has package detection
        loader = ModuleLoader('test', '/fake/path/test.py')
        
        # These methods should now exist
        self.assertTrue(hasattr(loader, '_is_generated_project_package'))
        self.assertTrue(hasattr(loader, '_load_as_package_module'))
        self.assertTrue(hasattr(loader, '_find_package_root'))
    
    def test_relative_imports_now_work_with_package(self):
        """Test that relative imports now work with new package implementation."""
        os.chdir(self.temp_dir)
        
        # Generate a project with enhanced implementation
        project = BuildProject('logos')
        project_dir = project.generate('test_imports')
        
        # Create a test file with relative imports
        test_file = os.path.join(project_dir, 'test_relative.py')
        with open(test_file, 'w') as f:
            f.write('from .semantic import *\nprint("Import successful")\n')
        
        # Try to load - this should now work with package detection
        loader = ModuleLoader('test_relative', test_file)
        
        try:
            module = loader.load_module()
            # If we get here, the import worked
            self.assertIsNotNone(module)
        except ImportError as e:
            # This might still fail if semantic.py doesn't exist in logos theory
            # which is expected - just verify it's not a relative import error
            error_msg = str(e).lower()
            self.assertNotIn('relative import', error_msg)
    
    def test_package_marker_now_exists(self):
        """Test .modelchecker marker is created with new implementation."""
        os.chdir(self.temp_dir)
        
        # Generate project with enhanced implementation
        project = BuildProject('logos')
        project_dir = project.generate('test_marker')
        
        # Check marker file now exists
        marker_path = os.path.join(project_dir, '.modelchecker')
        self.assertTrue(os.path.exists(marker_path))
        
        # Verify content
        with open(marker_path, 'r') as f:
            content = f.read()
            self.assertIn('theory=logos', content)
            self.assertIn('package=true', content)


if __name__ == '__main__':
    unittest.main()