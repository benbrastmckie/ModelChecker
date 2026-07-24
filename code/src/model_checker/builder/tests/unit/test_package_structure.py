"""Unit tests for package structure functionality.

Tests the creation of proper Python package structures
in generated projects.
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


class TestPackageStructure(unittest.TestCase):
    """Test package structure creation."""
    
    def setUp(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
    
    def tearDown(self):
        """Clean up test environment."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir, ignore_errors=True)
    
    def test_init_file_creation(self):
        """Test __init__.py is created for package structure."""
        project = BuildProject('logos')
        
        # Test that enhanced copy method doesn't exist yet
        # This should pass initially and fail after implementation
        try:
            os.chdir(self.temp_dir)
            project_dir = project.generate('test_package')
            
            # Check if __init__.py exists (it should with current implementation)
            init_path = os.path.join(project_dir, '__init__.py')
            self.assertTrue(os.path.exists(init_path))
            
            # But check that it doesn't have package-specific content yet
            with open(init_path, 'r') as f:
                content = f.read()
                # Should not contain our enhanced package exports yet
                self.assertNotIn('# Re-export main components', content)
                
        except Exception as e:
            self.fail(f"Current project generation failed: {e}")
    
    def test_subpackage_initialization(self):
        """Test nested directories get __init__.py files."""
        project = BuildProject('logos')
        
        # Test that enhanced subpackage method now exists
        self.assertTrue(hasattr(project, '_ensure_subpackages'))
        
        # Create nested structure
        subdir = os.path.join(self.temp_dir, 'subtheories', 'modal')
        os.makedirs(subdir)
        
        # Add Python file
        with open(os.path.join(subdir, 'test.py'), 'w') as f:
            f.write('# test file')
        
        # Call method
        project._ensure_subpackages(self.temp_dir)
        
        # Verify __init__.py was created
        init_path = os.path.join(subdir, '__init__.py')
        self.assertTrue(os.path.exists(init_path))
    
    def test_package_exports_structure(self):
        """Test __init__.py contains proper exports."""
        project = BuildProject('logos')
        
        # Test method existence
        self.assertTrue(hasattr(project, '_create_default_init'))
        
        # Create default init
        init_path = os.path.join(self.temp_dir, '__init__.py')
        project._create_default_init(init_path)
        
        # Verify content
        with open(init_path, 'r') as f:
            content = f.read()
            self.assertIn('__version__', content)
            self.assertIn('__theory__', content)
            self.assertIn('from .semantic import', content)
            self.assertIn('from .operators import', content)


if __name__ == '__main__':
    unittest.main()