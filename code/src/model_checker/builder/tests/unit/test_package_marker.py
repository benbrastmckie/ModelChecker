"""Unit tests for package marker functionality.

Tests the creation and validation of .modelchecker marker files
that identify generated projects as packages.
"""

import os
import tempfile
import unittest
from datetime import datetime
from unittest.mock import patch

# Add src to path for testing
import sys
test_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(test_dir, '..', '..', '..', '..')
sys.path.insert(0, src_dir)

from model_checker.builder.project import BuildProject


class TestPackageMarker(unittest.TestCase):
    """Test .modelchecker marker file creation."""
    
    def setUp(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()
    
    def tearDown(self):
        """Clean up test environment."""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)
    
    def test_marker_creation_with_metadata(self):
        """Test marker file contains required metadata."""
        # Following minimal mocking principle - use real BuildProject
        project = BuildProject('logos')
        
        # Method should now exist and work
        project._create_package_marker(self.temp_dir)
        
        # Verify marker file exists
        marker_path = os.path.join(self.temp_dir, '.modelchecker')
        self.assertTrue(os.path.exists(marker_path))
        
        # Verify content
        with open(marker_path, 'r') as f:
            content = f.read()
            self.assertIn('theory=logos', content)
            self.assertIn('package=true', content)
            self.assertIn('version=1.0', content)
    
    def test_marker_file_format(self):
        """Test marker file has correct format when created."""
        project = BuildProject('logos')
        
        # Test that method now exists
        self.assertTrue(hasattr(project, '_create_package_marker'))
        
        # Create marker and test format
        project._create_package_marker(self.temp_dir)
        
        marker_path = os.path.join(self.temp_dir, '.modelchecker')
        with open(marker_path, 'r') as f:
            lines = f.readlines()
            # First line should be comment
            self.assertTrue(lines[0].startswith('#'))
            # Should have key=value format
            theory_line = next(line for line in lines if line.startswith('theory='))
            self.assertIn('logos', theory_line)
    
    def test_marker_metadata_content(self):
        """Test marker contains theory name and package flag."""
        project = BuildProject('logos')
        
        # Test method existence
        self.assertTrue(hasattr(project, '_create_package_marker'))
        
        # Test different theory
        exclusion_project = BuildProject('exclusion')
        exclusion_project._create_package_marker(self.temp_dir)
        
        marker_path = os.path.join(self.temp_dir, '.modelchecker')
        with open(marker_path, 'r') as f:
            content = f.read()
            self.assertIn('theory=exclusion', content)
            self.assertIn('package=true', content)


if __name__ == '__main__':
    unittest.main()