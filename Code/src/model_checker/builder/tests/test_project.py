"""Tests for the BuildProject class."""

import unittest
import os
import tempfile
import shutil
from unittest.mock import Mock, patch

from model_checker.builder.project import BuildProject

class TestBuildProject(unittest.TestCase):
    """Test the BuildProject class."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Create a temporary directory for testing
        self.temp_dir = tempfile.mkdtemp()
        
    def tearDown(self):
        """Clean up test fixtures."""
        # Remove the temporary directory
        shutil.rmtree(self.temp_dir)
    
    def test_project_initialization_default(self):
        """Test that BuildProject initializes with logos theory."""
        builder = BuildProject()
        self.assertEqual(builder.theory, 'logos')
        self.assertTrue(os.path.exists(builder.source_dir))
    
    def test_project_initialization_logos(self):
        """Test that BuildProject initializes with logos theory."""
        builder = BuildProject('logos')
        self.assertEqual(builder.theory, 'logos')
        self.assertTrue(os.path.exists(builder.source_dir))
        self.assertIn('logos', builder.source_dir)
    
    def test_logos_project_generation(self):
        """Test that a logos project can be generated successfully."""
        builder = BuildProject('logos')
        project_path = builder.generate('test_logos', self.temp_dir)
        
        # Verify the project was created
        self.assertTrue(os.path.exists(project_path))
        self.assertTrue(os.path.isdir(project_path))
        
        # Verify modular structure was copied
        subtheories_path = os.path.join(project_path, 'subtheories')
        self.assertTrue(os.path.exists(subtheories_path))
        
        # Verify specific subtheories exist
        for subtheory in ['extensional', 'modal', 'constitutive', 'counterfactual']:
            subtheory_path = os.path.join(subtheories_path, subtheory)
            self.assertTrue(os.path.exists(subtheory_path))
            
            # Verify operators.py exists in each subtheory
            operators_path = os.path.join(subtheory_path, 'operators.py')
            self.assertTrue(os.path.exists(operators_path))
    
    def test_invalid_theory_raises_error(self):
        """Test that invalid theory names raise FileNotFoundError."""
        with self.assertRaises(FileNotFoundError):
            BuildProject('nonexistent_theory')

if __name__ == "__main__":
    unittest.main()