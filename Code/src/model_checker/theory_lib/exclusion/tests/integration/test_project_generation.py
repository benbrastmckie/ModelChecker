"""Test project generation for the exclusion theory.

This test ensures that projects can be generated from the exclusion theory
and that the generated projects work correctly with relative imports.
"""

import os
import sys
import tempfile
import unittest

# Add src to path for testing
test_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(test_dir, '..', '..', '..', '..', '..')
sys.path.insert(0, src_dir)

from model_checker.builder.project import BuildProject


class TestExclusionProjectGeneration(unittest.TestCase):
    """Test that the exclusion theory can generate working projects."""
    
    def test_exclusion_project_generation(self):
        """Test that projects can be generated from the exclusion theory."""
        with tempfile.TemporaryDirectory() as temp_dir:
            # Test that BuildProject works with exclusion theory
            project = BuildProject('exclusion')
            project_dir = project.generate('test_exclusion', temp_dir)
            
            # Verify the project was created
            self.assertTrue(os.path.exists(project_dir))
            
            # Verify essential files exist
            self.assertTrue(os.path.exists(os.path.join(project_dir, '__init__.py')))
            self.assertTrue(os.path.exists(os.path.join(project_dir, '.modelchecker')))
            self.assertTrue(os.path.exists(os.path.join(project_dir, 'semantic.py')))
            self.assertTrue(os.path.exists(os.path.join(project_dir, 'operators.py')))
            self.assertTrue(os.path.exists(os.path.join(project_dir, 'examples.py')))
            
            # Verify marker contains correct theory
            with open(os.path.join(project_dir, '.modelchecker')) as f:
                content = f.read()
                self.assertIn('theory=exclusion', content)
                self.assertIn('package=true', content)
    
    def test_exclusion_has_required_files(self):
        """Test that exclusion theory has all required files for project generation."""
        # Get the exclusion theory directory
        theory_dir = os.path.join(src_dir, 'model_checker', 'theory_lib', 'exclusion')
        
        # Check required files exist
        required_files = ['__init__.py', 'semantic.py', 'operators.py', 'examples.py']
        for file_name in required_files:
            file_path = os.path.join(theory_dir, file_name)
            self.assertTrue(
                os.path.exists(file_path),
                f"Required file {file_name} missing in exclusion theory"
            )
    
    def test_exclusion_project_structure(self):
        """Test that generated exclusion projects have correct structure."""
        with tempfile.TemporaryDirectory() as temp_dir:
            project = BuildProject('exclusion')
            project_dir = project.generate('test_structure', temp_dir)
            
            # Check if the __init__.py is appropriate for the theory
            init_path = os.path.join(project_dir, '__init__.py')
            with open(init_path) as f:
                content = f.read()
                # Exclusion theory should have witness-related imports
                self.assertIn('WitnessSemantics', content)
                self.assertIn('witness_operators', content)


if __name__ == '__main__':
    unittest.main()