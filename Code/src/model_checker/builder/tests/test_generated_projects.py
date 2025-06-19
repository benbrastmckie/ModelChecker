"""Tests for generated project import resolution functionality.

This module tests the BuildModule's ability to handle generated projects
with various structures and import patterns, ensuring the fix for the
"No module named 'project_SNAKE'" error works correctly.
"""

import os
import tempfile
import unittest
import sys
from unittest.mock import patch

# Add src to path for testing
test_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(test_dir, '..', '..', '..')
sys.path.insert(0, src_dir)

from model_checker.builder.module import BuildModule
from model_checker.builder.project import BuildProject


class MockFlags:
    """Mock flags object for testing BuildModule."""
    def __init__(self, file_path):
        self.file_path = file_path


class TestGeneratedProjectImports(unittest.TestCase):
    """Test BuildModule with generated projects."""
    
    def setUp(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
    
    def tearDown(self):
        """Clean up test environment."""
        os.chdir(self.original_cwd)
        # Clean up temp directory
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)
    
    def test_logos_project_generation_and_loading(self):
        """Test generating and loading a logos-based project."""
        os.chdir(self.temp_dir)
        
        # Generate project from logos template
        project = BuildProject('logos')
        project_dir = project.generate('test_logos')
        
        # Test loading examples.py from generated project
        examples_path = os.path.join(project_dir, 'examples.py')
        self.assertTrue(os.path.exists(examples_path), "examples.py should exist in generated project")
        
        # Test BuildModule can load it
        module_flags = MockFlags(examples_path)
        build_module = BuildModule(module_flags)
        
        # Verify it loaded successfully
        self.assertIsNotNone(build_module.module)
        self.assertIsInstance(build_module.example_range, dict)
        self.assertIsInstance(build_module.semantic_theories, dict)
        self.assertGreater(len(build_module.example_range), 0)
    
    def test_default_project_examples_init_loading(self):
        """Test loading examples/__init__.py from default theory project."""
        os.chdir(self.temp_dir)
        
        # Generate project from default template (has examples/ directory)
        project = BuildProject('default')
        project_dir = project.generate('test_default')
        
        # Test loading examples/__init__.py from generated project
        examples_init_path = os.path.join(project_dir, 'examples', '__init__.py')
        self.assertTrue(os.path.exists(examples_init_path), "examples/__init__.py should exist")
        
        # Test BuildModule can load it (this was the original failing case)
        module_flags = MockFlags(examples_init_path)
        build_module = BuildModule(module_flags)
        
        # Verify it loaded successfully
        self.assertIsNotNone(build_module.module)
        self.assertIsInstance(build_module.example_range, dict)
        self.assertIsInstance(build_module.semantic_theories, dict)
    
    def test_generated_project_detection(self):
        """Test the _is_generated_project method."""
        os.chdir(self.temp_dir)
        
        # Create test project
        project = BuildProject('logos')
        project_dir = project.generate('detection_test')
        
        examples_path = os.path.join(project_dir, 'examples.py')
        module_flags = MockFlags(examples_path)
        build_module = BuildModule(module_flags)
        
        # Test detection from project root
        self.assertTrue(build_module._is_generated_project(project_dir))
        
        # Test detection from subdirectory
        subdir = os.path.join(project_dir, 'subtheories', 'modal')
        if os.path.exists(subdir):
            self.assertTrue(build_module._is_generated_project(subdir))
        
        # Test non-generated directory
        self.assertFalse(build_module._is_generated_project('/usr/bin'))
    
    def test_find_project_directory(self):
        """Test the _find_project_directory method."""
        os.chdir(self.temp_dir)
        
        # Create test project
        project = BuildProject('logos')
        project_dir = project.generate('directory_test')
        
        examples_path = os.path.join(project_dir, 'examples.py')
        module_flags = MockFlags(examples_path)
        build_module = BuildModule(module_flags)
        
        # Test finding from project root
        found_dir = build_module._find_project_directory(project_dir)
        self.assertEqual(found_dir, project_dir)
        
        # Test finding from subdirectory
        subdir = os.path.join(project_dir, 'subtheories', 'modal')
        if os.path.exists(subdir):
            found_dir = build_module._find_project_directory(subdir)
            self.assertEqual(found_dir, project_dir)
    
    def test_sys_path_configuration(self):
        """Test that sys.path is properly configured for generated projects."""
        os.chdir(self.temp_dir)
        
        # Store original sys.path
        original_path = sys.path.copy()
        
        try:
            # Generate project
            project = BuildProject('logos')
            project_dir = project.generate('path_test')
            
            examples_path = os.path.join(project_dir, 'examples.py')
            module_flags = MockFlags(examples_path)
            
            # Create BuildModule - this should modify sys.path
            build_module = BuildModule(module_flags)
            
            # Check that project directory and its parent are in sys.path
            project_parent = os.path.dirname(project_dir)
            self.assertIn(project_dir, sys.path, "Project directory should be in sys.path")
            self.assertIn(project_parent, sys.path, "Project parent should be in sys.path")
            
        finally:
            # Restore original sys.path
            sys.path[:] = original_path
    
    def test_backward_compatibility(self):
        """Test that existing theory_lib functionality still works."""
        # Test loading from theory_lib (non-generated project)
        theory_lib_path = os.path.join(src_dir, 'model_checker', 'theory_lib', 'logos', 'examples.py')
        
        if os.path.exists(theory_lib_path):
            module_flags = MockFlags(theory_lib_path)
            build_module = BuildModule(module_flags)
            
            # Verify it loads successfully
            self.assertIsNotNone(build_module.module)
            self.assertIsInstance(build_module.example_range, dict)
            self.assertIsInstance(build_module.semantic_theories, dict)
    
    def test_error_handling_for_generated_projects(self):
        """Test error handling for generated projects."""
        os.chdir(self.temp_dir)
        
        # Create a generated project directory manually
        project_dir = os.path.join(self.temp_dir, 'project_error_test')
        os.makedirs(project_dir)
        
        # Create a problematic Python file
        bad_file = os.path.join(project_dir, 'bad_examples.py')
        with open(bad_file, 'w') as f:
            f.write("from ..nonexistent_module import something\n")
        
        module_flags = MockFlags(bad_file)
        
        # This should raise an ImportError with helpful message for generated projects
        with self.assertRaises(ImportError) as cm:
            BuildModule(module_flags)
        
        error_message = str(cm.exception)
        self.assertIn("generated project", error_message.lower())


class TestProjectStructureFlexibility(unittest.TestCase):
    """Test that the fix works with various project structures."""
    
    def setUp(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
    
    def tearDown(self):
        """Clean up test environment."""
        os.chdir(self.original_cwd)
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)
    
    def test_multiple_theory_templates(self):
        """Test that multiple theory templates work as project bases."""
        os.chdir(self.temp_dir)
        
        # Test theories that should exist
        test_theories = ['logos', 'default']
        theory_lib_dir = os.path.join(src_dir, 'model_checker', 'theory_lib')
        available_theories = [d for d in os.listdir(theory_lib_dir) 
                            if os.path.isdir(os.path.join(theory_lib_dir, d)) 
                            and not d.startswith('__')]
        
        for theory in test_theories:
            if theory in available_theories:
                with self.subTest(theory=theory):
                    # Generate project from this theory
                    project = BuildProject(theory)
                    project_dir = project.generate(f'test_{theory}')
                    
                    # Find loadable module (examples.py or examples/__init__.py)
                    examples_py = os.path.join(project_dir, 'examples.py')
                    examples_init = os.path.join(project_dir, 'examples', '__init__.py')
                    
                    loadable_path = None
                    if os.path.exists(examples_py):
                        loadable_path = examples_py
                    elif os.path.exists(examples_init):
                        loadable_path = examples_init
                    
                    self.assertIsNotNone(loadable_path, f"No loadable examples found for {theory}")
                    
                    # Test that it loads successfully
                    module_flags = MockFlags(loadable_path)
                    try:
                        build_module = BuildModule(module_flags)
                        self.assertIsNotNone(build_module.module)
                    except Exception as e:
                        self.fail(f"Failed to load {theory} project: {e}")


if __name__ == '__main__':
    unittest.main()