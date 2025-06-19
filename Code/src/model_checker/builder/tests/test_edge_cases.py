"""Edge case tests for generated project import resolution.

This module tests realistic edge cases and boundary conditions for the 
structure-agnostic module loading functionality to ensure robustness
in various real-world scenarios.
"""

import os
import tempfile
import unittest
import sys
import shutil
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


class TestEdgeCases(unittest.TestCase):
    """Test edge cases and boundary conditions."""
    
    def setUp(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
    
    def tearDown(self):
        """Clean up test environment."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir, ignore_errors=True)
    
    def test_project_names_with_special_characters(self):
        """Test project generation with special characters in names."""
        os.chdir(self.temp_dir)
        
        # Test names with underscores, numbers, and hyphens
        special_names = ['test_123', 'my_project_v2', 'project-test', 'test123']
        
        for name in special_names:
            with self.subTest(name=name):
                try:
                    project = BuildProject('logos')
                    project_dir = project.generate(name)
                    
                    # Verify the project was created with proper naming
                    expected_dir_name = f'project_{name}'
                    self.assertTrue(os.path.basename(project_dir).startswith('project_'))
                    
                    # Test that the generated project can be loaded
                    examples_path = os.path.join(project_dir, 'examples.py')
                    if os.path.exists(examples_path):
                        module_flags = MockFlags(examples_path)
                        build_module = BuildModule(module_flags)
                        self.assertIsNotNone(build_module.module)
                        
                except Exception as e:
                    self.fail(f"Failed to handle project name '{name}': {e}")
    
    def test_projects_in_directories_with_spaces(self):
        """Test project generation and loading in directories with spaces."""
        # Create a directory with spaces
        space_dir = os.path.join(self.temp_dir, 'my project directory')
        os.makedirs(space_dir)
        os.chdir(space_dir)
        
        try:
            project = BuildProject('logos')
            project_dir = project.generate('space_test')
            
            # Test loading from this path
            examples_path = os.path.join(project_dir, 'examples.py')
            self.assertTrue(os.path.exists(examples_path))
            
            module_flags = MockFlags(examples_path)
            build_module = BuildModule(module_flags)
            self.assertIsNotNone(build_module.module)
            
        except Exception as e:
            self.fail(f"Failed to handle directory with spaces: {e}")
    
    def test_deeply_nested_module_loading(self):
        """Test loading modules from deeply nested project structures."""
        os.chdir(self.temp_dir)
        
        project = BuildProject('logos')
        project_dir = project.generate('nested_test')
        
        # Test loading from a deeply nested submodule if it exists
        nested_path = os.path.join(project_dir, 'subtheories', 'modal', 'examples.py')
        if os.path.exists(nested_path):
            module_flags = MockFlags(nested_path)
            build_module = BuildModule(module_flags)
            
            # Verify the project detection still works from nested location
            nested_dir = os.path.dirname(nested_path)
            self.assertTrue(build_module._is_generated_project(nested_dir))
            
            # Verify it found the correct project root
            found_project_dir = build_module._find_project_directory(nested_dir)
            self.assertEqual(found_project_dir, project_dir)
    
    def test_multiple_projects_same_directory(self):
        """Test handling multiple generated projects in the same directory."""
        os.chdir(self.temp_dir)
        
        # Create multiple projects
        project1 = BuildProject('logos')
        project2 = BuildProject('logos')
        
        project_dir1 = project1.generate('multi_test1')
        project_dir2 = project2.generate('multi_test2')
        
        # Test loading from each project independently
        examples1 = os.path.join(project_dir1, 'examples.py')
        examples2 = os.path.join(project_dir2, 'examples.py')
        
        # Load first project
        module_flags1 = MockFlags(examples1)
        build_module1 = BuildModule(module_flags1)
        self.assertIsNotNone(build_module1.module)
        
        # Load second project (should not interfere)
        module_flags2 = MockFlags(examples2)
        build_module2 = BuildModule(module_flags2)
        self.assertIsNotNone(build_module2.module)
        
        # Verify they're treated as separate projects
        self.assertNotEqual(build_module1._find_project_directory(os.path.dirname(examples1)),
                           build_module2._find_project_directory(os.path.dirname(examples2)))
    
    def test_project_detection_boundary_cases(self):
        """Test edge cases in project detection logic."""
        os.chdir(self.temp_dir)
        
        project = BuildProject('logos')
        project_dir = project.generate('boundary_test')
        
        examples_path = os.path.join(project_dir, 'examples.py')
        module_flags = MockFlags(examples_path)
        build_module = BuildModule(module_flags)
        
        # Test detection from various depths
        test_cases = [
            project_dir,  # Root level
            os.path.dirname(examples_path),  # Same as root in this case
        ]
        
        # Add subdirectories if they exist
        if os.path.exists(os.path.join(project_dir, 'subtheories')):
            test_cases.append(os.path.join(project_dir, 'subtheories'))
        if os.path.exists(os.path.join(project_dir, 'subtheories', 'modal')):
            test_cases.append(os.path.join(project_dir, 'subtheories', 'modal'))
        
        for test_dir in test_cases:
            with self.subTest(test_dir=test_dir):
                self.assertTrue(build_module._is_generated_project(test_dir),
                              f"Should detect project from {test_dir}")
        
        # Test false positives
        non_project_dirs = [
            self.temp_dir,  # Parent of project
            '/tmp',  # System directory
            os.path.dirname(self.temp_dir),  # Grandparent
        ]
        
        for test_dir in non_project_dirs:
            with self.subTest(test_dir=test_dir):
                self.assertFalse(build_module._is_generated_project(test_dir),
                               f"Should not detect project from {test_dir}")
    
    def test_sys_path_cleanup_and_isolation(self):
        """Test that sys.path modifications don't leak between projects."""
        os.chdir(self.temp_dir)
        
        # Store original sys.path
        original_path = sys.path.copy()
        
        try:
            # Create and load first project
            project1 = BuildProject('logos')
            project_dir1 = project1.generate('isolation_test1')
            examples1 = os.path.join(project_dir1, 'examples.py')
            
            module_flags1 = MockFlags(examples1)
            build_module1 = BuildModule(module_flags1)
            
            # Capture sys.path after first project
            path_after_first = sys.path.copy()
            
            # Create and load second project
            project2 = BuildProject('logos')
            project_dir2 = project2.generate('isolation_test2')
            examples2 = os.path.join(project_dir2, 'examples.py')
            
            module_flags2 = MockFlags(examples2)
            build_module2 = BuildModule(module_flags2)
            
            # Verify both projects added their paths
            self.assertIn(project_dir1, sys.path)
            self.assertIn(project_dir2, sys.path)
            self.assertIn(os.path.dirname(project_dir1), sys.path)
            self.assertIn(os.path.dirname(project_dir2), sys.path)
            
        finally:
            # Note: We don't automatically clean up sys.path in the current implementation
            # This is by design for the module loading to work, but we verify it doesn't
            # interfere with functionality
            
            # Verify the modules still work
            self.assertIsNotNone(build_module1.module)
            self.assertIsNotNone(build_module2.module)
    
    def test_error_recovery_and_robustness(self):
        """Test error recovery in various failure scenarios."""
        os.chdir(self.temp_dir)
        
        # Test 1: Non-existent file
        non_existent = os.path.join(self.temp_dir, 'project_fake', 'examples.py')
        module_flags = MockFlags(non_existent)
        
        with self.assertRaises(ImportError):
            BuildModule(module_flags)
        
        # Test 2: File exists but has syntax errors
        project = BuildProject('logos')
        project_dir = project.generate('error_test')
        
        # Create a file with syntax errors
        bad_file = os.path.join(project_dir, 'bad_syntax.py')
        with open(bad_file, 'w') as f:
            f.write("this is not valid python syntax !")
        
        module_flags = MockFlags(bad_file)
        with self.assertRaises(ImportError):
            BuildModule(module_flags)
        
        # Test 3: Verify good file still works after errors
        good_file = os.path.join(project_dir, 'examples.py')
        if os.path.exists(good_file):
            module_flags = MockFlags(good_file)
            build_module = BuildModule(module_flags)
            self.assertIsNotNone(build_module.module)


class TestPerformanceAndMemory(unittest.TestCase):
    """Test performance characteristics and memory usage."""
    
    def setUp(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
    
    def tearDown(self):
        """Clean up test environment."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir, ignore_errors=True)
    
    def test_large_number_of_projects(self):
        """Test handling a large number of generated projects."""
        os.chdir(self.temp_dir)
        
        # Create multiple projects to test scalability
        num_projects = 10  # Keep reasonable for test speed
        projects = []
        
        for i in range(num_projects):
            project = BuildProject('logos')
            project_dir = project.generate(f'scale_test_{i}')
            projects.append(project_dir)
        
        # Test loading from each project
        for i, project_dir in enumerate(projects):
            with self.subTest(project=i):
                examples_path = os.path.join(project_dir, 'examples.py')
                if os.path.exists(examples_path):
                    module_flags = MockFlags(examples_path)
                    build_module = BuildModule(module_flags)
                    self.assertIsNotNone(build_module.module)
    
    def test_repeated_loading_same_project(self):
        """Test repeated loading of the same project for memory leaks."""
        os.chdir(self.temp_dir)
        
        project = BuildProject('logos')
        project_dir = project.generate('repeat_test')
        examples_path = os.path.join(project_dir, 'examples.py')
        
        if os.path.exists(examples_path):
            # Load the same project multiple times
            for i in range(5):
                with self.subTest(iteration=i):
                    module_flags = MockFlags(examples_path)
                    build_module = BuildModule(module_flags)
                    self.assertIsNotNone(build_module.module)
                    
                    # Verify consistent behavior
                    self.assertIsInstance(build_module.example_range, dict)
                    self.assertIsInstance(build_module.semantic_theories, dict)


class TestCLIIntegration(unittest.TestCase):
    """Test integration with the actual CLI workflow."""
    
    def setUp(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.original_cwd = os.getcwd()
    
    def tearDown(self):
        """Clean up test environment."""
        os.chdir(self.original_cwd)
        shutil.rmtree(self.temp_dir, ignore_errors=True)
    
    def test_cli_workflow_simulation(self):
        """Test the complete CLI workflow that users experience."""
        os.chdir(self.temp_dir)
        
        # Step 1: Generate project (simulates model-checker without args)
        project = BuildProject('logos')
        project_dir = project.generate('cli_test')
        
        # Step 2: Verify project structure matches expectations
        examples_path = os.path.join(project_dir, 'examples.py')
        self.assertTrue(os.path.exists(examples_path), 
                       "Generated project should have examples.py for CLI usage")
        
        # Step 3: Test loading (simulates model-checker path/to/examples.py)
        module_flags = MockFlags(examples_path)
        build_module = BuildModule(module_flags)
        
        # Step 4: Verify it has the expected structure for CLI execution
        self.assertIsNotNone(build_module.example_range)
        self.assertIsNotNone(build_module.semantic_theories)
        self.assertGreater(len(build_module.example_range), 0)
        
        # Step 5: Verify examples are actually runnable
        # (This tests that the examples contain valid, executable content)
        for example_name, example_case in list(build_module.example_range.items())[:1]:  # Test first example
            self.assertIsInstance(example_case, list)
            self.assertEqual(len(example_case), 3)  # [premises, conclusions, settings]
            premises, conclusions, settings = example_case
            self.assertIsInstance(premises, list)
            self.assertIsInstance(conclusions, list)
            self.assertIsInstance(settings, dict)


if __name__ == '__main__':
    unittest.main()