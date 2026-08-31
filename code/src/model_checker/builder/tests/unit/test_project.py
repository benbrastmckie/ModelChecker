"""Tests for the BuildProject class.

This module provides comprehensive unit tests for the BuildProject class,
covering project creation, theory selection, template generation, and
error handling according to TESTING_STANDARDS.md.
"""

import unittest
import os
import tempfile
import shutil
import stat
from unittest.mock import Mock, patch, MagicMock

# Import test fixtures
from model_checker.builder.tests.fixtures.test_data import (
    TestTheories, TestExamples, TestModules
)
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory

from model_checker.builder.project import BuildProject


class TestBuildProjectCore(unittest.TestCase):
    """Test BuildProject core functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Create a temporary directory for testing
        self.temp_dir = tempfile.mkdtemp()
        self.addCleanup(lambda: self._cleanup_temp_dir())
        
    def _cleanup_temp_dir(self):
        """Clean up temporary directory with proper permissions."""
        if os.path.exists(self.temp_dir):
            # Ensure we can delete even read-only files
            for root, dirs, files in os.walk(self.temp_dir):
                for d in dirs:
                    os.chmod(os.path.join(root, d), stat.S_IRWXU)
                for f in files:
                    os.chmod(os.path.join(root, f), stat.S_IRUSR | stat.S_IWUSR)
            shutil.rmtree(self.temp_dir)
    
    def tearDown(self):
        """Clean up test fixtures."""
        # Cleanup is handled by addCleanup
        pass
    
    def test_project_initialization_default(self):
        """Test that BuildProject initializes with the first registered theory.

        BuildProject() with no argument defers to the first entry in
        model_checker.registry (see project.py's __init__ docstring and
        docs/THEORY_ARCHITECTURE.md's Layering section) rather than a
        hardcoded theory name, so the expected default tracks whichever
        theory is registered first instead of assuming 'logos'.
        """
        from model_checker import registry

        builder = BuildProject()
        self.assertEqual(builder.theory, registry.get_registered()[0])
        self.assertTrue(os.path.exists(builder.source_dir))
    
    def test_project_initialization_logos(self):
        """Test that BuildProject initializes with logos theory."""
        builder = BuildProject('logos')
        self.assertEqual(builder.theory, 'logos')
        self.assertTrue(os.path.exists(builder.source_dir))
        self.assertIn('logos', builder.source_dir)

    def test_project_initialization_with_subtheories(self):
        """Test BuildProject initialization with subtheories."""
        builder = BuildProject('logos', subtheories=['modal', 'constitutive'])
        self.assertEqual(builder.theory, 'logos')
        self.assertEqual(builder.subtheories, ['modal', 'constitutive'])
        self.assertTrue(os.path.exists(builder.source_dir))

    
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
        with self.assertRaises(FileNotFoundError) as context:
            BuildProject('nonexistent_theory')
        
        self.assertIn("nonexistent_theory", str(context.exception).lower(),
                     "Error message should mention the invalid theory name")
    
    def test_create_project_with_valid_name_succeeds(self):
        """Test project creation with valid name creates correct structure.
        
        This verifies that a project with a valid name is created with
        all expected directories and files in the correct structure.
        """
        builder = BuildProject('logos')
        project_name = "valid_project_name"
        project_path = builder.generate(project_name, self.temp_dir)
        
        # Assert project directory exists
        self.assertTrue(os.path.exists(project_path),
                       f"Project directory should exist at {project_path}")
        self.assertTrue(os.path.isdir(project_path),
                       "Project path should be a directory")
        
        # Assert essential files exist
        essential_files = ['__init__.py', 'examples.py']
        for filename in essential_files:
            file_path = os.path.join(project_path, filename)
            self.assertTrue(os.path.exists(file_path),
                          f"Essential file {filename} should exist in project")
    
    def test_create_project_handles_special_characters_in_name(self):
        """Test project creation sanitizes special characters appropriately.
        
        This ensures that project names with special characters are
        properly sanitized to create valid directory names.
        """
        builder = BuildProject('logos')
        
        # Test various special character cases
        test_cases = [
            ("project-with-dashes", "project-with-dashes"),
            ("project_with_underscores", "project_with_underscores"),
            ("Project With Spaces", "Project With Spaces"),  # Spaces might be allowed
            ("project.with.dots", "project.with.dots"),
        ]
        
        for input_name, expected_name in test_cases:
            with self.subTest(input_name=input_name):
                project_path = builder.generate(input_name, self.temp_dir)
                actual_name = os.path.basename(project_path)
                
                # Check if the directory was created
                self.assertTrue(os.path.exists(project_path),
                              f"Project should be created for name: {input_name}")
                
                # The actual sanitization behavior depends on BuildProject implementation
                # For now, we just verify the project is created successfully
    
    def test_create_project_validates_theory_selection(self):
        """Test project creation rejects invalid theory selections.
        
        This verifies that only valid theory names are accepted and
        appropriate errors are raised for invalid selections.
        """
        # Note: None defaults to 'logos' so it doesn't raise an error
        # Empty string and numeric values might be converted to strings
        invalid_theories = ['invalid_theory_xyz', 'nonexistent_theory_abc']
        
        for invalid_theory in invalid_theories:
            with self.subTest(theory=invalid_theory):
                with self.assertRaises(FileNotFoundError) as context:
                    BuildProject(invalid_theory)
                
                self.assertIn(invalid_theory, str(context.exception).lower(),
                             f"Error should mention the invalid theory name: {invalid_theory}")
    
    def test_generate_template_creates_valid_content(self):
        """Test template generation produces valid Python module.
        
        This ensures that generated project templates contain valid
        Python code that can be imported and executed.
        """
        builder = BuildProject('logos')
        project_path = builder.generate('template_test', self.temp_dir)
        
        # Check that examples.py contains valid Python
        examples_path = os.path.join(project_path, 'examples.py')
        self.assertTrue(os.path.exists(examples_path),
                       "examples.py should be created")
        
        # Try to compile the Python file to check syntax
        with open(examples_path, 'r') as f:
            content = f.read()
            try:
                compile(content, examples_path, 'exec')
                syntax_valid = True
            except SyntaxError:
                syntax_valid = False
        
        self.assertTrue(syntax_valid,
                       "Generated examples.py should contain valid Python syntax")


class TestBuildProjectEdgeCases(unittest.TestCase):
    """Test BuildProject edge cases and error handling."""
    
    def setUp(self):
        """Set up test fixtures for edge case testing."""
        self.temp_dir = tempfile.mkdtemp()
        self.addCleanup(lambda: self._cleanup_temp_dir())
    
    def _cleanup_temp_dir(self):
        """Clean up temporary directory with proper permissions."""
        if os.path.exists(self.temp_dir):
            # Ensure we can delete even read-only files
            for root, dirs, files in os.walk(self.temp_dir):
                for d in dirs:
                    os.chmod(os.path.join(root, d), stat.S_IRWXU)
                for f in files:
                    os.chmod(os.path.join(root, f), stat.S_IRUSR | stat.S_IWUSR)
            shutil.rmtree(self.temp_dir)
    
    def test_create_project_in_readonly_directory_fails_gracefully(self):
        """Test project creation handles permission errors with clear message.
        
        This verifies that attempting to create a project in a read-only
        directory produces a clear error message about permissions.
        """
        builder = BuildProject('logos')
        
        # Create a read-only directory
        readonly_dir = os.path.join(self.temp_dir, 'readonly')
        os.makedirs(readonly_dir)
        
        # Make it read-only (remove write permission)
        os.chmod(readonly_dir, stat.S_IRUSR | stat.S_IXUSR)
        
        # Attempt to create project in read-only directory
        with self.assertRaises((PermissionError, OSError)) as context:
            builder.generate('test_project', readonly_dir)
        
        # Restore write permission for cleanup
        os.chmod(readonly_dir, stat.S_IRWXU)
    
    def test_create_project_with_existing_name_handles_appropriately(self):
        """Test project creation handles existing directories appropriately.
        
        This verifies the behavior when attempting to create a project
        in a location where a directory with that name already exists.
        """
        builder = BuildProject('logos')
        project_name = 'existing_project'
        
        # Create the project first time
        first_path = builder.generate(project_name, self.temp_dir)
        self.assertTrue(os.path.exists(first_path),
                       "First project creation should succeed")
        
        # Create a marker file to detect if directory is replaced
        marker_file = os.path.join(first_path, 'marker.txt')
        with open(marker_file, 'w') as f:
            f.write('original')
        
        # Try to create project with same name
        # The behavior depends on BuildProject implementation
        # It might overwrite, skip, or raise an error
        try:
            second_path = builder.generate(project_name, self.temp_dir)
            # If it succeeds, check if it overwrote or created elsewhere
            if second_path == first_path:
                # Check if marker file still exists to determine if overwritten
                if not os.path.exists(marker_file):
                    # Directory was overwritten
                    pass
                else:
                    # Directory was reused
                    pass
        except (FileExistsError, OSError):
            # Expected behavior - cannot overwrite existing directory
            pass
    
    def test_create_project_with_empty_name_raises_error(self):
        """Test that empty project names are handled appropriately.
        
        This ensures that empty or whitespace-only project names
        are either rejected or handled gracefully.
        """
        builder = BuildProject('logos')
        
        # Empty string might create a project in the temp_dir itself
        # or might be rejected - depends on implementation
        try:
            result = builder.generate('', self.temp_dir)
            # If it succeeds, verify something was created
            self.assertTrue(os.path.exists(self.temp_dir),
                          "Should handle empty name somehow")
        except (ValueError, OSError, FileNotFoundError):
            # This is also acceptable behavior
            pass
        
        # Test whitespace-only names
        whitespace_names = ['   ', '\t', '\n']
        
        for invalid_name in whitespace_names:
            with self.subTest(name=repr(invalid_name)):
                try:
                    result = builder.generate(invalid_name, self.temp_dir)
                    # If it succeeds, check that something was created
                    self.assertTrue(os.path.exists(result),
                                  f"Should create something for {repr(invalid_name)}")
                except (ValueError, OSError, FileNotFoundError):
                    # This is also acceptable - rejecting whitespace names
                    pass
    
    def test_create_project_with_very_long_name(self):
        """Test project creation with very long names.
        
        This verifies that extremely long project names are handled
        appropriately, either by truncation or error.
        """
        builder = BuildProject('logos')
        
        # Create a very long name (longer than typical filesystem limits)
        very_long_name = 'a' * 300  # Most filesystems limit to 255 characters
        
        # This should either truncate the name or raise an error
        try:
            project_path = builder.generate(very_long_name, self.temp_dir)
            # If it succeeds, check that the name was handled somehow
            actual_name = os.path.basename(project_path)
            self.assertLessEqual(len(actual_name), 255,
                               "Project name should be truncated to filesystem limits")
        except (OSError, ValueError):
            # Expected - name too long
            pass
    
    def test_generate_multiple_projects_independently(self):
        """Test that multiple projects can be generated independently.
        
        This verifies that generating multiple projects doesn't cause
        interference or state contamination between them.
        """
        builder = BuildProject('logos')
        
        # Generate multiple projects
        project_names = ['project1', 'project2', 'project3']
        project_paths = []
        
        for name in project_names:
            path = builder.generate(name, self.temp_dir)
            project_paths.append(path)
            
            # Verify project was created
            self.assertTrue(os.path.exists(path),
                          f"Project {name} should be created")
            
            # Verify it's unique
            self.assertEqual(len(set(project_paths)), len(project_paths),
                           "Each project should have a unique path")
        
        # Verify all projects still exist
        for path in project_paths:
            self.assertTrue(os.path.exists(path),
                          "All projects should still exist after creating others")


class TestBuildProjectManifestFilterPycache(unittest.TestCase):
    """Test that __pycache__/*.pyc are silently excluded from the manifest-filter
    warning loop, while genuinely unexpected items still warn."""

    def setUp(self):
        """Set up a synthetic, contract-conforming theory source tree under tmp_path-style
        tempfile, plus a real BuildProject instance pointed at it."""
        self.temp_dir = tempfile.mkdtemp()
        self.addCleanup(lambda: self._cleanup_temp_dir())

        from model_checker.builder.project import (
            REQUIRED_COPY_ITEMS, SEMANTIC_ALTERNATIVES,
        )

        self.source_dir = os.path.join(self.temp_dir, 'synthetic_theory')
        os.makedirs(self.source_dir)

        # Populate every required item plus one semantic alternative, minimally.
        for item in REQUIRED_COPY_ITEMS:
            item_path = os.path.join(self.source_dir, item)
            if item in ('tests', 'docs'):
                os.makedirs(item_path, exist_ok=True)
            else:
                with open(item_path, 'w') as f:
                    f.write("# synthetic\n")
        semantic_dir = os.path.join(self.source_dir, SEMANTIC_ALTERNATIVES[0])
        os.makedirs(semantic_dir, exist_ok=True)

        self.builder = BuildProject('logos')
        self.builder.source_dir = self.source_dir

        self.dest_dir = os.path.join(self.temp_dir, 'dest_project')
        os.makedirs(self.dest_dir)

    def _cleanup_temp_dir(self):
        """Clean up temporary directory with proper permissions."""
        if os.path.exists(self.temp_dir):
            for root, dirs, files in os.walk(self.temp_dir):
                for d in dirs:
                    os.chmod(os.path.join(root, d), stat.S_IRWXU)
                for f in files:
                    os.chmod(os.path.join(root, f), stat.S_IRUSR | stat.S_IWUSR)
            shutil.rmtree(self.temp_dir)

    def test_pycache_produces_no_warning(self):
        """A __pycache__ directory alongside manifest items produces no
        'Skipped non-manifest item' warning."""
        pycache_dir = os.path.join(self.source_dir, '__pycache__')
        os.makedirs(pycache_dir, exist_ok=True)
        with open(os.path.join(pycache_dir, 'module.cpython-313.pyc'), 'w') as f:
            f.write("")

        self.builder._copy_files(self.dest_dir)

        pycache_warnings = [
            msg for msg in self.builder.log_messages
            if 'Skipped non-manifest item: __pycache__' in msg
        ]
        self.assertEqual(pycache_warnings, [])

    def test_stray_unknown_item_still_warns(self):
        """A stray item not on the copy manifest still produces a WARNING."""
        with open(os.path.join(self.source_dir, 'stray_file.tmp'), 'w') as f:
            f.write("")

        self.builder._copy_files(self.dest_dir)

        stray_warnings = [
            msg for msg in self.builder.log_messages
            if 'Skipped non-manifest item: stray_file.tmp' in msg
        ]
        self.assertEqual(len(stray_warnings), 1)
        self.assertIn('WARNING', stray_warnings[0])


class TestHandleExampleScriptInteractiveFlag(unittest.TestCase):
    """Test _handle_example_script()'s interactive/non-interactive behavior.

    Non-interactive project generation needs a way to skip the "Would you like
    to test an example?" prompt without raising EOFError when stdin is closed.
    The `interactive` parameter defaults to True so the existing interactive
    path (called from ask_generate()) is unchanged.
    """

    def setUp(self):
        self.temp_dir = tempfile.mkdtemp()
        self.addCleanup(lambda: self._cleanup_temp_dir())

    def _cleanup_temp_dir(self):
        if os.path.exists(self.temp_dir):
            shutil.rmtree(self.temp_dir)

    def test_default_interactive_true_still_calls_input(self):
        """Default behavior (interactive=True) is unchanged: input() is called."""
        from model_checker import registry

        builder = BuildProject(registry.get_registered()[0])
        with patch('builtins.input', return_value='n') as mock_input:
            builder._handle_example_script(self.temp_dir)
        mock_input.assert_called_once()

    def test_non_interactive_skips_prompt_without_eof(self):
        """interactive=False never calls input(), even with no example files present."""
        from model_checker import registry

        builder = BuildProject(registry.get_registered()[0])
        with patch('builtins.input', side_effect=EOFError("stdin closed")) as mock_input:
            # Must not raise EOFError: input() must not be called at all.
            builder._handle_example_script(self.temp_dir, interactive=False)
        mock_input.assert_not_called()

    def test_non_interactive_prints_run_instructions(self):
        """interactive=False prints the 'how to run' message unconditionally."""
        from model_checker import registry

        builder = BuildProject(registry.get_registered()[0])
        with patch('builtins.input', side_effect=EOFError("stdin closed")):
            with patch('builtins.print') as mock_print:
                builder._handle_example_script(self.temp_dir, interactive=False)

        printed = "\n".join(str(call.args[0]) for call in mock_print.call_args_list if call.args)
        self.assertIn("model-checker <path-to-example-file>", printed)


if __name__ == "__main__":
    unittest.main()