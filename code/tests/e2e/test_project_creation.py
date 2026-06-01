#!/usr/bin/env python3
"""End-to-end tests for project creation functionality.

Tests the complete project creation workflow including:
- Non-interactive project generation
- Directory structure validation
- File content verification
"""

import os
import shutil
import pytest
from pathlib import Path
from tests.utils.helpers import run_cli_command, create_temp_project


class TestProjectCreation:
    """Test project creation with non-interactive inputs."""
    
    @pytest.fixture
    def project_setup(self, tmp_path):
        """Setup for project tests."""
        return {
            'base_dir': tmp_path,
            'project_name': 'test_project',
            'theory': 'bimodal'
        }
    
    def test_project_directory_creation(self, project_setup, tmp_path):
        """Test project directory is created correctly using BuildProject API."""
        from model_checker.builder.project import BuildProject

        # Create project using BuildProject API directly
        builder = BuildProject(theory=project_setup['theory'])
        project_path = builder.generate(
            name=project_setup['project_name'],
            destination_dir=str(tmp_path)
        )

        # Check project directory exists
        project_path = Path(project_path)
        assert project_path.exists(), f"Project directory not created at {project_path}"
        assert project_path.is_dir(), "Project path is not a directory"

        # Verify expected project name prefix
        assert project_path.name == f"project_{project_setup['project_name']}"
    
    def test_project_file_structure(self, project_setup, tmp_path):
        """Test all expected files are created."""
        # Create test project
        project_path = create_temp_project(
            tmp_path, 
            project_setup['project_name'],
            project_setup['theory']
        )
        
        # Check expected files exist
        expected_files = [
            '__init__.py',
            'examples.py'
        ]
        
        for filename in expected_files:
            file_path = project_path / filename
            assert file_path.exists(), f"Expected file {filename} not found"
            assert file_path.stat().st_size > 0, f"File {filename} is empty"
    
    def test_project_imports_work(self, project_setup, tmp_path):
        """Test generated project can be imported."""
        # Create test project
        project_path = create_temp_project(
            tmp_path,
            project_setup['project_name'], 
            project_setup['theory']
        )
        
        # Try to import the project
        import sys
        sys.path.insert(0, str(tmp_path))
        try:
            # Dynamic import of created project
            import importlib
            module = importlib.import_module(project_setup['project_name'])
            
            # Verify module has expected attributes
            assert hasattr(module, 'examples'), "Module missing 'examples' submodule"
            
        finally:
            # Clean up sys.path
            sys.path.remove(str(tmp_path))
    
    def test_project_content_validity(self, project_setup, tmp_path):
        """Test generated project content is valid."""
        # Create test project
        project_path = create_temp_project(
            tmp_path,
            project_setup['project_name'],
            project_setup['theory']
        )
        
        # Read and validate examples.py
        examples_file = project_path / 'examples.py'
        content = examples_file.read_text()
        
        # Check for required components
        assert f"from model_checker.theory_lib import {project_setup['theory']}" in content
        assert "semantic_theories" in content
        assert "example_range" in content
        
        # Validate syntax
        import ast
        try:
            ast.parse(content)
        except SyntaxError as e:
            pytest.fail(f"Generated examples.py has syntax error: {e}")
    
    @pytest.mark.parametrize("theory_name", [
        'bimodal'
    ])
    def test_project_creation_all_theories(self, theory_name, tmp_path):
        """Test project creation works for all supported theories."""
        # Create project for each theory
        project_path = create_temp_project(
            tmp_path,
            f"test_{theory_name}",
            theory_name
        )
        
        # Validate project was created
        assert project_path.exists()
        assert (project_path / '__init__.py').exists()
        assert (project_path / 'examples.py').exists()