"""BuildProject implementation for creating new theory projects.

This module provides the BuildProject class for creating new theory implementation 
projects from templates. It handles directory structure creation, file copying, 
and initial setup of new modal logic theory implementations.
"""

import os
import shutil

class BuildProject:
    """Creates a new theory implementation project from templates.
    
    This class handles the creation of a new modal logic theory implementation
    by copying and configuring template files. It sets up the directory structure
    and initializes the basic implementation files.
    
    Attributes:
        theory (str): Name of the source theory to use as template
        source_dir (str): Directory path to the source theory
    """

    # Essential files that should be present in a valid theory
    ESSENTIAL_FILES = [
        "README.md",
        "__init__.py",
        "operators.py",
        "semantic.py",
        "examples.py"
    ]

    def __init__(self, theory: str = 'default'):
        """Initialize project builder with specified theory.
        
        Args:
            theory: Name of the source theory to use as template
            
        Raises:
            FileNotFoundError: If the source theory directory doesn't exist
        """
        self.theory = theory
        self.source_dir = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'theory_lib', theory)
        
        # Validate source directory exists
        if not os.path.exists(self.source_dir):
            raise FileNotFoundError(
                f"The semantic theory '{self.theory}' was not found at '{self.source_dir}'."
            )
        
    def generate(self, name: str, destination_dir: str = None):
        """Generate a new theory project.
        
        Args:
            name: Name for the new project
            destination_dir: Target directory (defaults to current directory)
            
        Returns:
            str: Path to the created project
            
        Raises:
            ValueError: If project name is invalid
            FileExistsError: If project directory already exists
            FileNotFoundError: If source theory not found
        """
        if not name:
            raise ValueError("Project name cannot be empty")
            
        # Create project path
        project_name = f"project_{name}"
        
        # Use current directory if no destination specified
        if destination_dir is None:
            destination_dir = os.getcwd()
            
        project_dir = os.path.join(destination_dir, project_name)
        
        # Verify destination doesn't exist
        if os.path.exists(project_dir):
            raise FileExistsError(f"Directory '{project_dir}' already exists.")
            
        # Create the project directory
        os.makedirs(project_dir)
        
        try:
            # Copy files from source to destination
            self._copy_files(project_dir)
            
            # Customize project files
            self._update_file_contents(project_dir)
            
            # Verify all essential files exist
            self._verify_essential_files(project_dir)
            
            return project_dir
            
        except Exception as e:
            # Clean up on failure
            if os.path.exists(project_dir):
                shutil.rmtree(project_dir)
            raise
    
    def _copy_files(self, project_dir):
        """Copy all files from source to destination directory.
        
        Args:
            project_dir: Path to the destination project directory
            
        Raises:
            FileNotFoundError: If source files don't exist
            PermissionError: If files can't be copied due to permissions
        """
        # Directories to ignore
        ignore_dirs = ['__pycache__', '.ipynb_checkpoints']
        
        # Copy all files from source to destination
        for item in os.listdir(self.source_dir):
            # Skip ignored directories
            if item in ignore_dirs:
                continue
                
            source_item = os.path.join(self.source_dir, item)
            dest_item = os.path.join(project_dir, item)
            
            if os.path.isdir(source_item):
                # Copy directories recursively, but ignore __pycache__ and .ipynb_checkpoints
                shutil.copytree(
                    source_item, 
                    dest_item,
                    ignore=shutil.ignore_patterns(*ignore_dirs)
                )
            else:
                # Copy files
                shutil.copy2(source_item, dest_item)
    
    def _update_file_contents(self, project_dir):
        """Update file contents with project-specific information.
        
        Args:
            project_dir: Path to the project directory
            
        Raises:
            FileNotFoundError: If files to update don't exist
            PermissionError: If files can't be modified
        """
        # Update __init__.py with current version
        init_path = os.path.join(project_dir, "__init__.py")
        if os.path.exists(init_path):
            with open(init_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # Get current version
            version = self._get_current_version()
            
            # Replace version in content
            new_content = content.replace("unknown", version)
            
            with open(init_path, 'w', encoding='utf-8') as f:
                f.write(new_content)
    
    def _get_current_version(self):
        """Extract the current version from pyproject.toml.
        
        Returns:
            str: Current version number, or fallback version if not found
        """
        try:
            # Look for pyproject.toml in parent directories
            current_dir = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
            pyproject_path = os.path.join(current_dir, 'pyproject.toml')
            
            if os.path.exists(pyproject_path):
                with open(pyproject_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                    
                # Find version line
                for line in content.split('\n'):
                    if line.strip().startswith('version = '):
                        return line.split('=')[1].strip().strip('"\'')
                        
            return "0.0.0"  # Fallback
            
        except Exception:
            return "0.0.0"  # Fallback on any error
    
    def _verify_essential_files(self, project_dir):
        """Verify all essential files were copied successfully.
        
        Args:
            project_dir: Path to the project directory
            
        Raises:
            FileNotFoundError: If any essential file is missing
        """
        missing_files = []
        
        for file in self.ESSENTIAL_FILES:
            file_path = os.path.join(project_dir, file)
            if not os.path.exists(file_path):
                missing_files.append(file)
                
        if missing_files:
            raise FileNotFoundError(
                f"Failed to create essential files: {', '.join(missing_files)}"
            )