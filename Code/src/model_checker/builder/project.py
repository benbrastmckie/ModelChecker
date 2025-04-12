"""BuildProject implementation for creating new theory projects.

This module provides the BuildProject class for creating new theory implementation 
projects from templates. It handles directory structure creation, file copying, 
and initial setup of new modal logic theory implementations.
"""

import os
import sys
import shutil
import subprocess

class BuildProject:
    """Creates a new theory implementation project from templates.
    
    This class handles the creation of a new modal logic theory implementation
    by copying and configuring template files. It sets up the directory structure
    and initializes the basic implementation files.
    
    Attributes:
        theory (str): Name of the source theory to use as template
        source_dir (str): Directory path to the source theory
        project_name (str): Name of the new project (will be prefixed with 'project_')
        destination_dir (str): Directory path for the new project
        log_messages (list): Log of actions and messages during project generation
    """

    # Essential files that should be present in a valid theory
    ESSENTIAL_FILES = [
        "README.md",
        "__init__.py",
        "operators.py",
        "semantic.py",
        "examples.py"
    ]
    
    # Core files that will be highlighted in the success message
    CORE_FILES = [
        "examples.py",
        "operators.py",
        "semantic.py",
        "README.md"
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
        self.project_name = ""
        self.destination_dir = ""
        self.log_messages = []
        
        # Validate source directory exists
        if not os.path.exists(self.source_dir):
            raise FileNotFoundError(
                f"The semantic theory '{self.theory}' was not found at '{self.source_dir}'."
            )
    
    def log(self, message, level="INFO"):
        """Log a message with a specified level.
        
        Args:
            message (str): The message to log
            level (str): The log level (INFO, WARNING, ERROR)
        """
        self.log_messages.append(f"[{level}] {message}")
        if level == "ERROR":
            print(f"Error: {message}")
        elif level == "WARNING":
            print(f"Warning: {message}")
        else:
            print(message)
    
    def ask_generate(self):
        """Prompt user to create a new theory implementation project.
        
        Asks the user if they want to generate a new project for the current theory.
        If yes, prompts for a project name and calls generate(). If no, displays
        information about running existing example files.
        """
        result = input(f"Would you like to generate a new {self.theory}-project? (y/n): ")
        if result.lower() not in {'yes', 'ye', 'y'}:
            print("\nYou can run an example.py file that already exists with the command:\n")
            print("  $ model-checker example.py\n")
            return
        
        test_name = input("Enter the name of your project using snake_case: ")
        if not test_name:
            print("Project name cannot be empty.")
            return
            
        try:
            project_dir = self.generate(test_name)
            self._print_success_message(project_dir)
            self._handle_example_script(project_dir)
        except Exception as e:
            print(f"Error creating project: {e}")
        
    def generate(self, name: str, destination_dir: str = None):
        """Generate a new theory implementation project from templates.
        
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
        self.project_name = f"project_{name}"
        
        # Use current directory if no destination specified
        if destination_dir is None:
            destination_dir = os.getcwd()
            
        self.destination_dir = os.path.join(destination_dir, self.project_name)
        
        # Verify destination doesn't exist
        if os.path.exists(self.destination_dir):
            raise FileExistsError(f"Directory '{self.destination_dir}' already exists.")
            
        # Create the project directory
        os.makedirs(self.destination_dir)
        
        try:
            # Copy files from source to destination
            self._copy_files(self.destination_dir)
            
            # Customize project files
            self._update_file_contents(self.destination_dir)
            
            # Verify all essential files exist
            self._verify_essential_files(self.destination_dir)
            
            return self.destination_dir
            
        except Exception as e:
            # Clean up on failure
            if os.path.exists(self.destination_dir):
                shutil.rmtree(self.destination_dir)
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
            
            try:
                if os.path.isdir(source_item):
                    # Copy directories recursively, but ignore __pycache__ and .ipynb_checkpoints
                    shutil.copytree(
                        source_item, 
                        dest_item,
                        ignore=shutil.ignore_patterns(*ignore_dirs)
                    )
                    self.log(f"Copied directory: {item}")
                else:
                    # Copy files
                    shutil.copy2(source_item, dest_item)
                    self.log(f"Copied file: {item}")
            except Exception as e:
                self.log(f"Error copying {item}: {str(e)}", "ERROR")
    
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
            source_path = os.path.join(self.source_dir, file)
            
            # If file exists in source but not in destination, try to copy it again
            if os.path.exists(source_path) and not os.path.exists(file_path):
                try:
                    # Try direct binary copy as a backup method
                    with open(source_path, 'rb') as src, open(file_path, 'wb') as dst:
                        dst.write(src.read())
                except Exception:
                    missing_files.append(file)
            elif not os.path.exists(file_path):
                missing_files.append(file)
                
        if missing_files:
            raise FileNotFoundError(
                f"Failed to create essential files: {', '.join(missing_files)}"
            )
    
    def _print_success_message(self, project_dir):
        """Print success message with created files.
        
        Args:
            project_dir: Path to the project directory
        """
        print(f"\nProject generated at: {project_dir}\n")
        print("The following modules were created:")
        
        # List core files that were actually copied
        for file in sorted(os.listdir(project_dir)):
            # Show all .py files and README.md
            if file.endswith(".py") or file == "README.md":
                print(f"  {file}")
    
    def _handle_example_script(self, project_dir):
        """Handle running the example script if requested.
        
        Args:
            project_dir: Path to the project directory
        """
        result = input("Would you like to test the example script? (y/n): ")
        if result.lower() not in {'yes', 'ye', 'y'}:
            print(f"\nRun the following command to test your project:\n\nmodel-checker {project_dir}/examples.py\n")
            return

        example_script = os.path.join(project_dir, "examples.py")
        print(example_script)
        if os.path.exists(example_script):
            print("\nRunning the example script...")
            try:
                # Use subprocess to run the example script
                subprocess.run(["model-checker", example_script], 
                             check=True,
                             timeout=30)  # Add 30 second timeout
            except subprocess.TimeoutExpired:
                print("\nScript execution timed out. You can run it manually with:")
                print(f"model-checker {example_script}")
            except subprocess.CalledProcessError as e:
                print(f"\nError running example script: {e}")
                print(f"You can run it manually with: model-checker {example_script}")
            except Exception as e:
                print(f"\nUnexpected error: {e}")
                print(f"You can run it manually with: model-checker {example_script}")
        else:
            print(f"\nFailed to run: model-checker {example_script}")
            print(f"The examples.py file was not found at: {example_script}")
            print(f"Please check if the file exists and try running it manually.")