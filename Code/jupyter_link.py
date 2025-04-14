#!/usr/bin/env python3
"""
ModelChecker Jupyter Integration Tool

This script sets up the ModelChecker package for use with Jupyter notebooks
by creating symlinks from the development code to the Python user site-packages.
This approach works well in NixOS and other environments where you can't easily
install packages with pip.

Usage:
    ./jupyter_link.py [--launch]

Options:
    --launch    Launch Jupyter notebook after setup

After running this script, the ModelChecker package will be available
in Jupyter notebooks without needing to modify PYTHONPATH in each notebook.
"""

import os
import sys
import subprocess
import glob
import site
import argparse
import signal
from pathlib import Path

def create_symlink():
    """
    Create symlinks from the development code to the Python user site-packages.
    """
    # Get the current directory (should be ModelChecker/Code)
    project_dir = os.path.abspath(os.getcwd())
    source_dir = os.path.join(project_dir, 'src', 'model_checker')
    
    # Find the user site-packages directory
    user_site = site.getusersitepackages()
    target_dir = os.path.join(user_site, 'model_checker')
    
    # Ensure the user site-packages directory exists
    os.makedirs(user_site, exist_ok=True)
    
    print(f"Setting up ModelChecker for Jupyter...")
    print(f"Project directory: {project_dir}")
    print(f"Source directory: {source_dir}")
    print(f"Target directory: {target_dir}")
    
    # Create the target directory if it doesn't exist
    os.makedirs(target_dir, exist_ok=True)
    
    # Create symlinks for all files in the source directory
    for source_file in glob.glob(os.path.join(source_dir, '*')):
        # Skip __pycache__ directories
        if '__pycache__' in source_file:
            continue
            
        filename = os.path.basename(source_file)
        target_file = os.path.join(target_dir, filename)
        
        # Remove existing file or symlink if it exists
        if os.path.exists(target_file):
            if os.path.isdir(target_file) and not os.path.islink(target_file):
                # If it's a real directory, remove it
                os.system(f"rm -rf {target_file}")
            else:
                os.remove(target_file)
        
        # Create the symlink
        print(f"Creating symlink: {filename}")
        os.symlink(source_file, target_file)
    
    # Create init.py in the user site-packages directory if needed
    init_path = os.path.join(user_site, 'model_checker', '__init__.py')
    if not os.path.exists(init_path):
        with open(init_path, 'w') as f:
            f.write('# This file was created by jupyter_link.py\n')
    
    # Check that the module can be imported
    try:
        sys.path.insert(0, user_site)
        import model_checker
        print(f"Success! model_checker can be imported from {model_checker.__file__}")
        print(f"Version: {model_checker.__version__}")
        return True
    except ImportError as e:
        print(f"Error importing model_checker: {e}")
        return False

def create_jupyter_example():
    """
    Create a simple example Jupyter notebook in the current directory
    to demonstrate the ModelChecker package.
    """
    notebook_path = "model_checker_example.ipynb"
    
    # Don't overwrite existing example
    if os.path.exists(notebook_path):
        print(f"Example notebook already exists: {notebook_path}")
        return notebook_path
    
    notebook_content = {
        "cells": [
            {
                "cell_type": "markdown",
                "metadata": {},
                "source": ["# ModelChecker Example\n", "\n", "This notebook demonstrates how to use the ModelChecker package with Jupyter."]
            },
            {
                "cell_type": "code",
                "execution_count": None,
                "metadata": {},
                "outputs": [],
                "source": [
                    "# Import the ModelChecker package\n",
                    "import model_checker\n",
                    "print(f\"ModelChecker version: {model_checker.__version__}\")\n",
                    "print(f\"ModelChecker location: {model_checker.__file__}\")"
                ]
            },
            {
                "cell_type": "code",
                "execution_count": None,
                "metadata": {},
                "outputs": [],
                "source": [
                    "# Import the check_formula function for interactive use\n",
                    "from model_checker.jupyter import check_formula"
                ]
            },
            {
                "cell_type": "code",
                "execution_count": None,
                "metadata": {},
                "outputs": [],
                "source": [
                    "# Check a simple formula\n",
                    "check_formula(\"(A \\\\equiv A)\")"
                ]
            },
            {
                "cell_type": "code",
                "execution_count": None,
                "metadata": {},
                "outputs": [],
                "source": [
                    "# Create an interactive explorer\n",
                    "from model_checker.jupyter import InteractiveModelExplorer\n",
                    "\n",
                    "explorer = InteractiveModelExplorer()\n",
                    "explorer.display()"
                ]
            }
        ],
        "metadata": {
            "kernelspec": {
                "display_name": "Python 3",
                "language": "python",
                "name": "python3"
            },
            "language_info": {
                "codemirror_mode": {
                    "name": "ipython",
                    "version": 3
                },
                "file_extension": ".py",
                "mimetype": "text/x-python",
                "name": "python",
                "nbconvert_exporter": "python",
                "pygments_lexer": "ipython3",
                "version": "3.8.10"
            }
        },
        "nbformat": 4,
        "nbformat_minor": 4
    }
    
    try:
        import json
        with open(notebook_path, 'w') as f:
            json.dump(notebook_content, f, indent=2)
        print(f"Created example notebook: {notebook_path}")
        return notebook_path
    except Exception as e:
        print(f"Error creating example notebook: {e}")
        return None

def launch_jupyter():
    """
    Launch Jupyter notebook server with proper signal handling.
    """
    print("\nLaunching Jupyter notebook server...")
    
    # Set up signal handler for clean exit
    def signal_handler(sig, frame):
        print("\nShutting down Jupyter (this may take a moment)...")
        # The process will be terminated by the signal, no need to do anything else
        pass
    
    # Register the signal handler
    signal.signal(signal.SIGINT, signal_handler)
    
    # Use os.execvp to replace the current process with Jupyter
    # This avoids subprocess management issues with Ctrl+C
    os.execvp("jupyter", ["jupyter", "notebook"])

def main():
    parser = argparse.ArgumentParser(description="Set up ModelChecker for Jupyter notebooks")
    # parser.add_argument("--launch", action="store_true", help="Launch Jupyter notebook after setup")
    parser.add_argument("--example", action="store_true", help="Create an example notebook")
    args = parser.parse_args()
    
    # Create symlinks
    if create_symlink():
        print("\nSetup complete! ModelChecker is now available in Jupyter notebooks.")
        
        # Create example notebook only if explicitly requested
        if args.example:
            example_path = create_jupyter_example()
        
        print("\nQuick Start:")
        print("1. Run 'jupyter notebook' to start the Jupyter server")
        print("2. Open any notebook and import model_checker")
        print("3. Use model_checker.jupyter module for interactive features")
        
        # Launch Jupyter if requested
        # if args.launch:
        launch_jupyter()
    else:
        print("\nSetup failed. Please check the error messages above.")
        sys.exit(1)

if __name__ == "__main__":
    main()
