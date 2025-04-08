#!/usr/bin/env python3
"""
A script to create a symlink from the model_checker source to the Python path
so it can be imported in Jupyter notebooks without installation.
"""

import os
import sys
import subprocess
import glob
import site
from pathlib import Path

def create_symlink():
    # Get the current directory (should be ModelChecker/Code)
    project_dir = os.path.abspath(os.getcwd())
    source_dir = os.path.join(project_dir, 'src', 'model_checker')
    
    # Find the user site-packages directory
    user_site = site.getusersitepackages()
    target_dir = os.path.join(user_site, 'model_checker')
    
    # Ensure the user site-packages directory exists
    os.makedirs(user_site, exist_ok=True)
    
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
                # If it's a real directory, recreate the symlink to the directory
                os.system(f"rm -rf {target_file}")
            else:
                os.remove(target_file)
        
        # Create the symlink
        print(f"Creating symlink: {source_file} -> {target_file}")
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

if __name__ == "__main__":
    if create_symlink():
        print("\nYou can now import model_checker in Jupyter notebooks.")
        print("To start a Jupyter notebook server, run:")
        print("jupyter notebook")
    else:
        print("\nFailed to set up the model_checker module for Jupyter.")
        print("Check the error messages above for clues.")