#!/usr/bin/env python3
"""Test script for project creation with non-interactive inputs."""

import os
import sys
import tempfile
import shutil
import subprocess

# Directory for testing project creation
test_dir = tempfile.mkdtemp()
print(f"Created temporary directory for testing: {test_dir}")

try:
    # Path to dev_cli.py
    dev_cli_path = "./dev_cli.py"
    
    # Test command with input piped for non-interactive use
    # Simulates answering "y" to generate project, "test_project" as name, "n" to not run example
    cmd = f'echo -e "y\ntest_project\nn\n" | {dev_cli_path} -l bimodal'
    
    # Run the command using bash to properly handle the pipe
    result = subprocess.run(
        ["bash", "-c", cmd],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=os.getcwd()  # Run from current directory
    )
    
    # Print the result
    print("\nCommand output:")
    print(result.stdout)
    
    if result.stderr:
        print("\nError output:")
        print(result.stderr)
    
    # Check if project was created successfully
    expected_project_path = os.path.join(os.getcwd(), "project_test_project")
    if os.path.exists(expected_project_path):
        print(f"\nProject successfully created at: {expected_project_path}")
        
        # List project contents
        print("\nProject contents:")
        for root, dirs, files in os.walk(expected_project_path):
            level = root.replace(expected_project_path, '').count(os.sep)
            indent = ' ' * 4 * level
            print(f"{indent}{os.path.basename(root)}/")
            sub_indent = ' ' * 4 * (level + 1)
            for f in files:
                print(f"{sub_indent}{f}")
                
        # Clean up the created project
        shutil.rmtree(expected_project_path)
        print(f"\nRemoved test project: {expected_project_path}")
    else:
        print(f"\nProject was not created at expected path: {expected_project_path}")
        print("This could indicate an issue with the project creation process.")

finally:
    # Clean up test directory
    shutil.rmtree(test_dir)
    print(f"Removed temporary test directory: {test_dir}")