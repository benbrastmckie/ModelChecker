#!/usr/bin/env python3
"""
ModelChecker Package Update Script

This script:
1. Updates the version numbers in pyproject.toml and __init__.py
2. Optionally runs tests for all registered theories (using run_tests.py)
3. Builds the package and uploads it to PyPI using twine

Usage:
    python update.py               # Run the update process
    python update.py --no-version  # Skip version increment
    python update.py --no-upload   # Skip the upload step
"""

import os
import re
import sys
import shutil
import importlib.util
import subprocess
from pathlib import Path

def load_module_from_path(module_name, module_path):
    """Load a Python module from a file path."""
    spec = importlib.util.spec_from_file_location(module_name, module_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def get_current_version():
    """Get the current version from pyproject.toml."""
    pyproject_path = Path(__file__).parent / 'pyproject.toml'
    with open(pyproject_path, 'r') as f:
        content = f.read()
    
    match = re.search(r'version = "([^"]+)"', content)
    if match:
        return match.group(1)
    return None

def increment_version(version):
    """Increment the patch number in a version string."""
    if not version:
        return None
    
    # Split the version into parts
    parts = version.split('.')
    if len(parts) < 3:
        return None
    
    # Increment the patch number
    parts[-1] = str(int(parts[-1]) + 1)
    
    # Join back together
    return '.'.join(parts)

def update_version_in_files(current_version, new_version):
    """Update version numbers in pyproject.toml and __init__.py."""
    # Update pyproject.toml
    pyproject_path = Path(__file__).parent / 'pyproject.toml'
    with open(pyproject_path, 'r') as f:
        content = f.read()
    
    content = content.replace(f'version = "{current_version}"', f'version = "{new_version}"')
    
    with open(pyproject_path, 'w') as f:
        f.write(content)
    
    # Update __init__.py
    init_path = Path(__file__).parent / 'src' / 'model_checker' / '__init__.py'
    if init_path.exists():
        with open(init_path, 'r') as f:
            content = f.read()
        
        content = content.replace(f'__version__ = "{current_version}"', f'__version__ = "{new_version}"')
        
        with open(init_path, 'w') as f:
            f.write(content)
    
    print(f"Updated version from {current_version} to {new_version}")

def clean_build_dirs():
    """Delete dist and egg-info directories."""
    # Delete dist directory
    dist_dir = Path(__file__).parent / 'dist'
    if dist_dir.exists():
        shutil.rmtree(dist_dir)
    
    # Delete egg-info directory
    egg_info_dir = Path(__file__).parent / 'src' / 'model_checker.egg-info'
    if egg_info_dir.exists():
        shutil.rmtree(egg_info_dir)
    
    print("Cleaned build directories")

def run_tests():
    """Run package and theory tests using test_package.py and test_theories.py."""
    response = input("Do you want to run tests? (y/N): ").strip().lower()
    if response != 'y':
        print("Skipping tests")
        return True  # Continue with build even without running tests
    
    # First run package tests
    package_tests_script = Path(__file__).parent / 'test_package.py'
    if not package_tests_script.exists():
        print("Error: test_package.py not found")
        return False
    
    # Import the test_package module
    package_tests_module = load_module_from_path('test_package', str(package_tests_script))
    
    # Run package tests
    print("\nRunning package component tests...")
    print("=" * 80)
    package_tests_passed = package_tests_module.run_package_tests() == 0
    
    if not package_tests_passed:
        response = input("\nPackage tests failed. Continue with theory tests? (y/N): ").strip().lower()
        if response != 'y':
            return False  # Stop the process if user chooses not to continue
    
    # Now run theory tests
    theory_tests_script = Path(__file__).parent / 'test_theories.py'
    if not theory_tests_script.exists():
        print("Error: test_theories.py not found")
        return False
    
    # Import the test_theories module
    theory_tests_module = load_module_from_path('test_theories', str(theory_tests_script))
    
    # Run theory tests
    print("\nRunning theory tests...")
    print("=" * 80)
    theory_tests_passed = theory_tests_module.run_tests() == 0
    
    if not theory_tests_passed:
        response = input("\nTheory tests failed. Continue with build and upload anyway? (y/N): ").strip().lower()
        return response == 'y'
    
    if not package_tests_passed:
        # Ask again if package tests failed but theory tests passed
        response = input("\nPackage tests failed, but theory tests passed. Continue with build and upload? (y/N): ").strip().lower()
        return response == 'y'
    
    return True  # All tests passed

def build_package():
    """Build the package using python -m build."""
    print("Building package...")
    result = subprocess.run([sys.executable, '-m', 'build'], cwd=Path(__file__).parent)
    return result.returncode == 0

def upload_package():
    """Upload the package to PyPI using twine."""
    print("Uploading package to PyPI...")
    result = subprocess.run(['twine', 'upload', 'dist/*'], cwd=Path(__file__).parent)
    return result.returncode == 0

def main():
    """Main function to update and release the package."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Update and release the ModelChecker package")
    parser.add_argument('--no-version', action='store_true', help="Skip version number increment")
    parser.add_argument('--no-upload', action='store_true', help="Skip uploading to PyPI")
    args = parser.parse_args()
    
    # Get current version
    current_version = get_current_version()
    if not current_version:
        print("Error: Could not determine current version")
        return 1
    
    # Increment version if requested
    if not args.no_version:
        new_version = increment_version(current_version)
        if not new_version:
            print("Error: Failed to increment version")
            return 1
        
        # Update version in files
        update_version_in_files(current_version, new_version)
    else:
        print("Skipping version increment")
    
    # Clean build directories
    clean_build_dirs()
    
    # Run tests
    if not run_tests():
        print("Aborting due to test failures")
        return 1
    
    # Build package
    if not build_package():
        print("Package build failed")
        return 1
    
    # Upload package if requested
    if not args.no_upload:
        if not upload_package():
            print("Package upload failed")
            return 1
        print("Package uploaded successfully")
    else:
        print("Skipping package upload")
    
    return 0

if __name__ == '__main__':
    sys.exit(main())