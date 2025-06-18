#!/usr/bin/env python3
"""
ModelChecker Package Update Script

This script:
1. Updates the version numbers in pyproject.toml and __init__.py
2. Optionally runs comprehensive tests using the unified run_tests.py
3. Builds the package and uploads it to PyPI using twine

The testing phase uses the unified test runner which includes:
- Theory examples tests (integration tests from examples.py files)
- Unit tests (component/implementation tests)
- Package tests (framework infrastructure tests)

Usage:
    python run_update.py               # Run the full update process
    python run_update.py --no-version  # Skip version increment
    python run_update.py --no-upload   # Skip the upload step
"""

import os
import re
import sys
import shutil
import subprocess
from pathlib import Path

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
    """Run comprehensive tests using the unified run_tests.py script."""
    response = input("Do you want to run tests before building? (y/N): ").strip().lower()
    if response != 'y':
        print("Skipping tests")
        return True  # Continue with build even without running tests
    
    # Check if the unified test runner exists
    test_runner_script = Path(__file__).parent / 'run_tests.py'
    if not test_runner_script.exists():
        print("Error: run_tests.py not found")
        return False
    
    print("\nRunning comprehensive tests with unified test runner...")
    print("=" * 80)
    
    # Run all tests using the unified test runner
    # This runs examples, unit tests, and package tests for all theories (excluding default)
    result = subprocess.run([
        sys.executable, 
        str(test_runner_script),
        '--verbose'
    ], cwd=Path(__file__).parent)
    
    tests_passed = result.returncode == 0
    
    if not tests_passed:
        print("\n" + "=" * 80)
        print("Some tests failed. You can:")
        print("1. Continue with build anyway (not recommended)")
        print("2. Fix the failing tests and run the update script again")
        print("3. Run specific tests: ./run_tests.py --examples logos modal")
        print("4. Run package tests only: ./run_tests.py --package")
        
        response = input("\nContinue with build and upload despite test failures? (y/N): ").strip().lower()
        return response == 'y'
    
    print("\n" + "=" * 80)
    print("All tests passed successfully!")
    return True

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