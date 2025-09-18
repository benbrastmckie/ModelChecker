#!/usr/bin/env python3
"""
ModelChecker Package Update and Release Script

This script manages the release process for the ModelChecker package:
1. Runs all tests BEFORE any version changes
2. Prompts for version increment type (patch/minor/major)
3. Updates version in pyproject.toml
4. Builds and uploads the package to PyPI

The script follows semantic versioning:
- MAJOR: Incompatible API changes (1.0.0 -> 2.0.0)
- MINOR: New functionality, backwards compatible (1.0.0 -> 1.1.0)
- PATCH: Bug fixes, backwards compatible (1.0.0 -> 1.0.1)

Usage:
    python run_update.py               # Interactive release process
    python run_update.py --skip-tests  # Skip test execution
    python run_update.py --no-upload   # Build but don't upload
    python run_update.py --test-pypi   # Upload to Test PyPI instead
"""

import os
import re
import sys
import shutil
import subprocess
from pathlib import Path
from typing import Tuple, Optional

def get_current_version() -> Optional[str]:
    """Get the current version from pyproject.toml."""
    pyproject_path = Path(__file__).parent / 'pyproject.toml'
    with open(pyproject_path, 'r') as f:
        content = f.read()
    
    match = re.search(r'version = "([^"]+)"', content)
    if match:
        return match.group(1)
    return None

def parse_version(version: str) -> Tuple[int, int, int]:
    """Parse semantic version string into tuple of integers."""
    parts = version.split('.')
    if len(parts) != 3:
        raise ValueError(f"Invalid version format: {version}")
    
    try:
        return tuple(int(p) for p in parts)
    except ValueError:
        raise ValueError(f"Version must contain only numbers: {version}")

def increment_version(current_version: str, increment_type: str) -> str:
    """
    Increment version based on semantic versioning.
    
    Args:
        current_version: Current version string (e.g., "1.0.3")
        increment_type: One of "patch", "minor", or "major"
    
    Returns:
        New version string
    """
    major, minor, patch = parse_version(current_version)
    
    if increment_type == "major":
        return f"{major + 1}.0.0"
    elif increment_type == "minor":
        return f"{major}.{minor + 1}.0"
    elif increment_type == "patch":
        return f"{major}.{minor}.{patch + 1}"
    else:
        raise ValueError(f"Invalid increment type: {increment_type}")

def run_tests() -> bool:
    """
    Run comprehensive tests using run_tests.py.
    
    Returns:
        True if tests pass or user chooses to continue, False to abort
    """
    print("\n" + "=" * 80)
    print("STEP 1: TEST EXECUTION")
    print("=" * 80)
    
    # Ask if user wants to run tests
    response = input("\nRun all tests before proceeding? (recommended) [Y/n]: ").strip().lower()
    if response == 'n':
        print("\n⚠️  WARNING: Skipping tests is not recommended for releases!")
        confirm = input("Are you sure you want to skip tests? [y/N]: ").strip().lower()
        if confirm != 'y':
            print("Good choice! Running tests...")
        else:
            print("Skipping tests at your own risk...")
            return True
    
    # Check if run_tests.py exists
    test_runner = Path(__file__).parent / 'run_tests.py'
    if not test_runner.exists():
        print("❌ Error: run_tests.py not found")
        print("Cannot proceed without test runner")
        return False
    
    print("\nRunning comprehensive test suite...")
    print("-" * 40)
    
    # Run all tests
    result = subprocess.run([
        sys.executable,
        str(test_runner),
        '--verbose'
    ], cwd=Path(__file__).parent)
    
    if result.returncode == 0:
        print("\n" + "-" * 40)
        print("✅ All tests passed successfully!")
        return True
    else:
        print("\n" + "-" * 40)
        print("❌ Some tests failed!")
        print("\nOptions:")
        print("1. Fix the failing tests and run this script again (recommended)")
        print("2. Continue anyway (not recommended for releases)")
        print("3. Abort the release process")
        
        while True:
            choice = input("\nYour choice [1/2/3]: ").strip()
            if choice == '1':
                print("Please fix the tests and run this script again.")
                return False
            elif choice == '2':
                confirm = input("⚠️  Are you SURE you want to continue with failing tests? [y/N]: ").strip().lower()
                return confirm == 'y'
            elif choice == '3':
                print("Aborting release process.")
                return False
            else:
                print("Invalid choice. Please enter 1, 2, or 3.")

def get_version_increment_type(current_version: str) -> Optional[str]:
    """
    Prompt user for the type of version increment.
    
    Returns:
        One of "patch", "minor", "major", or None if cancelled
    """
    print("\n" + "=" * 80)
    print("STEP 2: VERSION INCREMENT")
    print("=" * 80)
    
    print(f"\nCurrent version: {current_version}")
    print("\nSelect version increment type:")
    print("1. PATCH - Bug fixes only (x.x.X)")
    print("2. MINOR - New features, backwards compatible (x.X.0)")
    print("3. MAJOR - Breaking changes (X.0.0)")
    print("4. Cancel")
    
    major, minor, patch = parse_version(current_version)
    
    # Show what the new version would be
    print("\nNew version would be:")
    print(f"  1 → {major}.{minor}.{patch + 1} (patch)")
    print(f"  2 → {major}.{minor + 1}.0 (minor)")
    print(f"  3 → {major + 1}.0.0 (major)")
    
    while True:
        choice = input("\nYour choice [1/2/3/4]: ").strip()
        
        if choice == '1':
            return 'patch'
        elif choice == '2':
            return 'minor'
        elif choice == '3':
            return 'major'
        elif choice == '4':
            return None
        else:
            print("Invalid choice. Please enter 1, 2, 3, or 4.")

def update_version_in_pyproject(current_version: str, new_version: str) -> bool:
    """
    Update version in pyproject.toml.
    
    Note: __init__.py uses get_model_checker_version() which reads from 
    package metadata, so it doesn't need manual updating.
    """
    pyproject_path = Path(__file__).parent / 'pyproject.toml'
    
    try:
        with open(pyproject_path, 'r') as f:
            content = f.read()
        
        # Replace version
        pattern = f'version = "{re.escape(current_version)}"'
        replacement = f'version = "{new_version}"'
        new_content = re.sub(pattern, replacement, content)
        
        if new_content == content:
            print(f"❌ Error: Could not find version {current_version} in pyproject.toml")
            return False
        
        with open(pyproject_path, 'w') as f:
            f.write(new_content)
        
        print(f"✅ Updated version: {current_version} → {new_version}")
        return True
        
    except Exception as e:
        print(f"❌ Error updating pyproject.toml: {e}")
        return False

def clean_build_dirs():
    """Delete dist and egg-info directories."""
    dist_dir = Path(__file__).parent / 'dist'
    if dist_dir.exists():
        shutil.rmtree(dist_dir)
    
    egg_info_dir = Path(__file__).parent / 'src' / 'model_checker.egg-info'
    if egg_info_dir.exists():
        shutil.rmtree(egg_info_dir)
    
    print("✅ Cleaned build directories")

def build_package() -> bool:
    """Build the package using python -m build."""
    print("\n" + "=" * 80)
    print("STEP 3: BUILD PACKAGE")
    print("=" * 80)
    
    print("\nBuilding package distributions...")
    result = subprocess.run([sys.executable, '-m', 'build'], cwd=Path(__file__).parent)
    
    if result.returncode == 0:
        print("✅ Package built successfully")
        
        # List the built files
        dist_dir = Path(__file__).parent / 'dist'
        if dist_dir.exists():
            files = list(dist_dir.glob('*'))
            print("\nBuilt files:")
            for f in files:
                size_kb = f.stat().st_size / 1024
                print(f"  - {f.name} ({size_kb:.1f} KB)")
        
        return True
    else:
        print("❌ Package build failed")
        return False

def upload_package(test_pypi: bool = False) -> bool:
    """
    Upload the package to PyPI or Test PyPI.
    
    Args:
        test_pypi: If True, upload to Test PyPI instead of production
    """
    print("\n" + "=" * 80)
    print(f"STEP 4: UPLOAD TO {'TEST ' if test_pypi else ''}PYPI")
    print("=" * 80)
    
    repository = "testpypi" if test_pypi else "pypi"
    
    print(f"\nUploading to {repository}...")
    
    cmd = ['twine', 'upload']
    if test_pypi:
        cmd.extend(['--repository', 'testpypi'])
    cmd.append('dist/*')
    
    result = subprocess.run(cmd, cwd=Path(__file__).parent)
    
    if result.returncode == 0:
        print(f"\n✅ Package uploaded successfully to {repository}!")
        
        if test_pypi:
            print("\nTo test installation:")
            print("pip install --index-url https://test.pypi.org/simple/ --extra-index-url https://pypi.org/simple/ model-checker")
        else:
            print("\nTo install the new version:")
            print("pip install --upgrade model-checker")
        
        return True
    else:
        print(f"❌ Failed to upload to {repository}")
        return False

def main():
    """Main function to orchestrate the release process."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Release ModelChecker package with semantic versioning")
    parser.add_argument('--skip-tests', action='store_true', help="Skip test execution (not recommended)")
    parser.add_argument('--no-upload', action='store_true', help="Build but don't upload to PyPI")
    parser.add_argument('--test-pypi', action='store_true', help="Upload to Test PyPI instead of production")
    args = parser.parse_args()
    
    print("\n" + "=" * 80)
    print("MODELCHECKER RELEASE PROCESS")
    print("=" * 80)
    
    # Step 1: Run tests BEFORE any changes
    if not args.skip_tests:
        if not run_tests():
            print("\n❌ Release aborted due to test failures")
            return 1
    else:
        print("\n⚠️  Skipping tests as requested")
    
    # Step 2: Get current version and ask for increment type
    current_version = get_current_version()
    if not current_version:
        print("❌ Error: Could not determine current version from pyproject.toml")
        return 1
    
    increment_type = get_version_increment_type(current_version)
    if not increment_type:
        print("\n❌ Release cancelled by user")
        return 1
    
    # Calculate new version
    new_version = increment_version(current_version, increment_type)
    
    # Confirm with user
    print(f"\n📦 Release Summary:")
    print(f"  Current version: {current_version}")
    print(f"  New version:     {new_version}")
    print(f"  Increment type:  {increment_type.upper()}")
    
    if increment_type in ['minor', 'major']:
        print(f"\n✨ Note: {increment_type.capitalize()} releases will automatically")
        print("   trigger PyPI upload when you push the tag to GitHub!")
    else:
        print(f"\n📝 Note: Patch releases will NOT auto-upload to PyPI")
        print("   (but you can still upload manually with this script)")
    
    confirm = input("\nProceed with version update? [Y/n]: ").strip().lower()
    if confirm == 'n':
        print("❌ Release cancelled")
        return 1
    
    # Step 3: Update version in pyproject.toml
    if not update_version_in_pyproject(current_version, new_version):
        print("❌ Failed to update version")
        return 1
    
    # Step 4: Clean and build
    clean_build_dirs()
    if not build_package():
        print("❌ Build failed")
        return 1
    
    # Step 5: Upload if requested
    if not args.no_upload:
        if not upload_package(test_pypi=args.test_pypi):
            print("❌ Upload failed")
            return 1
    else:
        print("\n📦 Package built but not uploaded (--no-upload flag)")
    
    # Step 6: Provide git instructions and next steps
    print("\n" + "=" * 80)
    print("NEXT STEPS")
    print("=" * 80)
    
    print("\n📝 Git commands to finalize release:")
    print(f"\n  git add Code/pyproject.toml")
    print(f"  git commit -m 'Release version {new_version}'")
    
    if increment_type in ['minor', 'major']:
        print(f"  git tag v{new_version}")
        print(f"  git push origin main --tags")
        
        print("\n" + "=" * 80)
        print("AUTOMATIC PYPI RELEASE")
        print("=" * 80)
        
        print(f"\n✨ {increment_type.upper()} RELEASE DETECTED - Automatic PyPI upload will occur!")
        print("\nWhat happens next:")
        print("1. GitHub Actions will detect the version tag")
        print("2. The workflow will run all tests across 15 environments")
        print("3. If ALL tests pass, the package will be automatically uploaded to PyPI")
        print("4. You'll receive a notification when complete")
        
        print("\n📋 Workflow location:")
        print("  .github/workflows/pypi-release.yml")
        
        print("\n🔍 Monitor progress at:")
        print("  https://github.com/benbrastmckie/ModelChecker/actions")
        
        print("\n⚠️  IMPORTANT: PyPI upload will ONLY happen if:")
        print("  - All tests pass on all platforms (Linux, macOS, Windows)")
        print("  - All Python versions pass (3.8, 3.9, 3.10, 3.11, 3.12)")
        print("  - The PYPI_API_TOKEN secret is properly configured")
        
        print("\n📦 Alternative: Manual upload with twine (if needed):")
        print("  cd Code")
        print("  twine upload dist/*")
        print("\n  (Use this if GitHub Actions fails or you need immediate release)")
    else:
        print(f"  git push origin main")
        
        print("\n" + "=" * 80)
        print("PATCH RELEASE")
        print("=" * 80)
        
        print(f"\n📝 PATCH RELEASE - No automatic PyPI upload")
        print("\nThis patch version will NOT be automatically uploaded to PyPI.")
        print("The changes will be in GitHub but not on PyPI.")
        
        print("\n📦 To manually upload this patch to PyPI:")
        print("  cd Code")
        print("  twine upload dist/*")
        
        print("\n💡 Tip: Save patches for minor releases unless critical fix needed")
    
    print("\n✅ Release process complete!")
    return 0

if __name__ == '__main__':
    sys.exit(main())