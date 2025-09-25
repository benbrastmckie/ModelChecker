#!/usr/bin/env python3
"""
ModelChecker Test PyPI Release Script

This script manages test releases to Test PyPI for the ModelChecker package:
1. Runs all tests BEFORE any version changes
2. Prompts for version increment type (patch/minor/major)
3. Updates version in pyproject.toml with a dev suffix
4. Builds and uploads the package to Test PyPI

This allows testing releases before pushing to production PyPI.

Usage:
    python test_update.py               # Interactive test release process
    python test_update.py --skip-tests  # Skip test execution
    python test_update.py --no-git      # Don't commit changes to git

To install from Test PyPI after upload:
    pip install --index-url https://test.pypi.org/simple/ --extra-index-url https://pypi.org/simple/ model-checker
"""

import os
import re
import sys
import shutil
import subprocess
from pathlib import Path
from typing import Tuple, Optional
from datetime import datetime

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
    # Remove any dev suffix if present
    base_version = version.split('.dev')[0].split('+')[0]
    parts = base_version.split('.')
    if len(parts) != 3:
        raise ValueError(f"Invalid version format: {version}")

    try:
        return tuple(int(p) for p in parts)
    except ValueError:
        raise ValueError(f"Version must contain only numbers: {version}")

def increment_version(current_version: str, increment_type: str) -> str:
    """
    Increment version based on semantic versioning and add dev suffix.

    Args:
        current_version: Current version string (e.g., "1.0.3")
        increment_type: One of "patch", "minor", or "major"

    Returns:
        New version string with dev suffix (e.g., "1.0.4.dev20240101")
    """
    # Parse base version (removing any existing dev suffix)
    base_version = current_version.split('.dev')[0].split('+')[0]
    major, minor, patch = parse_version(base_version)

    if increment_type == "major":
        new_base = f"{major + 1}.0.0"
    elif increment_type == "minor":
        new_base = f"{major}.{minor + 1}.0"
    elif increment_type == "patch":
        new_base = f"{major}.{minor}.{patch + 1}"
    else:
        raise ValueError(f"Invalid increment type: {increment_type}")

    # Add dev suffix with timestamp for uniqueness
    timestamp = datetime.now().strftime("%Y%m%d%H%M%S")
    return f"{new_base}.dev{timestamp}"

def run_tests() -> bool:
    """
    Run comprehensive tests using run_tests.py.

    Returns:
        True if tests pass or user chooses to continue, False to abort
    """
    print("\n" + "=" * 80)
    print("STEP 1: TEST EXECUTION")
    print("=" * 80)

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
        print("⚠️ Some tests failed!")
        print("\nFor Test PyPI uploads, you may want to continue anyway.")

        confirm = input("\nContinue with failing tests? [y/N]: ").strip().lower()
        return confirm == 'y'

def get_version_increment_type(current_version: str) -> Optional[str]:
    """
    Prompt user for the type of version increment.

    Returns:
        One of "patch", "minor", "major", or None if cancelled
    """
    print("\n" + "=" * 80)
    print("STEP 2: VERSION INCREMENT FOR TEST RELEASE")
    print("=" * 80)

    # Remove any existing dev suffix for display
    base_version = current_version.split('.dev')[0].split('+')[0]
    print(f"\nCurrent version: {base_version}")
    print("\nThis will create a development version for Test PyPI.")
    print("\nSelect version increment type:")
    print("1. PATCH - Bug fixes only (x.x.X)")
    print("2. MINOR - New features, backwards compatible (x.X.0)")
    print("3. MAJOR - Breaking changes (X.0.0)")
    print("4. Cancel")

    major, minor, patch = parse_version(base_version)

    # Show what the new version would be (without dev suffix for clarity)
    print("\nNew version would be based on:")
    print(f"  1 → {major}.{minor}.{patch + 1} (patch)")
    print(f"  2 → {major}.{minor + 1}.0 (minor)")
    print(f"  3 → {major + 1}.0.0 (major)")
    print("\n(A dev suffix will be added automatically)")

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
    """
    pyproject_path = Path(__file__).parent / 'pyproject.toml'

    try:
        with open(pyproject_path, 'r') as f:
            content = f.read()

        # Replace version - handle both clean versions and dev versions
        pattern = r'version = "[^"]+"'
        replacement = f'version = "{new_version}"'
        new_content = re.sub(pattern, replacement, content)

        if new_content == content:
            print(f"❌ Error: Could not find version in pyproject.toml")
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

def upload_to_test_pypi() -> bool:
    """Upload the package to Test PyPI."""
    print("\n" + "=" * 80)
    print("STEP 4: UPLOAD TO TEST PYPI")
    print("=" * 80)

    # Check for Test PyPI credentials
    print("\n📋 Checking for Test PyPI credentials...")

    # Check environment variables
    test_token = os.environ.get('TEST_PYPI_API_TOKEN')

    if not test_token:
        print("\n⚠️ TEST_PYPI_API_TOKEN environment variable not set.")
        print("\nTo set it up:")
        print("1. Go to https://test.pypi.org/manage/account/token/")
        print("2. Create an API token (or use existing one)")
        print("3. Set the environment variable:")
        print("   export TEST_PYPI_API_TOKEN=pypi-AgEIcH...")
        print("\nAlternatively, you can enter credentials when prompted by twine.")

        manual = input("\nContinue with manual authentication? [Y/n]: ").strip().lower()
        if manual == 'n':
            return False

    # Install twine if needed
    try:
        import twine
    except ImportError:
        print("\n📦 Installing twine...")
        subprocess.run([sys.executable, '-m', 'pip', 'install', 'twine'], check=True)

    # Upload to Test PyPI
    print("\n📤 Uploading to Test PyPI...")

    dist_dir = Path(__file__).parent / 'dist'

    if test_token:
        # Use token authentication
        env = os.environ.copy()
        env['TWINE_USERNAME'] = '__token__'
        env['TWINE_PASSWORD'] = test_token

        result = subprocess.run([
            sys.executable, '-m', 'twine', 'upload',
            '--repository', 'testpypi',
            '--skip-existing',
            str(dist_dir / '*')
        ], env=env, cwd=Path(__file__).parent)
    else:
        # Let twine prompt for credentials
        result = subprocess.run([
            sys.executable, '-m', 'twine', 'upload',
            '--repository', 'testpypi',
            '--skip-existing',
            str(dist_dir / '*')
        ], cwd=Path(__file__).parent)

    if result.returncode == 0:
        print("\n✅ Successfully uploaded to Test PyPI!")
        return True
    else:
        print("\n❌ Upload to Test PyPI failed")
        return False

def main():
    """Main function to orchestrate the test release process."""
    import argparse

    parser = argparse.ArgumentParser(description="Release ModelChecker to Test PyPI for testing")
    parser.add_argument('--skip-tests', action='store_true', help="Skip test execution")
    parser.add_argument('--no-git', action='store_true', help="Don't commit changes to git")
    args = parser.parse_args()

    print("\n" + "=" * 80)
    print("MODELCHECKER TEST RELEASE PROCESS (Test PyPI)")
    print("=" * 80)
    print("\n⚠️  This will upload to Test PyPI, not production PyPI")
    print("   Use this to test releases before running run_update.py")

    # Step 1: Run tests (optional)
    if not args.skip_tests:
        if not run_tests():
            print("\n❌ Test release aborted")
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
        print("\n❌ Test release cancelled by user")
        return 1

    # Calculate new version with dev suffix
    new_version = increment_version(current_version, increment_type)

    # Confirm with user
    print(f"\n📦 Test Release Summary:")
    print(f"  Current version: {current_version}")
    print(f"  New version:     {new_version}")
    print(f"  Increment type:  {increment_type.upper()}")
    print(f"  Target:          Test PyPI")

    confirm = input("\nProceed with test release? [Y/n]: ").strip().lower()
    if confirm == 'n':
        print("❌ Test release cancelled")
        return 1

    # Step 3: Update version in pyproject.toml
    if not update_version_in_pyproject(current_version, new_version):
        print("❌ Failed to update version")
        return 1

    # Step 4: Clean and build
    clean_build_dirs()
    if not build_package():
        print("❌ Build failed")
        # Revert version change
        update_version_in_pyproject(new_version, current_version)
        return 1

    # Step 5: Upload to Test PyPI
    if not upload_to_test_pypi():
        print("❌ Upload to Test PyPI failed")
        # Revert version change
        update_version_in_pyproject(new_version, current_version)
        return 1

    # Step 6: Instructions for testing
    print("\n" + "=" * 80)
    print("TEST RELEASE COMPLETE!")
    print("=" * 80)

    print(f"\n✅ Version {new_version} has been uploaded to Test PyPI")

    print("\n📥 To install and test from Test PyPI:")
    print("\n  pip install --index-url https://test.pypi.org/simple/ \\")
    print("              --extra-index-url https://pypi.org/simple/ \\")
    print(f"              model-checker=={new_version}")

    print("\n🧪 After testing, if everything works:")

    if not args.no_git:
        # Optionally commit the test version
        print("\n⚠️  Note: The dev version is still in pyproject.toml")
        revert = input("\nRevert to original version? [Y/n]: ").strip().lower()

        if revert != 'n':
            # Revert the version change
            if update_version_in_pyproject(new_version, current_version.split('.dev')[0].split('+')[0]):
                print(f"✅ Reverted to original version: {current_version.split('.dev')[0]}")
            else:
                print("⚠️ Could not revert version, please check pyproject.toml manually")

    print("\n1. Run 'python run_update.py' to create an official release")
    print("2. The official release will trigger GitHub Actions for PyPI upload")

    print("\n📦 Test PyPI package page:")
    print(f"   https://test.pypi.org/project/model-checker/{new_version}/")

    return 0

if __name__ == '__main__':
    sys.exit(main())