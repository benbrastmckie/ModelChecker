"""Global pytest configuration for ModelChecker test suite.

This provides global fixtures and configuration that applies to all tests
across the entire ModelChecker codebase.
"""

import pytest
import glob
import shutil
import atexit
import os


@pytest.fixture(autouse=True, scope='function')
def cleanup_output_directories():
    """Automatically clean up output directories after each test.
    
    This fixture runs automatically for every test function and ensures that
    any output directories created during test execution are cleaned up
    to prevent cluttering the codebase.
    """
    # Store current working directory and initial output directories
    original_cwd = os.getcwd()
    initial_dirs = set(glob.glob('output_*'))
    
    yield  # Run the test
    
    # Clean up any new output directories created during the test
    # (only if we're still in the same directory)
    if os.getcwd() == original_cwd:
        final_dirs = set(glob.glob('output_*'))
        new_dirs = final_dirs - initial_dirs
        
        for output_dir in new_dirs:
            try:
                if os.path.exists(output_dir):
                    shutil.rmtree(output_dir)
            except (OSError, PermissionError):
                # Directory might already be removed or in use
                pass


@pytest.fixture(autouse=True, scope='session')
def cleanup_on_session_end():
    """Clean up any remaining output directories when pytest session ends.
    
    This provides a final cleanup to catch any directories that might
    have been missed by the per-test cleanup.
    """
    def final_cleanup():
        """Remove all output directories from current working directory."""
        for output_dir in glob.glob('output_*'):
            try:
                if os.path.exists(output_dir):
                    shutil.rmtree(output_dir)
            except (OSError, PermissionError):
                # Directory might already be removed or in use
                pass
    
    # Register cleanup to run at interpreter exit
    atexit.register(final_cleanup)
    
    yield  # Run all tests
    
    # Final cleanup when session ends
    final_cleanup()


def pytest_runtest_teardown(item):
    """Hook that runs after each test item completes.
    
    This provides an additional safety net to clean up output directories
    even if the fixture-based cleanup fails.
    """
    # Clean up output directories in current working directory
    for output_dir in glob.glob('output_*'):
        try:
            if os.path.exists(output_dir):
                shutil.rmtree(output_dir)
        except (OSError, PermissionError):
            # Directory might be in use or already removed
            pass


def pytest_sessionfinish(session, exitstatus):
    """Hook that runs when the entire test session is finished.
    
    This is the final opportunity to clean up any output directories
    that might have been created during the test session.
    """
    # Final cleanup of all output directories
    for output_dir in glob.glob('output_*'):
        try:
            if os.path.exists(output_dir):
                shutil.rmtree(output_dir)
        except (OSError, PermissionError):
            # Directory might be in use or already removed
            pass


# Configure pytest to be less verbose about fixtures
def pytest_configure(config):
    """Configure pytest settings."""
    # Suppress warnings about fixtures if desired
    pass