"""Pytest configuration for ModelChecker integration tests.

This module provides test isolation, cleanup fixtures, and shared utilities
for all integration tests in the ModelChecker framework.
"""

import pytest
import tempfile
import shutil
import os
import sys
import glob
from pathlib import Path
from unittest.mock import Mock

# Add src to path for testing
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))


@pytest.fixture(autouse=True)
def test_isolation():
    """Ensure test isolation with cleanup.
    
    This fixture runs automatically for every test to ensure proper isolation
    between tests by capturing and restoring system state.
    """
    # Store initial state
    initial_cwd = os.getcwd()
    initial_path = sys.path.copy()
    initial_modules = set(sys.modules.keys())
    
    yield
    
    # Restore state
    os.chdir(initial_cwd)
    sys.path[:] = initial_path
    
    # Clean up imported modules
    current_modules = set(sys.modules.keys())
    new_modules = current_modules - initial_modules
    for module in new_modules:
        if module.startswith('model_checker'):
            sys.modules.pop(module, None)


@pytest.fixture(autouse=True)
def cleanup_test_artifacts():
    """Clean up any test artifacts created during test execution.
    
    This fixture automatically tracks and removes artifacts created during
    test execution to prevent test pollution and disk space issues.
    """
    # Track artifacts created
    initial_test_files = set(glob.glob('test_*'))
    initial_output_dirs = set(glob.glob('output_*'))
    initial_temp_files = set(glob.glob('tmp_*'))
    
    yield
    
    # Clean up new artifacts
    artifacts_to_clean = [
        ('test_*', initial_test_files),
        ('output_*', initial_output_dirs),
        ('tmp_*', initial_temp_files),
    ]
    
    for pattern, initial_set in artifacts_to_clean:
        current_items = set(glob.glob(pattern))
        new_items = current_items - initial_set
        
        for item in new_items:
            try:
                if os.path.isdir(item):
                    shutil.rmtree(item)
                else:
                    os.remove(item)
            except (OSError, PermissionError):
                # Some files may be locked or already removed
                pass


@pytest.fixture
def temp_test_dir():
    """Provide temporary directory for test isolation.
    
    Creates a temporary directory that is automatically cleaned up
    after the test completes.
    
    Returns:
        Path: Path object pointing to the temporary directory
    """
    with tempfile.TemporaryDirectory(prefix='test_mc_') as tmpdir:
        yield Path(tmpdir)


@pytest.fixture
def mock_theory():
    """Provide mock theory for testing.
    
    Creates a mock theory object with all required components for testing
    without requiring actual theory implementations.
    
    Returns:
        dict: Mock theory dictionary with required components
    """
    from tests.fixtures.mock_theories import create_mock_theory
    return create_mock_theory()


@pytest.fixture
def test_module_content():
    """Provide standard test module content.
    
    Returns:
        str: Valid Python module content for testing
    """
    return '''
from model_checker.theory_lib import logos

# Get theory
theory = logos.get_theory(['extensional'])

# Required attributes
semantic_theories = {
    "TestTheory": theory
}

example_range = {
    "TEST_EXAMPLE": [
        [],  # assumptions
        ["A"],  # formula
        {"N": 2}  # settings
    ]
}

general_settings = {
    "print_constraints": False,
    "print_z3": False,
    "save_output": False
}
'''


@pytest.fixture
def cli_runner():
    """Provide CLI runner for testing command-line interface.
    
    Returns:
        callable: Function to run CLI commands with captured output
    """
    import subprocess
    
    def run_cli(*args, capture_output=True, check=False):
        """Run ModelChecker CLI command and return result."""
        cmd = [sys.executable, '-m', 'model_checker'] + list(args)
        
        result = subprocess.run(
            cmd,
            capture_output=capture_output,
            text=True,
            check=check,
            cwd=Path(__file__).parent.parent
        )
        
        return result
    
    return run_cli


@pytest.fixture
def example_formulas():
    """Provide standard test formulas.
    
    Returns:
        dict: Dictionary of formula categories with examples
    """
    return {
        'valid': [
            "(A \\wedge B)",
            "\\Box (A \\rightarrow B)",
            "\\neg (A \\vee B)",
            "(A \\rightarrow (B \\rightarrow A))",
        ],
        'invalid': [
            "(A ∧ B)",  # Unicode instead of LaTeX
            "A \\wedge B",  # Missing parentheses
            "(A \\wedge)",  # Incomplete
            "\\Box \\Box",  # Missing proposition
        ],
        'modal': [
            "\\Box A",
            "\\Diamond B",
            "\\Box (A \\rightarrow \\Diamond B)",
        ],
        'complex': [
            "((A \\wedge B) \\rightarrow (C \\vee D))",
            "\\Box ((A \\vee B) \\rightarrow \\Diamond C)",
            "\\neg \\Box \\neg (A \\wedge B)",
        ]
    }


@pytest.fixture
def test_settings():
    """Provide standard test settings configurations.
    
    Returns:
        dict: Dictionary of settings configurations for different test scenarios
    """
    return {
        'minimal': {
            'N': 2,
            'max_time': 1
        },
        'standard': {
            'N': 3,
            'max_time': 10,
            'print_constraints': False
        },
        'complex': {
            'N': 5,
            'max_time': 30,
            'print_constraints': True,
            'print_z3': False
        },
        'debug': {
            'N': 3,
            'max_time': 10,
            'print_constraints': True,
            'print_z3': True,
            'print_impossible': True
        }
    }


# Test markers for categorizing tests
def pytest_configure(config):
    """Configure custom pytest markers."""
    config.addinivalue_line(
        "markers", "slow: marks tests as slow (deselect with '-m \"not slow\"')"
    )
    config.addinivalue_line(
        "markers", "integration: marks tests as integration tests"
    )
    config.addinivalue_line(
        "markers", "unit: marks tests as unit tests"
    )
    config.addinivalue_line(
        "markers", "e2e: marks tests as end-to-end tests"
    )
    config.addinivalue_line(
        "markers", "requires_z3: marks tests that require Z3 solver"
    )