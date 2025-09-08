"""Pytest configuration for output tests.

This module provides shared fixtures and configuration for all
output package tests.
"""

import pytest
import tempfile
import shutil
from pathlib import Path
from unittest.mock import Mock, MagicMock
from io import StringIO
import sys


@pytest.fixture
def temp_output_dir():
    """Create a temporary directory for output tests."""
    temp_dir = tempfile.mkdtemp(prefix="output_test_")
    yield Path(temp_dir)
    shutil.rmtree(temp_dir, ignore_errors=True)


@pytest.fixture
def mock_output_manager():
    """Create a mock OutputManager for testing."""
    manager = Mock()
    manager.mode = "interactive"
    manager.save_enabled = False
    manager.output_dir = None
    manager.stream = StringIO()
    return manager


@pytest.fixture
def capture_stdout():
    """Capture stdout for testing output."""
    old_stdout = sys.stdout
    sys.stdout = StringIO()
    yield sys.stdout
    sys.stdout = old_stdout


@pytest.fixture
def mock_model():
    """Create a mock model for testing."""
    model = Mock()
    model.N = 3
    model.solver = Mock()
    model.solver.check.return_value = Mock(r=lambda: True)
    return model


@pytest.fixture
def mock_build_module():
    """Create a mock BuildModule for testing."""
    module = Mock()
    module.theory_name = "test_theory"
    module.module_name = "test_module"
    module.examples = []
    return module


@pytest.fixture
def mock_progress_indicator():
    """Create a mock progress indicator."""
    indicator = MagicMock()
    indicator.start = MagicMock()
    indicator.stop = MagicMock()
    indicator.update = MagicMock()
    return indicator


@pytest.fixture(autouse=True)
def cleanup_output():
    """Ensure output streams are cleaned up after each test."""
    yield
    # Flush any remaining output
    sys.stdout.flush()
    sys.stderr.flush()