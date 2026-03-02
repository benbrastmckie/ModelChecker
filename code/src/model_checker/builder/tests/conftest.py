"""
Pytest configuration and shared fixtures for builder tests.

This provides standardized fixtures and utilities for all builder tests,
reducing duplication and improving consistency.
"""
import pytest
import tempfile
import os
import glob
import atexit
from pathlib import Path
from unittest.mock import Mock, MagicMock
from model_checker.builder.module import BuildModule


@pytest.fixture
def mock_flags():
    """Create a properly configured mock flags object.
    
    Returns a Mock with spec to prevent attribute auto-creation,
    avoiding issues with _parsed_args detection.
    """
    return Mock(
        spec=['file_path', 'print_constraints', 'print_z3', 'save_output',
              'output_mode', 'sequential_files', 'comparison', 'interactive',
              'verbose', 'timeout'],
        # Default values
        print_constraints=False,
        print_z3=False,
        save_output=False,
        comparison=False,
        verbose=False,
        timeout=None
    )


@pytest.fixture
def temp_module_file(tmp_path):
    """Create a minimal valid module file for testing.
    
    Returns:
        Path: Path to the created module file
    """
    module_content = '''
from model_checker.theory_lib import logos

# Get theory with minimal setup
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
    
    module_path = tmp_path / "test_module.py"
    module_path.write_text(module_content)
    return str(module_path)


@pytest.fixture
def build_module(mock_flags, temp_module_file):
    """Create a BuildModule instance with standard test configuration.
    
    Args:
        mock_flags: Fixture providing mock flags
        temp_module_file: Fixture providing module file path
        
    Returns:
        BuildModule: Configured BuildModule instance
    """
    mock_flags.file_path = temp_module_file
    return BuildModule(mock_flags)


@pytest.fixture
def mock_semantic_class():
    """Create a mock semantic class for testing.
    
    Returns a class that follows SemanticDefaults interface.
    """
    class MockSemantics:
        DEFAULT_EXAMPLE_SETTINGS = {"N": 2, "max_time": 5}
        DEFAULT_GENERAL_SETTINGS = {
            "print_constraints": False,
            "print_z3": False,
            "save_output": False,
            "print_impossible": False,
            "maximize": False
        }
        
        def __init__(self):
            pass
    
    return MockSemantics


@pytest.fixture
def mock_theory(mock_semantic_class):
    """Create a mock theory dictionary.
    
    Returns:
        dict: Theory configuration with all required components
    """
    return {
        "semantics": mock_semantic_class,
        "model": MagicMock(),
        "proposition": MagicMock(),
        "operators": {
            "wedge": MagicMock(symbol="∧", arity=2),
            "neg": MagicMock(symbol="¬", arity=1),
        }
    }


@pytest.fixture
def example_case():
    """Standard example case for testing.
    
    Returns:
        list: [assumptions, formulas, settings]
    """
    return [
        ["A"],  # assumptions
        ["(A \\wedge B)"],  # formulas
        {"N": 3, "max_time": 10}  # settings
    ]


@pytest.fixture
def generated_project_dir(tmp_path):
    """Create a mock generated project directory structure.
    
    Returns:
        Path: Root directory of the generated project
    """
    project_dir = tmp_path / "project_test"
    project_dir.mkdir()
    
    # Create expected files
    (project_dir / "__init__.py").write_text("")
    (project_dir / "examples.py").write_text('''
from .semantic import TestSemantics
from .operators import get_operators

semantic_theories = {"Test": {"semantics": TestSemantics}}
example_range = {"TEST": [[], ["A"], {"N": 2}]}
''')
    
    (project_dir / "semantic.py").write_text("class TestSemantics: pass")
    (project_dir / "operators.py").write_text("def get_operators(): return {}")
    
    # Create subdirectories
    (project_dir / "tests").mkdir()
    (project_dir / "notebooks").mkdir()
    
    return project_dir


@pytest.fixture
def mock_output_manager():
    """Create a mock OutputManager for testing output handling."""
    manager = Mock()
    manager.should_save.return_value = False
    manager.create_output_directory = Mock()
    manager.save_example = Mock()
    manager.finalize = Mock()
    return manager


@pytest.fixture
def mock_interactive_manager():
    """Create a mock SequentialSaveManager for testing sequential mode."""
    manager = Mock()
    manager.is_interactive.return_value = False
    manager.prompt_save_mode = Mock()
    manager.prompt_save_model = Mock(return_value=False)
    manager.get_next_model_number = Mock(return_value=1)
    return manager


# Shared test utilities

def create_test_file_structure(base_path, structure):
    """Create a test file structure from a dictionary specification.
    
    Args:
        base_path: Root directory path
        structure: Dict describing the file structure
        
    Example:
        create_test_file_structure("/tmp/test", {
            "module.py": "# content",
            "subdir": {
                "__init__.py": "",
                "file.py": "# more content"
            }
        })
    """
    Path(base_path).mkdir(exist_ok=True)
    
    for name, content in structure.items():
        path = Path(base_path) / name
        
        if isinstance(content, dict):
            # Subdirectory
            path.mkdir(exist_ok=True)
            create_test_file_structure(path, content)
        else:
            # File
            path.write_text(content)


def assert_component_initialized(build_module, component_name, component_class=None):
    """Assert that a component is properly initialized on BuildModule.
    
    Args:
        build_module: BuildModule instance
        component_name: Name of the component attribute
        component_class: Expected class of the component (optional)
    """
    assert hasattr(build_module, component_name), \
        f"Component '{component_name}' not found on BuildModule"
    
    component = getattr(build_module, component_name)
    assert component is not None, \
        f"Component '{component_name}' is None"
    
    if component_class:
        assert isinstance(component, component_class), \
            f"Component '{component_name}' is not instance of {component_class.__name__}"


@pytest.fixture(autouse=True)
def auto_cleanup_output_dirs():
    """Automatically clean up output directories after each test.
    
    This fixture runs automatically for every test and ensures that
    any output directories created during test execution are cleaned up
    to prevent cluttering the codebase.
    """
    # Store initial output directories
    initial_dirs = set(glob.glob('output_*'))
    
    yield  # Run the test
    
    # Clean up any new output directories created during the test
    final_dirs = set(glob.glob('output_*'))
    new_dirs = final_dirs - initial_dirs
    
    for output_dir in new_dirs:
        try:
            import shutil
            shutil.rmtree(output_dir)
        except OSError:
            pass  # Directory might already be removed


@pytest.fixture(scope='session', autouse=True)
def cleanup_output_dirs_on_exit():
    """Clean up any remaining output directories when pytest session ends.
    
    This provides a final cleanup to catch any directories that might
    have been missed by the per-test cleanup.
    """
    def cleanup_all_output_dirs():
        """Remove all output directories from current working directory."""
        import shutil
        for output_dir in glob.glob('output_*'):
            try:
                shutil.rmtree(output_dir)
            except OSError:
                pass  # Directory might already be removed
    
    # Register cleanup to run at exit
    atexit.register(cleanup_all_output_dirs)
    
    yield  # Run all tests
    
    # Final cleanup
    cleanup_all_output_dirs()