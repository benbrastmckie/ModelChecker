"""
Shared test fixtures and utilities for builder package tests.

This module provides standardized test data, mock objects, and helper functions
to ensure consistent testing across the builder package, following TESTING_STANDARDS.md.
"""
import os
import tempfile
from pathlib import Path
from unittest.mock import Mock
from typing import Dict, List, Optional, Any


# =============================================================================
# Test Data Constants
# =============================================================================

# Valid formula examples for testing
VALID_FORMULAS = [
    "A",
    "B",
    "(A \\wedge B)",
    "(A \\vee B)",
    "\\neg A",
    "(A \\rightarrow B)",
    "(A \\leftrightarrow B)",
    "\\Box A",
    "\\Diamond B",
    "\\Box (A \\rightarrow B)",
    "(\\Box A \\rightarrow \\Box B)",
]

# Invalid formula examples
INVALID_FORMULAS = [
    "",                    # Empty
    "∧",                  # Unicode operator
    "(A ∧ B)",            # Unicode in formula
    "a",                  # Lowercase proposition
    "(A B)",              # Missing operator
    "\\Box",              # Operator without operand
    "(A \\wedge)",        # Missing operand
    "((A))",              # Extra parentheses
]

# Valid settings configurations
VALID_SETTINGS = [
    {"N": 2},
    {"N": 3, "contingent": True},
    {"N": 4, "reflexive": True, "symmetric": True},
    {"N": 2, "expectation": False},
    {"N": 5, "print_constraints": True},
]

# Invalid settings configurations
INVALID_SETTINGS = [
    {"N": -1},                    # Negative N
    {"N": 0},                     # Zero N
    {"N": 1.5},                   # Non-integer N
    {"N": "2"},                   # String N
    {"N": 65},                    # N too large for bit vectors
    {},                           # Missing N
    {"contingent": True},         # Missing N with other settings
]

# Theory names for testing
THEORY_NAMES = ["logos", "exclusion", "imposition", "bimodal", "test_theory"]

# Valid build configurations for testing
VALID_BUILD_CONFIGS = [
    {
        "module_name": "test_module",
        "module_path": "/test/path/test_module.py",
        "N": 4,
        "comparison": False
    },
    {
        "module_name": "logos",
        "module_path": None,  # Use theory discovery
        "N": 3,
        "comparison": True
    },
    {
        "module_name": "exclusion",
        "module_path": None,
        "N": 5,
        "comparison": False
    },
]

# Invalid configurations for error testing
INVALID_BUILD_CONFIGS = [
    {
        "module_name": "",  # Empty name
        "N": 4
    },
    {
        "module_name": "test",
        "N": -1  # Invalid N value
    },
    {
        "module_name": "test",
        "N": 65  # N too large for bit vectors
    },
]

# Example module content
EXAMPLE_MODULE_CONTENT = '''"""Test module for builder tests."""
from model_checker.theory_lib.logos import get_theory

theory = get_theory(["extensional"])

semantic_theories = {
    "Test Theory": theory
}

example_range = {
    "TEST_1": [["A"], ["B"], {"N": 2}],
    "TEST_2": [["(A \\wedge B)"], ["A"], {"N": 3}],
}

general_settings = {}
'''

# Example test cases for model checking
TEST_EXAMPLE_CASES = [
    {
        "name": "simple_validity",
        "settings": {"N": 3},
        "assumptions": [],
        "formula": "(A \\rightarrow A)",
        "expected": "valid"
    },
    {
        "name": "countermodel_exists",
        "settings": {"N": 2},
        "assumptions": ["A"],
        "formula": "B",
        "expected": "invalid"
    },
    {
        "name": "modal_formula",
        "settings": {"N": 3},
        "assumptions": [],
        "formula": "\\Box A \\rightarrow A",
        "expected": "depends_on_theory"
    },
]

# Method migration mappings for test updates
TEST_METHOD_MIGRATIONS = {
    # Old method -> New method
    'module.run_model_check': 'module.runner.run_model_check',
    'module.try_single_N': 'module.runner.try_single_N',
    'module.process_example': 'module.runner.process_example',
    'module.process_iterations': 'module.runner.process_iterations',
    'module.translate': 'module.translation.translate',
    'module.compare_semantics': 'module.comparison.compare_semantics',
    'module.run_comparison': 'module.comparison.run_comparison',
    'module._find_max_N': 'module.comparison._find_max_N',
    'module.load_module': 'module.loader.load_module',
    'module.discover_theory_module': 'module.loader.discover_theory_module',
    'module.find_project_directory': 'module.loader.find_project_directory',
}

# Z3 test contexts for isolation testing
Z3_TEST_CONTEXTS = [
    {"timeout": 1000},
    {"timeout": 5000},
    {"timeout": None},
]

# Common error messages for assertions
ERROR_MESSAGES = {
    "module_not_found": "Module not found: {}",
    "invalid_formula": "Invalid formula syntax: {}",
    "invalid_settings": "Invalid settings configuration: {}",
    "import_error": "Failed to import module: {}",
    "validation_error": "Validation failed: {}",
}


# =============================================================================
# Mock Object Factories
# =============================================================================

def create_mock_flags(**kwargs) -> Mock:
    """Create a properly configured mock flags object.
    
    Args:
        **kwargs: Override default flag values
        
    Returns:
        Mock: Configured flags object
    """
    defaults = {
        'file_path': '/tmp/test_module.py',
        'print_constraints': False,
        'print_z3': False,
        'save_output': False,
        'output_mode': 'single',
        'sequential_files': False,
        'comparison': False,
        'interactive': False,
        'verbose': False,
        'timeout': 30000,
        'use_project': None,
        'list': None,
    }
    defaults.update(kwargs)
    
    # Create mock with proper spec
    mock = Mock(
        spec=list(defaults.keys()),
        **defaults
    )
    return mock


def create_mock_theory(**kwargs) -> Mock:
    """Create a mock semantic theory object.
    
    Args:
        **kwargs: Override default theory attributes
        
    Returns:
        Mock: Configured theory object
    """
    defaults = {
        'operators': {
            'negation': Mock(symbol='\\neg', arity=1),
            'conjunction': Mock(symbol='\\wedge', arity=2),
        },
        'settings': {'N': 3},
        'validate_model': Mock(return_value=True),
        'check_validity': Mock(return_value=(True, None)),
    }
    
    for key, value in kwargs.items():
        if key in defaults:
            if isinstance(defaults[key], dict) and isinstance(value, dict):
                defaults[key].update(value)
            else:
                defaults[key] = value
    
    return Mock(**defaults)


def create_mock_module(name: str = "test_module", **kwargs) -> Mock:
    """Create a mock module object.
    
    Args:
        name: Module name
        **kwargs: Module attributes
        
    Returns:
        Mock: Configured module object
    """
    module = Mock()
    module.__name__ = name
    
    # Set default attributes
    module.semantic_theories = kwargs.get('semantic_theories', {"Test": create_mock_theory()})
    module.example_range = kwargs.get('example_range', {"TEST": [["A"], ["B"], {"N": 2}]})
    module.general_settings = kwargs.get('general_settings', {})
    
    return module


# =============================================================================
# File System Helpers
# =============================================================================

def create_temp_module_file(content: str = None) -> str:
    """Create a temporary Python module file.
    
    Args:
        content: Module content (uses EXAMPLE_MODULE_CONTENT if None)
        
    Returns:
        str: Path to created file
    """
    content = content or EXAMPLE_MODULE_CONTENT
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
        f.write(content)
        return f.name


def create_test_project_structure(base_dir: str = None) -> Dict[str, str]:
    """Create a test project directory structure.
    
    Args:
        base_dir: Base directory (creates temp if None)
        
    Returns:
        Dict[str, str]: Mapping of file type to path
    """
    if base_dir is None:
        base_dir = tempfile.mkdtemp(prefix="test_project_")
    
    project_dir = Path(base_dir)
    project_dir.mkdir(exist_ok=True)
    
    # Create standard project structure
    files = {
        'semantic': project_dir / 'semantic.py',
        'examples': project_dir / 'examples.py',
        'settings': project_dir / 'settings.toml',
        '__init__': project_dir / '__init__.py',
    }
    
    # Create files with basic content
    files['semantic'].write_text('"""Semantic module."""\nclass TestSemantics: pass')
    files['examples'].write_text(EXAMPLE_MODULE_CONTENT)
    files['settings'].write_text('[settings]\nN = 3')
    files['__init__'].write_text('"""Test project."""')
    
    return {k: str(v) for k, v in files.items()}


# =============================================================================
# Test Data Generators
# =============================================================================

def generate_test_cases(pattern: str = "TEST", count: int = 3) -> Dict[str, List]:
    """Generate example test cases.
    
    Args:
        pattern: Name pattern for test cases
        count: Number of test cases
        
    Returns:
        Dict[str, List]: Example range dictionary
    """
    test_cases = {}
    
    for i in range(count):
        premises = [f"P_{i}"] if i == 0 else [f"(P_{i} \\wedge P_{i+1})"]
        conclusions = [f"P_{i}"]
        settings = {"N": i + 2}
        
        test_cases[f"{pattern}_{i+1}"] = [premises, conclusions, settings]
    
    return test_cases


def generate_operator_map(include_modal: bool = True) -> Dict[str, Any]:
    """Generate a standard operator map.
    
    Args:
        include_modal: Whether to include modal operators
        
    Returns:
        Dict[str, Any]: Operator definitions
    """
    operators = {
        'negation': Mock(symbol='\\neg', arity=1),
        'conjunction': Mock(symbol='\\wedge', arity=2),
        'disjunction': Mock(symbol='\\vee', arity=2),
        'implication': Mock(symbol='\\rightarrow', arity=2),
        'biconditional': Mock(symbol='\\leftrightarrow', arity=2),
    }
    
    if include_modal:
        operators.update({
            'box': Mock(symbol='\\Box', arity=1),
            'diamond': Mock(symbol='\\Diamond', arity=1),
        })
    
    return operators


# =============================================================================
# Assertion Helpers
# =============================================================================

def assert_valid_module_structure(module: Any, test_case: Any) -> None:
    """Assert that a module has valid structure.
    
    Args:
        module: Module to check
        test_case: TestCase instance for assertions
    """
    test_case.assertTrue(
        hasattr(module, 'semantic_theories'),
        "Module missing semantic_theories attribute"
    )
    test_case.assertTrue(
        hasattr(module, 'example_range'),
        "Module missing example_range attribute"
    )
    test_case.assertIsInstance(
        module.semantic_theories, dict,
        "semantic_theories must be a dictionary"
    )
    test_case.assertIsInstance(
        module.example_range, dict,
        "example_range must be a dictionary"
    )


def assert_valid_theory_structure(theory: Any, test_case: Any) -> None:
    """Assert that a theory has valid structure.
    
    Args:
        theory: Theory to check
        test_case: TestCase instance for assertions
    """
    required_methods = ['validate_model', 'check_validity']
    for method in required_methods:
        test_case.assertTrue(
            hasattr(theory, method),
            f"Theory missing required method: {method}"
        )
    
    test_case.assertTrue(
        hasattr(theory, 'operators'),
        "Theory missing operators attribute"
    )


def assert_error_message_contains(error: Exception, substring: str, test_case: Any) -> None:
    """Assert that an error message contains expected substring.
    
    Args:
        error: The exception
        substring: Expected substring
        test_case: TestCase instance for assertions
    """
    error_message = str(error)
    test_case.assertIn(
        substring, error_message,
        f"Error message '{error_message}' does not contain '{substring}'"
    )


# =============================================================================
# Cleanup Utilities
# =============================================================================

class TempFileCleanup:
    """Context manager for automatic temp file cleanup."""
    
    def __init__(self):
        self.files = []
        self.dirs = []
    
    def add_file(self, path: str) -> str:
        """Add a file to be cleaned up."""
        self.files.append(path)
        return path
    
    def add_dir(self, path: str) -> str:
        """Add a directory to be cleaned up."""
        self.dirs.append(path)
        return path
    
    def __enter__(self):
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        # Clean up files
        for file_path in self.files:
            try:
                os.unlink(file_path)
            except (OSError, FileNotFoundError):
                pass
        
        # Clean up directories
        for dir_path in self.dirs:
            try:
                import shutil
                shutil.rmtree(dir_path)
            except (OSError, FileNotFoundError):
                pass


# =============================================================================
# Test Decorators
# =============================================================================

def requires_z3(test_func):
    """Decorator to skip tests if z3 is not available."""
    def wrapper(*args, **kwargs):
        try:
            import z3
            return test_func(*args, **kwargs)
        except ImportError:
            args[0].skipTest("z3 not available")
    return wrapper


def with_temp_files(test_func):
    """Decorator to automatically clean up temp files."""
    def wrapper(*args, **kwargs):
        with TempFileCleanup() as cleanup:
            # Inject cleanup into test
            kwargs['cleanup'] = cleanup
            return test_func(*args, **kwargs)
    return wrapper


# =============================================================================
# Legacy Support
# =============================================================================

# Keep old TEST_FLAGS_CONFIGS for backward compatibility
TEST_FLAGS_CONFIGS = {
    "basic": create_mock_flags(
        comparison=False,
        verbose=False,
        interactive=False
    ),
    
    "comparison": create_mock_flags(
        comparison=True,
        verbose=True,
        interactive=False
    ),
    
    "interactive": create_mock_flags(
        comparison=False,
        verbose=False,
        interactive=True
    ),
}