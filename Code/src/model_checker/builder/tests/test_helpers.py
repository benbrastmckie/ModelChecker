"""
Test helper utilities for builder package tests.

Following TESTING_STANDARDS.md for descriptive assertions.
"""
import os
import sys
from unittest.mock import MagicMock
from model_checker.builder import BuildModule


def create_test_module_with_components(flags=None):
    """
    Create BuildModule with all components initialized.
    
    Args:
        flags: Optional flags object, uses basic test flags if None
        
    Returns:
        BuildModule instance with verified components
        
    Raises:
        AssertionError: If any required component is not initialized
    """
    if flags is None:
        from model_checker.builder.tests.fixtures import TEST_FLAGS_CONFIGS
        flags = TEST_FLAGS_CONFIGS["basic"]
    
    # Create module
    module = BuildModule(flags)
    
    # Verify all components exist with descriptive messages
    assert hasattr(module, 'runner'), "Runner component not initialized on BuildModule"
    assert hasattr(module, 'translation'), "Translation component not initialized on BuildModule"
    assert hasattr(module, 'loader'), "Loader component not initialized on BuildModule"
    
    # Verify comparison only exists when in comparison mode
    if hasattr(flags, 'comparison') and flags.comparison:
        assert hasattr(module, 'comparison'), "Comparison component not initialized despite comparison flag"
    else:
        assert not hasattr(module, 'comparison'), "Comparison component should not exist without comparison flag"
    
    return module


def create_mock_theory_module(theory_name="test_theory", has_semantics=True, has_examples=True):
    """
    Create a mock theory module for testing.
    
    Args:
        theory_name: Name of the theory
        has_semantics: Whether to include semantic class
        has_examples: Whether to include examples
        
    Returns:
        Mock module object with theory attributes
    """
    module = MagicMock()
    module.__name__ = f"model_checker.theory_lib.{theory_name}"
    
    if has_semantics:
        # Create semantic class
        semantics_class = MagicMock()
        semantics_class.__name__ = f"{theory_name.title()}Semantics"
        semantics_class.return_value = MagicMock()  # Instance
        
        # Set it with correct name pattern
        setattr(module, f"{theory_name.title()}Semantics", semantics_class)
        setattr(module, f"{theory_name.upper()}_Semantics", semantics_class)  # Alternative pattern
    
    if has_examples:
        # Create examples list
        module.examples = [
            {
                "name": "test_example_1",
                "settings": {"N": 3},
                "assumptions": [],
                "formula": "A"
            },
            {
                "name": "test_example_2", 
                "settings": {"N": 4},
                "assumptions": ["A"],
                "formula": "(A \\rightarrow B)"
            }
        ]
    
    return module


def verify_component_delegation(module, method_name, component_name):
    """
    Verify that a method properly delegates to a component.
    
    Args:
        module: BuildModule instance
        method_name: Name of the method that should delegate
        component_name: Name of the component ('runner', 'translation', etc.)
        
    Raises:
        AssertionError: If delegation is not properly set up
    """
    # Check component exists
    assert hasattr(module, component_name), \
        f"Component '{component_name}' not found on module"
    
    component = getattr(module, component_name)
    
    # Check method exists on component
    assert hasattr(component, method_name), \
        f"Method '{method_name}' not found on {component_name} component"
    
    # Verify it's callable
    method = getattr(component, method_name)
    assert callable(method), \
        f"{component_name}.{method_name} is not callable"


def create_test_file_structure(base_path, structure):
    """
    Create a test file structure for loader testing.
    
    Args:
        base_path: Base directory path
        structure: Dict describing file structure
        
    Example:
        create_test_file_structure("/tmp/test", {
            "module.py": "# test module",
            "subdir": {
                "__init__.py": "",
                "component.py": "class Component: pass"
            }
        })
    """
    os.makedirs(base_path, exist_ok=True)
    
    for name, content in structure.items():
        path = os.path.join(base_path, name)
        
        if isinstance(content, dict):
            # Subdirectory
            create_test_file_structure(path, content)
        else:
            # File
            with open(path, 'w') as f:
                f.write(content)


def assert_method_migrated(test_case, module, old_path, new_path):
    """
    Assert that a method has been properly migrated to new location.
    
    Args:
        test_case: unittest.TestCase instance for assertions
        module: BuildModule instance
        old_path: Old method path (e.g., "module.run_model_check")
        new_path: New method path (e.g., "module.runner.run_model_check")
    """
    # Parse paths
    old_parts = old_path.split('.')
    new_parts = new_path.split('.')
    
    # Check old method doesn't exist
    if len(old_parts) == 2 and old_parts[0] == "module":
        test_case.assertFalse(
            hasattr(module, old_parts[1]),
            f"Old method {old_parts[1]} still exists on module - should be removed"
        )
    
    # Check new method exists
    current = module
    for i, part in enumerate(new_parts[1:], 1):  # Skip 'module'
        test_case.assertTrue(
            hasattr(current, part),
            f"Migration failed: {'.'.join(new_parts[:i+1])} not found"
        )
        current = getattr(current, part)
    
    # Verify it's callable
    test_case.assertTrue(
        callable(current),
        f"Migrated method {new_path} is not callable"
    )


def capture_test_output(func, *args, **kwargs):
    """
    Capture stdout/stderr from a function call.
    
    Args:
        func: Function to call
        *args: Positional arguments for func
        **kwargs: Keyword arguments for func
        
    Returns:
        tuple: (result, stdout, stderr)
    """
    import io
    from contextlib import redirect_stdout, redirect_stderr
    
    stdout_buffer = io.StringIO()
    stderr_buffer = io.StringIO()
    
    with redirect_stdout(stdout_buffer), redirect_stderr(stderr_buffer):
        result = func(*args, **kwargs)
    
    return result, stdout_buffer.getvalue(), stderr_buffer.getvalue()


def create_progress_callback_mock():
    """
    Create a mock progress callback for testing progress tracking.
    
    Returns:
        Mock object that records all progress calls
    """
    callback = MagicMock()
    callback.calls = []
    
    def record_call(*args, **kwargs):
        callback.calls.append((args, kwargs))
    
    callback.side_effect = record_call
    return callback