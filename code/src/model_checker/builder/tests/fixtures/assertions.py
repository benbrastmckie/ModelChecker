"""
Custom assertion helpers for builder test suite.

Provides reusable assertion functions with descriptive error messages
for common testing patterns.
"""

import unittest
from typing import Any, Dict, List, Optional, Union


def assert_valid_theory_structure(test_case: unittest.TestCase, 
                                theory: Dict[str, Any], 
                                theory_name: str = "") -> None:
    """Assert that theory dictionary has all required components.
    
    Args:
        test_case: Test case instance for assertions
        theory: Theory dictionary to validate
        theory_name: Optional name for better error messages
    """
    required_keys = ["semantics", "proposition", "model", "operators"]
    name_prefix = f"Theory {theory_name} " if theory_name else "Theory "
    
    test_case.assertIsInstance(theory, dict,
                             f"{name_prefix}must be a dictionary")
    
    for key in required_keys:
        test_case.assertIn(key, theory,
                          f"{name_prefix}missing required key: {key}")
    
    # Validate operators structure if present
    if "operators" in theory:
        test_case.assertIsInstance(theory["operators"], dict,
                                 f"{name_prefix}operators must be a dictionary")
    
    # Validate dictionary structure if present
    if "dictionary" in theory:
        test_case.assertIsInstance(theory["dictionary"], dict,
                                 f"{name_prefix}dictionary must be a dictionary")


def assert_build_module_initialized(test_case: unittest.TestCase, 
                                  build_module: Any) -> None:
    """Assert that BuildModule has all components properly initialized.
    
    Args:
        test_case: Test case instance for assertions
        build_module: BuildModule instance to validate
    """
    test_case.assertIsNotNone(build_module,
                             "BuildModule instance should not be None")
    
    components = ["loader", "runner", "comparison", "translation"]
    for component in components:
        test_case.assertTrue(hasattr(build_module, component),
                           f"BuildModule missing component: {component}")
        
        component_instance = getattr(build_module, component)
        test_case.assertIsNotNone(component_instance,
                                f"BuildModule component {component} is None")


def assert_error_message_contains(test_case: unittest.TestCase,
                                exception: Exception,
                                expected_text: str,
                                context: str = "") -> None:
    """Assert that exception message contains expected text.
    
    Args:
        test_case: Test case instance for assertions
        exception: Exception instance to check
        expected_text: Text that should be in error message
        context: Optional context for better error messages
    """
    error_msg = str(exception).lower()
    expected_lower = expected_text.lower()
    
    context_prefix = f"{context} - " if context else ""
    
    test_case.assertIn(expected_lower, error_msg,
                      f"{context_prefix}Expected error message to contain "
                      f"'{expected_text}', but got: {str(exception)}")


def assert_component_methods_exist(test_case: unittest.TestCase,
                                 component: Any,
                                 expected_methods: List[str],
                                 component_name: str = "") -> None:
    """Assert that component has all expected methods.
    
    Args:
        test_case: Test case instance for assertions
        component: Component instance to check
        expected_methods: List of method names that should exist
        component_name: Optional component name for better error messages
    """
    name_prefix = f"{component_name} " if component_name else "Component "
    
    for method_name in expected_methods:
        test_case.assertTrue(hasattr(component, method_name),
                           f"{name_prefix}missing method: {method_name}")
        
        method = getattr(component, method_name)
        test_case.assertTrue(callable(method),
                           f"{name_prefix}{method_name} is not callable")


def assert_file_exists_and_readable(test_case: unittest.TestCase,
                                  file_path: str,
                                  should_contain: Optional[str] = None) -> None:
    """Assert that file exists and optionally contains specific content.
    
    Args:
        test_case: Test case instance for assertions
        file_path: Path to file that should exist
        should_contain: Optional text that file should contain
    """
    import os
    
    test_case.assertTrue(os.path.exists(file_path),
                        f"File should exist: {file_path}")
    
    test_case.assertTrue(os.path.isfile(file_path),
                        f"Path should be a file, not directory: {file_path}")
    
    # Check file is readable
    try:
        with open(file_path, 'r') as f:
            content = f.read()
    except Exception as e:
        test_case.fail(f"File should be readable: {file_path}, error: {e}")
    
    # Check content if specified
    if should_contain:
        test_case.assertIn(should_contain, content,
                          f"File {file_path} should contain '{should_contain}'")


def assert_mock_called_with_pattern(test_case: unittest.TestCase,
                                  mock_obj: Any,
                                  expected_patterns: List[Any],
                                  method_name: str = "call") -> None:
    """Assert that mock was called with arguments matching patterns.
    
    Args:
        test_case: Test case instance for assertions
        mock_obj: Mock object to check
        expected_patterns: List of expected argument patterns
        method_name: Name of method for error messages
    """
    test_case.assertTrue(mock_obj.called,
                        f"Mock {method_name} should have been called")
    
    # Check call count if specific patterns provided
    if expected_patterns:
        actual_calls = len(mock_obj.call_args_list)
        expected_calls = len(expected_patterns)
        
        test_case.assertEqual(actual_calls, expected_calls,
                            f"Mock {method_name} called {actual_calls} times, "
                            f"expected {expected_calls}")


def assert_result_has_expected_structure(test_case: unittest.TestCase,
                                       result: Any,
                                       expected_keys: List[str],
                                       result_name: str = "result") -> None:
    """Assert that result has expected dictionary structure.
    
    Args:
        test_case: Test case instance for assertions
        result: Result object/dict to validate
        expected_keys: Keys that should be present
        result_name: Name for better error messages
    """
    test_case.assertIsNotNone(result,
                             f"{result_name} should not be None")
    
    if expected_keys:
        # If expecting dict-like structure
        if hasattr(result, 'keys') or isinstance(result, dict):
            for key in expected_keys:
                test_case.assertIn(key, result,
                                 f"{result_name} missing key: {key}")
        else:
            # If expecting object with attributes
            for attr in expected_keys:
                test_case.assertTrue(hasattr(result, attr),
                                   f"{result_name} missing attribute: {attr}")


def assert_no_exceptions_during_execution(test_case: unittest.TestCase,
                                        func: callable,
                                        *args,
                                        operation_name: str = "operation",
                                        **kwargs) -> Any:
    """Assert that function executes without raising exceptions.
    
    Args:
        test_case: Test case instance for assertions  
        func: Function to execute
        *args: Arguments to pass to function
        operation_name: Name of operation for error messages
        **kwargs: Keyword arguments to pass to function
    
    Returns:
        Result of function execution
    """
    try:
        return func(*args, **kwargs)
    except Exception as e:
        test_case.fail(f"{operation_name} should not raise exception, "
                      f"but got {type(e).__name__}: {e}")