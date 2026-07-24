"""
Validation helper utilities for testing.

Provides utilities for validating component interfaces, checking test coverage,
and other validation operations.
"""

import inspect
from typing import Any, Dict, List, Optional, Set, Tuple, Type


def validate_component_interface(component: Any, 
                               expected_methods: List[str],
                               expected_attributes: Optional[List[str]] = None) -> Dict[str, bool]:
    """Validate that component has expected interface.
    
    Args:
        component: Component instance or class to validate
        expected_methods: List of method names that should exist
        expected_attributes: Optional list of attribute names that should exist
    
    Returns:
        Dictionary with validation results
    """
    results = {
        'has_all_methods': True,
        'has_all_attributes': True,
        'missing_methods': [],
        'missing_attributes': [],
        'extra_methods': [],
        'method_signatures': {}
    }
    
    # Check methods
    for method_name in expected_methods:
        if not hasattr(component, method_name):
            results['has_all_methods'] = False
            results['missing_methods'].append(method_name)
        else:
            method = getattr(component, method_name)
            if callable(method):
                try:
                    sig = inspect.signature(method)
                    results['method_signatures'][method_name] = str(sig)
                except (ValueError, TypeError):
                    results['method_signatures'][method_name] = 'signature_unavailable'
    
    # Check attributes
    if expected_attributes:
        for attr_name in expected_attributes:
            if not hasattr(component, attr_name):
                results['has_all_attributes'] = False
                results['missing_attributes'].append(attr_name)
    
    # Find extra public methods
    all_methods = [name for name in dir(component) 
                  if callable(getattr(component, name)) and not name.startswith('_')]
    results['extra_methods'] = [m for m in all_methods if m not in expected_methods]
    
    return results


def check_test_coverage(test_methods: List[str], 
                       component_methods: List[str]) -> Dict[str, Any]:
    """Check test coverage for component methods.
    
    Args:
        test_methods: List of test method names
        component_methods: List of component method names to check coverage for
    
    Returns:
        Dictionary with coverage analysis
    """
    coverage_data = {
        'total_methods': len(component_methods),
        'tested_methods': [],
        'untested_methods': [],
        'coverage_percentage': 0.0,
        'test_method_mapping': {}
    }
    
    # Find which component methods have tests
    for component_method in component_methods:
        has_test = False
        associated_tests = []
        
        for test_method in test_methods:
            # Check if test method name suggests it tests this component method
            if component_method.lower() in test_method.lower():
                has_test = True
                associated_tests.append(test_method)
        
        if has_test:
            coverage_data['tested_methods'].append(component_method)
            coverage_data['test_method_mapping'][component_method] = associated_tests
        else:
            coverage_data['untested_methods'].append(component_method)
    
    # Calculate coverage percentage
    if coverage_data['total_methods'] > 0:
        coverage_data['coverage_percentage'] = (
            len(coverage_data['tested_methods']) / coverage_data['total_methods'] * 100
        )
    
    return coverage_data


def validate_test_naming_convention(test_methods: List[str],
                                  expected_pattern: str = "test_") -> Dict[str, List[str]]:
    """Validate test method naming conventions.
    
    Args:
        test_methods: List of test method names
        expected_pattern: Expected naming pattern prefix
    
    Returns:
        Dictionary with validation results
    """
    results = {
        'valid_names': [],
        'invalid_names': [],
        'suggestions': {}
    }
    
    for method_name in test_methods:
        if method_name.startswith(expected_pattern):
            # Check for descriptive naming
            parts = method_name.replace(expected_pattern, '').split('_')
            if len(parts) >= 2:  # At least component_action
                results['valid_names'].append(method_name)
            else:
                results['invalid_names'].append(method_name)
                results['suggestions'][method_name] = (
                    f"Consider more descriptive name like: "
                    f"{expected_pattern}component_action_condition"
                )
        else:
            results['invalid_names'].append(method_name)
            results['suggestions'][method_name] = (
                f"Should start with '{expected_pattern}'"
            )
    
    return results


def analyze_test_class_organization(test_classes: List[Type]) -> Dict[str, Any]:
    """Analyze organization of test classes.
    
    Args:
        test_classes: List of test class types
    
    Returns:
        Dictionary with organization analysis
    """
    analysis = {
        'total_classes': len(test_classes),
        'methods_per_class': {},
        'class_patterns': {},
        'recommendations': []
    }
    
    for test_class in test_classes:
        class_name = test_class.__name__
        
        # Count test methods
        test_methods = [name for name in dir(test_class) 
                       if name.startswith('test_')]
        analysis['methods_per_class'][class_name] = len(test_methods)
        
        # Analyze naming patterns
        if 'Core' in class_name:
            analysis['class_patterns'][class_name] = 'core_functionality'
        elif 'Edge' in class_name or 'Boundary' in class_name:
            analysis['class_patterns'][class_name] = 'edge_cases'
        elif 'Error' in class_name or 'Exception' in class_name:
            analysis['class_patterns'][class_name] = 'error_handling'
        elif 'Integration' in class_name:
            analysis['class_patterns'][class_name] = 'integration'
        else:
            analysis['class_patterns'][class_name] = 'general'
    
    # Generate recommendations
    avg_methods = sum(analysis['methods_per_class'].values()) / len(test_classes)
    
    if avg_methods > 15:
        analysis['recommendations'].append(
            "Consider splitting large test classes (>15 methods) into smaller, "
            "more focused classes"
        )
    
    pattern_counts = {}
    for pattern in analysis['class_patterns'].values():
        pattern_counts[pattern] = pattern_counts.get(pattern, 0) + 1
    
    if pattern_counts.get('error_handling', 0) == 0:
        analysis['recommendations'].append(
            "Consider adding dedicated error handling test classes"
        )
    
    return analysis


def validate_mock_usage(test_file_content: str) -> Dict[str, Any]:
    """Analyze mock usage patterns in test file.
    
    Args:
        test_file_content: Content of test file to analyze
    
    Returns:
        Dictionary with mock usage analysis
    """
    import re
    
    analysis = {
        'total_mocks': 0,
        'patch_decorators': 0,
        'context_manager_patches': 0,
        'mock_objects': 0,
        'potential_issues': []
    }
    
    # Count patch decorators
    patch_decorators = re.findall(r'@patch\(', test_file_content)
    analysis['patch_decorators'] = len(patch_decorators)
    
    # Count context manager patches
    context_patches = re.findall(r'with patch\(', test_file_content)
    analysis['context_manager_patches'] = len(context_patches)
    
    # Count Mock() instances
    mock_instances = re.findall(r'Mock\(', test_file_content)
    analysis['mock_objects'] = len(mock_instances)
    
    analysis['total_mocks'] = (
        analysis['patch_decorators'] + 
        analysis['context_manager_patches'] + 
        analysis['mock_objects']
    )
    
    # Identify potential issues
    if analysis['total_mocks'] > 10:
        analysis['potential_issues'].append(
            f"High mock usage ({analysis['total_mocks']} mocks) - "
            "consider using real objects where possible"
        )
    
    # Check for complex mock chains
    complex_chains = re.findall(r'mock_\w+\.return_value\.\w+\.return_value', test_file_content)
    if complex_chains:
        analysis['potential_issues'].append(
            f"Found {len(complex_chains)} complex mock chains - "
            "consider simplifying mock structure"
        )
    
    return analysis