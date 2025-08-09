"""
Formatting utility functions for the model checker.

This module provides functions for pretty printing sets and generating
standard error messages.
"""

import string


def pretty_set_print(set_with_strings):
    """Pretty print a set containing strings.
    
    Args:
        set_with_strings: A set or frozenset containing string elements
        
    Returns:
        A formatted string representation of the set with elements joined by commas
        
    Example:
        >>> pretty_set_print({'a', 'b', 'c'})
        '{a, b, c}'
        >>> pretty_set_print(set())
        '{}'
    """
    if not set_with_strings:
        return "{}"
    
    # Convert to sorted list for consistent output
    elements = sorted(str(elem) for elem in set_with_strings)
    return "{" + ", ".join(elements) + "}"


def not_implemented_string(cl_name):
    """Return a message for NotImplemented Errors on Operator and Proposition classes.
    
    The error is raised when a user creates an Operator object or a Proposition object,
    and directs them to implement a subclass and create instances of the subclass.
    
    Args:
        cl_name: The name of the class that should not be instantiated directly
        
    Returns:
        An appropriate error message string
    """
    if cl_name == "PropositionDefaults":
        return (f"User should implement subclass(es) of {cl_name} for propositions. The "
                f"ModelChecker assumes the user will create proposition classes for each letter "
                f"in a model.")
    elif cl_name == "OperatorDefaults":
        return (f"User should implement subclass(es) of {cl_name} for operators. The "
                f"ModelChecker assumes the user will create operator classes for each operator "
                f"in the logical language.")
    else:
        return (f"Cannot instantiate {cl_name} directly. Please implement and use a "
                f"subclass instead.")


def flatten(structured_list):
    """Recursively flatten a nested list structure.
    
    Args:
        structured_list: A potentially nested list structure
        
    Returns:
        A flat list containing all non-list elements from the input
        
    Example:
        >>> flatten([1, [2, 3], [4, [5, 6]]])
        [1, 2, 3, 4, 5, 6]
        >>> flatten(['a', ['b', ['c', 'd']], 'e'])
        ['a', 'b', 'c', 'd', 'e']
    """
    result = []
    for item in structured_list:
        if isinstance(item, list):
            result.extend(flatten(item))
        else:
            result.append(item)
    return result