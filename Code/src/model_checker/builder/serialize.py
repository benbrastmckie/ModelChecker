"""
Serialization utilities for multiprocessing in maximize mode.

This module provides functions to serialize and deserialize semantic theories
for use with ProcessPoolExecutor, avoiding pickle errors with complex objects.
"""

import importlib
from typing import Dict, Any, Union, Type
from model_checker.syntactic import OperatorCollection


def serialize_operators(operators: Union[OperatorCollection, dict]) -> Dict[str, Dict[str, str]]:
    """
    Serialize an OperatorCollection or dict of operators to a picklable format.
    
    Args:
        operators: Either an OperatorCollection instance or a dict of operators
        
    Returns:
        Dictionary mapping operator names to their class info:
        {
            "\\boxright": {
                "class_name": "BoxRightOperator",
                "module_name": "model_checker.theory_lib.imposition.operators"
            },
            ...
        }
    """
    serialized = {}
    
    if isinstance(operators, OperatorCollection):
        operator_dict = operators.operator_dictionary
    else:
        operator_dict = operators
    
    for op_name, op_class in operator_dict.items():
        serialized[op_name] = {
            "class_name": op_class.__name__,
            "module_name": op_class.__module__
        }
    
    return serialized


def deserialize_operators(operator_data: Dict[str, Dict[str, str]]) -> OperatorCollection:
    """
    Reconstruct an OperatorCollection from serialized data.
    
    Args:
        operator_data: Serialized operator information
        
    Returns:
        OperatorCollection instance with all operators restored
    """
    # Import here to avoid circular imports
    from model_checker.syntactic import OperatorCollection
    
    collection = OperatorCollection()
    
    for op_name, class_info in operator_data.items():
        module = importlib.import_module(class_info["module_name"])
        op_class = getattr(module, class_info["class_name"])
        collection.add_operator(op_class)
    
    return collection


def serialize_semantic_theory(theory_name: str, semantic_theory: Dict[str, Any]) -> Dict[str, Any]:
    """
    Serialize a semantic theory dictionary to a picklable format.
    
    Args:
        theory_name: Name of the theory (e.g., "Fine", "Brast-McKie")
        semantic_theory: Dictionary containing semantics, operators, etc.
        
    Returns:
        Serialized theory configuration with only picklable data
    """
    return {
        "theory_name": theory_name,
        "semantics": {
            "class_name": semantic_theory["semantics"].__name__,
            "module_name": semantic_theory["semantics"].__module__
        },
        "proposition": {
            "class_name": semantic_theory["proposition"].__name__,
            "module_name": semantic_theory["proposition"].__module__
        },
        "model": {
            "class_name": semantic_theory["model"].__name__,
            "module_name": semantic_theory["model"].__module__
        },
        "operators": serialize_operators(semantic_theory["operators"]),
        "dictionary": semantic_theory.get("dictionary", {})  # Already serializable
    }


def deserialize_semantic_theory(theory_config: Dict[str, Any]) -> Dict[str, Any]:
    """
    Reconstruct a semantic theory from serialized configuration.
    
    Args:
        theory_config: Serialized theory configuration
        
    Returns:
        Semantic theory dictionary with all classes restored
    """
    # Helper function to load a class from module and class name
    def load_class(class_info: Dict[str, str]) -> Type:
        module = importlib.import_module(class_info["module_name"])
        return getattr(module, class_info["class_name"])
    
    return {
        "semantics": load_class(theory_config["semantics"]),
        "proposition": load_class(theory_config["proposition"]),
        "model": load_class(theory_config["model"]),
        "operators": deserialize_operators(theory_config["operators"]),
        "dictionary": theory_config["dictionary"]
    }


def import_class(module_name: str, class_name: str) -> Type:
    """
    Import a class from a module by name.
    
    Args:
        module_name: Fully qualified module name
        class_name: Name of the class to import
        
    Returns:
        The imported class
        
    Raises:
        ImportError: If module cannot be imported
        AttributeError: If class doesn't exist in module
    """
    try:
        module = importlib.import_module(module_name)
        return getattr(module, class_name)
    except ImportError as e:
        raise ImportError(f"Cannot import module '{module_name}': {e}")
    except AttributeError as e:
        raise AttributeError(f"Class '{class_name}' not found in module '{module_name}': {e}")


def safe_import_module(module_name: str):
    """
    Safely import a module with helpful error messages.
    
    Args:
        module_name: Fully qualified module name
        
    Returns:
        The imported module
        
    Raises:
        ImportError: With helpful context if import fails
    """
    try:
        return importlib.import_module(module_name)
    except ImportError as e:
        # Check if it's a theory module
        if "theory_lib" in module_name:
            theory_name = module_name.split(".")[-2]
            raise ImportError(
                f"Cannot import theory module '{theory_name}'. "
                f"Make sure the theory is properly installed. "
                f"Original error: {e}"
            )
        raise