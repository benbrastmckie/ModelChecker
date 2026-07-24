"""
API utility functions for accessing theories and examples.

This module provides functions for retrieving theories and examples from an
already-supplied mapping. It is deliberately theory-*unaware*: it never imports
`theory_lib` (core must not -- see `docs/THEORY_ARCHITECTURE.md`'s Layering section).
The theory-aware entry point that auto-loads a theory's `semantic_theories` mapping by
name lives in the upper-layer `model_checker/api.py`, which delegates the actual lookup
to `get_theory()` below once it has a mapping in hand.
"""

from typing import List, Dict, Any, Union


def get_example(name: str, example_range: Dict[str, List[Any]]) -> List[Any]:
    """Get a specific example by name from the provided example range.

    Args:
        name (str): Name of the example to retrieve
        example_range (dict): Dictionary containing the examples

    Returns:
        list: [premises, conclusions, settings]

    Raises:
        KeyError: If the example name is not found
    """
    if name not in example_range:
        raise KeyError(f"Example {name} not found. Available examples: {list(example_range.keys())}")
    return example_range[name]


def get_theory(name: str, semantic_theories: Dict[str, Any]) -> Dict[str, Any]:
    """Get a specific semantic theory by name from an already-supplied mapping.

    Pure lookup: `semantic_theories` must already be loaded by the caller (e.g. via
    `model_checker.api.get_theory()`, which auto-loads it from `theory_lib` and then
    delegates here). This function itself never reaches into `theory_lib`.

    Args:
        name (str): Name of the theory to retrieve (e.g., 'default', 'exclusion')
        semantic_theories (dict): Dictionary containing semantic theories.

    Returns:
        dict: Dictionary containing semantics, proposition, model, and operators

    Raises:
        KeyError: If the specific theory is not found in the semantic_theories
    """
    # For theories with only one variant, return that variant regardless of name
    if len(semantic_theories) == 1:
        return list(semantic_theories.values())[0]

    # Standard case - look up the theory by name
    if name not in semantic_theories:
        raise KeyError(f"Theory '{name}' not found. Available theories: {list(semantic_theories.keys())}")

    return semantic_theories[name]