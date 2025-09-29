"""
Utility functions for imposition theory semantics.

This module contains helper functions and utilities used by the imposition theory
semantic classes.
"""

from typing import Any, List, Dict, Optional, Set
import z3


def safe_bitvec_as_long(bitvec: z3.BitVecRef) -> int:
    """Safely convert a Z3 bitvector to a Python integer.

    Args:
        bitvec: The Z3 bitvector to convert

    Returns:
        Integer representation of the bitvector
    """
    if isinstance(bitvec, int):
        return bitvec
    return bitvec.as_long()


def format_imposition_relation(state: z3.BitVecRef, world: z3.BitVecRef, outcome: z3.BitVecRef) -> str:
    """Format an imposition relation triple as a string.

    Args:
        state: The state being imposed
        world: The world being imposed on
        outcome: The outcome world

    Returns:
        Formatted string representation
    """
    state_val = safe_bitvec_as_long(state)
    world_val = safe_bitvec_as_long(world)
    outcome_val = safe_bitvec_as_long(outcome)
    return f"s{state_val} ->_{world_val} s{outcome_val}"


def group_impositions_by_world(imposition_relations: List[tuple]) -> Dict[z3.BitVecRef, List[tuple]]:
    """Group imposition relations by the world being imposed on.

    Args:
        imposition_relations: List of (state, world, outcome) tuples

    Returns:
        Dictionary mapping worlds to lists of (state, outcome) pairs
    """
    grouped = {}
    for state, world, outcome in imposition_relations:
        if world not in grouped:
            grouped[world] = []
        grouped[world].append((state, outcome))
    return grouped


def extract_unique_states(imposition_relations: List[tuple]) -> Set[z3.BitVecRef]:
    """Extract all unique states from imposition relations.

    Args:
        imposition_relations: List of (state, world, outcome) tuples

    Returns:
        Set of all unique states involved in the relations
    """
    states = set()
    for state, world, outcome in imposition_relations:
        states.add(state)
        states.add(world)
        states.add(outcome)
    return states


def validate_imposition_triple(state: z3.BitVecRef, world: z3.BitVecRef, outcome: z3.BitVecRef) -> bool:
    """Validate that an imposition triple has valid Z3 bitvector components.

    Args:
        state: The state being imposed
        world: The world being imposed on
        outcome: The outcome world

    Returns:
        True if all components are valid Z3 bitvectors
    """
    try:
        # Check that all components are bitvectors or integers
        for component in [state, world, outcome]:
            if not (isinstance(component, (int, z3.BitVecRef)) or z3.is_bv(component)):
                return False
        return True
    except:
        return False


def sort_imposition_relations(relations: List[tuple]) -> List[tuple]:
    """Sort imposition relations by state, world, then outcome values.

    Args:
        relations: List of (state, world, outcome) tuples

    Returns:
        Sorted list of relations
    """
    def sort_key(relation):
        state, world, outcome = relation
        return (
            safe_bitvec_as_long(state),
            safe_bitvec_as_long(world),
            safe_bitvec_as_long(outcome)
        )

    return sorted(relations, key=sort_key)


def filter_valid_impositions(relations: List[tuple]) -> List[tuple]:
    """Filter out invalid imposition relations.

    Args:
        relations: List of (state, world, outcome) tuples

    Returns:
        List containing only valid imposition relations
    """
    return [
        (state, world, outcome)
        for state, world, outcome in relations
        if validate_imposition_triple(state, world, outcome)
    ]