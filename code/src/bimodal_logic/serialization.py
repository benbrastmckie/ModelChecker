"""bimodal_logic.serialization - Result serialization utilities.

This module provides utilities for serializing Z3 model results into
structured formats suitable for the bimodal_harness response protocol.

Public API:
    extract_true_false_atoms(z3_model, semantics, model_constraints, structure):
        Extract true/false atom dicts at the main evaluation point.
    extract_task_triples(z3_model, semantics, N, M):
        Extract all task_rel triples that hold in the model.
    serialize_world_histories(structure):
        Convert world_histories to serializable list of dicts.
    serialize_countermodel(z3_model, semantics, model_constraints, structure,
                           formula_json, formula_folded, depth, M, semantics_version):
        Assemble the full countermodel result dict.
"""

from __future__ import annotations

import z3 as _z3

from model_checker.solver import is_true


##############################################################################
# Atom truth extraction
##############################################################################

def extract_true_false_atoms(z3_model, semantics, model_constraints, structure):
    """Extract true and false atoms at the main evaluation point.

    Evaluates each sentence letter's truth_condition at the world state of
    the main world (world_id=0) at the main time.

    Args:
        z3_model: The satisfiable Z3 model from BimodalStructure.z3_model.
        semantics: The BimodalSemantics instance.
        model_constraints: The ModelConstraints instance (has .sentence_letters).
        structure: The BimodalStructure instance (has .z3_main_world_state).

    Returns:
        Tuple[list, list]: (trueAtoms, falseAtoms), each a list of
        {"name": str} dicts.
    """
    true_atoms = []
    false_atoms = []

    # Use the actual Z3 bitvec main world state for truth condition evaluation
    main_state = structure.z3_main_world_state
    if main_state is None:
        # No valid model state; return empty lists
        return true_atoms, false_atoms

    for sl in model_constraints.sentence_letters:
        try:
            tc = semantics.truth_condition(main_state, sl)
            val = z3_model.eval(tc)
            name = str(sl)
            if is_true(val):
                true_atoms.append({"name": name})
            else:
                false_atoms.append({"name": name})
        except Exception:
            # On error, skip this atom
            pass

    return true_atoms, false_atoms


##############################################################################
# Task relation triple extraction
##############################################################################

def extract_task_triples(z3_model, semantics, N, M):
    """Extract all task_rel triples that hold in the Z3 model.

    Iterates over all combinations of (source_state, duration, target_state)
    and collects those where task_rel evaluates to True.

    Time complexity: O(2^(2N) * (2M-1)) evaluations.

    Args:
        z3_model: The satisfiable Z3 model.
        semantics: The BimodalSemantics instance (has .task_rel function).
        N: Number of world state bits (world states range 0..2^N - 1).
        M: Time bound (durations range -(M-1)..(M-1)).

    Returns:
        list of {"source": int, "duration": int, "target": int} dicts.
    """
    task_triples = []
    num_states = 2 ** N

    for s in range(num_states):
        s_bv = _z3.BitVecVal(s, N)
        for d in range(-(M - 1), M):
            d_int = _z3.IntVal(d)
            for u in range(num_states):
                u_bv = _z3.BitVecVal(u, N)
                try:
                    val = z3_model.eval(semantics.task_rel(s_bv, d_int, u_bv))
                    if is_true(val):
                        task_triples.append({
                            "source": s,
                            "duration": d,
                            "target": u,
                        })
                except Exception:
                    # Skip unevaluatable triples
                    pass

    return task_triples


##############################################################################
# World history serialization
##############################################################################

def serialize_world_histories(structure):
    """Convert BimodalStructure world_histories to a serializable list of dicts.

    BimodalStructure.world_histories maps:
        world_id (int) -> {time (int) -> state_str (str)}

    where state_str is an alphabetic label like 'a', 'b', etc.

    Args:
        structure: The BimodalStructure instance.

    Returns:
        list of {"world_id": int, "times": {str: str}} dicts,
        one per world in the model, sorted by world_id.
    """
    result = []
    for world_id in sorted(structure.world_histories.keys()):
        time_map = structure.world_histories[world_id]
        # Convert time keys to strings for JSON serialization compatibility
        times_dict = {str(t): str(state) for t, state in sorted(time_map.items())}
        result.append({
            "world_id": world_id,
            "times": times_dict,
        })
    return result


##############################################################################
# Full countermodel serialization
##############################################################################

def serialize_countermodel(
    z3_model,
    semantics,
    model_constraints,
    structure,
    formula_json: dict,
    formula_folded: dict,
    depth: int,
    M: int,
    semantics_version: str,
) -> dict:
    """Assemble the full countermodel result dict.

    Combines SimpleCountermodel fields (trueAtoms, falseAtoms, world_histories,
    task_relation) with StructuredCountermodel fields (formula_folded_json,
    temporal_depth, boundary_safe, time_bound, semantics_version).

    Args:
        z3_model: The satisfiable Z3 model.
        semantics: The BimodalSemantics instance.
        model_constraints: The ModelConstraints instance.
        structure: The BimodalStructure instance.
        formula_json: The original input JSON formula dict.
        formula_folded: The fold_formula result for formula_json.
        depth: The temporal_depth of formula_json.
        M: The time_bound used for this solve.
        semantics_version: The provider's semantics_version string.

    Returns:
        dict with all countermodel output fields.
    """
    N = semantics.N

    true_atoms, false_atoms = extract_true_false_atoms(
        z3_model, semantics, model_constraints, structure
    )
    task_triples = extract_task_triples(z3_model, semantics, N, M)
    world_histories = serialize_world_histories(structure)

    # boundary_safe: True if M > depth + 1 (i.e., M >= depth + 2)
    boundary_safe = M > depth + 1

    return {
        # StructuredCountermodel fields
        "temporal_depth": depth,
        "boundary_safe": boundary_safe,
        "time_bound": M,
        "semantics_version": semantics_version,
        "formula_folded_json": formula_folded,
        # SimpleCountermodel fields
        "formula": formula_json,
        "trueAtoms": true_atoms,
        "falseAtoms": false_atoms,
        "world_histories": world_histories,
        "task_relation": task_triples,
        # Evaluation point metadata
        "evaluation_world": structure.main_world,
        "evaluation_time": structure.main_time,
        "world_count": len(structure.world_histories),
    }
