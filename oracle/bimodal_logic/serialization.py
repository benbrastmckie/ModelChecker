"""bimodal_logic.serialization - Result serialization utilities.

This module provides utilities for serializing a found witness-family
certificate into structured formats suitable for the bimodal_harness response
protocol.

## Change of meaning

This module previously serialized the retired window-and-abundance encoding's
model shape: `world_histories` (`{world_id: {time: state}}`) and `task_relation`
triples extracted by brute-force enumeration over a bounded `(-M, M)` domain.
That model shape no longer exists (`BimodalStructure` has no `world_histories`,
`main_world`, or `task_rel` -- see `theory_lib/bimodal/semantic/model.py`'s own
module docstring). This rewrite serializes the certificate `BimodalStructure`
actually produces: a `WitnessFamily` of labelled lassos, already independently
re-checked by the theory's own S3 obligation before this module ever sees it.

Public API:
    extract_true_false_atoms(structure):
        Extract true/false atom name lists from the main lasso's label at the
        target time.
    serialize_countermodel(structure, formula_json, formula_folded, depth,
                           back, mid, fwd, semantics_version):
        Assemble the full countermodel result dict.
"""

from __future__ import annotations

from model_checker.theory_lib.bimodal.semantic.formula import Atom


##############################################################################
# Atom truth extraction
##############################################################################

def extract_true_false_atoms(structure) -> tuple[list, list]:
    """Extract true and false atoms at the certificate's target position.

    The atom vocabulary is every `Atom` in the search's own formula closure
    (`structure.semantics.witness_registry.closure`), not just the ones
    mentioned in the input formula -- matching the retired serializer's own
    convention of reporting every sentence letter the search knew about.
    "True" means the atom belongs to the main lasso's label at
    `structure.target_time`; every other closure atom is "false" (labels are
    total over the closure -- an atom's absence from a label just is its
    falsity there, `docs/ADEQUACY.md`'s atom-membership identity).

    Args:
        structure: A `BimodalStructure` instance with `certificate is not None`.

    Returns:
        Tuple[list, list]: (trueAtoms, falseAtoms), each a list of
        {"name": str} dicts.
    """
    true_atoms: list = []
    false_atoms: list = []

    certificate = structure.certificate
    if certificate is None or structure.target_time is None:
        return true_atoms, false_atoms

    closure_atoms = {
        f.base
        for f in structure.semantics.witness_registry.closure
        if isinstance(f, Atom) and f.fresh_index is None
    }
    label = certificate.main.label(structure.target_time)
    label_atom_names = {f.base for f in label if isinstance(f, Atom)}

    for name in sorted(closure_atoms):
        if name in label_atom_names:
            true_atoms.append({"name": name})
        else:
            false_atoms.append({"name": name})

    return true_atoms, false_atoms


##############################################################################
# Full countermodel serialization
##############################################################################

def serialize_countermodel(
    structure,
    formula_json: dict,
    formula_folded: dict,
    depth: int,
    back: int,
    mid: int,
    fwd: int,
    semantics_version: str,
) -> dict:
    """Assemble the full countermodel result dict from a found certificate.

    Args:
        structure: The `BimodalStructure` instance (`certificate is not None`,
            already independently re-checked by its own S3 hook).
        formula_json: The original input JSON formula dict.
        formula_folded: The fold_formula result for formula_json.
        depth: The temporal_depth of formula_json.
        back: The back segment length used for this search.
        mid: The mid segment length used for this search.
        fwd: The fwd segment length used for this search.
        semantics_version: The provider's semantics_version string.

    Returns:
        dict with all countermodel output fields. `certificate` carries the
        found `WitnessFamily` in the exact wire shape
        `WitnessFamily.to_json` produces -- the same shape BimodalLogic's own
        `lake exe check_certificate` accepts on stdin, so a caller wanting a
        second, independent (Lean-side) verification can pass this field
        straight through with no translation layer.
    """
    true_atoms, false_atoms = extract_true_false_atoms(structure)
    certificate = structure.certificate

    return {
        "temporal_depth": depth,
        "segment_lengths": {"back": back, "mid": mid, "fwd": fwd},
        "semantics_version": semantics_version,
        "formula_folded_json": formula_folded,
        "formula": formula_json,
        "trueAtoms": true_atoms,
        "falseAtoms": false_atoms,
        "certificate": certificate.to_json(
            premises=structure.semantics._premise_formulas,
            conclusions=structure.semantics._conclusion_formulas,
            target_time=structure.target_time,
        ),
        "lasso_count": len(certificate.lassos),
    }
