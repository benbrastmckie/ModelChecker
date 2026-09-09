"""Example collections that discriminate between the candidate verifier clauses.

The 37 examples in ``examples.py`` cannot separate any candidate: no premise
or conclusion places a counterfactual in a verifier-consuming position, and
the shared truth clause decides everything else.  The collections here put a
counterfactual ``X := A \\boxrightK B`` in *antecedent* position (nested
schemata), compare two counterfactuals with the constitutive identity
``\\equiv`` (hyperintensionality), and re-run the 37 examples under each
candidate (regression).

Run directly for the dual-methodology check (``./dev_cli.py <this file>``);
``example_range`` selects a curated subset.  ``tests/test_candidate_logic.py``
asserts the outcome of every nested schema against the oracle profile pinned
in ``tests/test_candidate_logic_oracle.py``.
"""

import os
import subprocess
import sys
from typing import Any, Dict, List, Tuple

from ...operators import LogosOperatorRegistry
from ...semantic import LogosSemantics, LogosProposition, LogosModelStructure
from .candidates import CANDIDATE_OPERATORS, substitute_candidate

CANDIDATE_KEYS: Tuple[str, ...] = tuple(CANDIDATE_OPERATORS)

#: Nested-antecedent schemata, with ``X := A \\boxrightK B``.
SCHEMATA: Tuple[str, ...] = (
    "identity",        # ⊢ X □→ X
    "modus_ponens",    # X, X □→ C ⊢ C
    "strengthening",   # X □→ C ⊢ (X ∧ D) □→ C
    "strict_to_cf",    # □(X → C) ⊢ X □→ C
    "cf_to_strict",    # X □→ C ⊢ □(X → C)
    "might_identity",  # ⊢ (A ◇→ B) □→ (A ◇→ B)
)

#: Oracle-pinned profile (``tests/test_candidate_logic_oracle.py``):
#: ``theorem`` = no countermodel, ``countermodel`` = a countermodel exists.
ORACLE_PROFILE: Dict[str, Dict[str, str]] = {
    "I": {
        "identity": "countermodel", "modus_ponens": "theorem", "strengthening": "countermodel",
        "strict_to_cf": "countermodel", "cf_to_strict": "theorem", "might_identity": "countermodel",
    },
    "ILC": {schema: "theorem" for schema in SCHEMATA},
    "W": {schema: "theorem" for schema in SCHEMATA},
    "L": {schema: "theorem" for schema in SCHEMATA},
    "ILMC": {
        "identity": "theorem", "modus_ponens": "theorem", "strengthening": "countermodel",
        "strict_to_cf": "theorem", "cf_to_strict": "countermodel", "might_identity": "theorem",
    },
    "MC": {
        "identity": "theorem", "modus_ponens": "theorem", "strengthening": "countermodel",
        "strict_to_cf": "theorem", "cf_to_strict": "countermodel", "might_identity": "theorem",
    },
}

NESTED_SUBTHEORIES: List[str] = ['extensional', 'modal', 'counterfactual']
CONSTITUTIVE_SUBTHEORIES: List[str] = ['extensional', 'modal', 'constitutive', 'counterfactual']


def example_settings(N: int, expectation: bool, max_time: int = 10) -> Dict[str, Any]:
    """Settings in the shape of the counterfactual examples."""
    return {
        'N': N,
        'contingent': True,
        'non_null': True,
        'non_empty': True,
        'disjoint': False,
        'max_time': max_time,
        'iterate': 1,
        'expectation': expectation,
        'solver': 'z3',
    }


def nested_schema(key: str, schema: str) -> Tuple[List[str], List[str]]:
    """Premises and conclusions of one nested-antecedent schema under candidate ``key``."""
    box, might = f"\\boxright{key}", f"\\diamondright{key}"
    x = f"(A {box} B)"
    x_might = f"(A {might} B)"
    if schema == "identity":
        return [], [f"({x} {box} {x})"]
    if schema == "modus_ponens":
        return [x, f"({x} {box} C)"], ["C"]
    if schema == "strengthening":
        return [f"({x} {box} C)"], [f"(({x} \\wedge D) {box} C)"]
    if schema == "strict_to_cf":
        return [f"\\Box ({x} \\rightarrow C)"], [f"({x} {box} C)"]
    if schema == "cf_to_strict":
        return [f"({x} {box} C)"], [f"\\Box ({x} \\rightarrow C)"]
    if schema == "might_identity":
        return [], [f"({x_might} {box} {x_might})"]
    raise ValueError(f"unknown schema {schema!r}")


def nested_examples(key: str, N: int = 3, max_time: int = 10) -> Dict[str, List[Any]]:
    """The six nested schemata for candidate ``key``; ``expectation`` follows the oracle profile."""
    examples: Dict[str, List[Any]] = {}
    for schema in SCHEMATA:
        premises, conclusions = nested_schema(key, schema)
        expectation = ORACLE_PROFILE[key][schema] == "countermodel"
        examples[f"{key}_{schema.upper()}"] = [premises, conclusions, example_settings(N, expectation, max_time)]
    return examples


def constitutive_example(key: str, N: int = 3, max_time: int = 10, expectation: bool = True) -> List[Any]:
    """Necessary equivalence of two counterfactuals against their constitutive identity.

    Premise ``\\Box ((A K B) \\leftrightarrow (C K D))``, conclusion
    ``((A K B) \\equiv (C K D))``: a countermodel is a model in which two
    counterfactuals share a truth-set yet express distinct propositions
    under the candidate's verifier clause.  Requires the constitutive
    subtheory.
    """
    box = f"\\boxright{key}"
    x, y = f"(A {box} B)", f"(C {box} D)"
    return [[f"\\Box ({x} \\leftrightarrow {y})"], [f"({x} \\equiv {y})"], example_settings(N, expectation, max_time)]


def constitutive_examples(key: str, Ns: Tuple[int, ...] = (3, 4), max_time: int = 10) -> Dict[str, List[Any]]:
    return {f"{key}_CONSTITUTIVE_N{N}": constitutive_example(key, N, max_time) for N in Ns}


def regression_examples(key: str) -> Dict[str, List[Any]]:
    """The 37 baseline examples with ``\\boxright``/``\\diamondright`` rewritten to candidate ``key``."""
    # Imported here: examples.py imports this module for its candidate collection.
    from .examples import unit_tests as baseline_unit_tests

    examples: Dict[str, List[Any]] = {}
    for name, (premises, conclusions, settings) in baseline_unit_tests.items():
        examples[f"{key}_{name}"] = [
            [substitute_candidate(p, key) for p in premises],
            [substitute_candidate(c, key) for c in conclusions],
            dict(settings),
        ]
    return examples


# ---------------------------------------------------------------------------
# Curated collection for direct runs
# ---------------------------------------------------------------------------

def _curated() -> Dict[str, List[Any]]:
    ilmc = nested_examples("ILMC")
    ilc = nested_examples("ILC")
    return {
        "ILMC_IDENTITY": ilmc["ILMC_IDENTITY"],
        "ILMC_MODUS_PONENS": ilmc["ILMC_MODUS_PONENS"],
        "ILMC_STRENGTHENING": ilmc["ILMC_STRENGTHENING"],
        "ILMC_CF_TO_STRICT": ilmc["ILMC_CF_TO_STRICT"],
        "ILC_CF_TO_STRICT": ilc["ILC_CF_TO_STRICT"],
        "ILMC_CONSTITUTIVE_N3": constitutive_example("ILMC", 3),
    }


#: Curated subset: the primary candidate's nested profile, the control's
#: strict collapse, and the constitutive comparison for the primary candidate.
counterfactual_candidate_examples: Dict[str, List[Any]] = _curated()

general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

candidate_registry = LogosOperatorRegistry()
candidate_registry.load_subtheories(CONSTITUTIVE_SUBTHEORIES)

candidate_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": candidate_registry.get_operators(),
}

semantic_theories = {
    "Brast-McKie": candidate_theory,
}

example_range = dict(counterfactual_candidate_examples)


if __name__ == '__main__':
    file_name = os.path.basename(__file__)
    parent_parent_dir = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_parent_dir)
