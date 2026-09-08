"""Shared helpers for the counterfactual subtheory's verifier-clause tests.

The tests in this directory need a *solved* model whose sentence objects carry
propositions, so that an operator's Z3-side clause (``extended_verify``) and its
Python-side clause (``find_verifiers_and_falsifiers``) can be evaluated against
each other on identical data. ``run_test`` in ``model_checker.utils.testing``
only returns a boolean, so this module repeats its pipeline and hands back the
pieces.
"""

from typing import Any, Dict, List, Optional, Sequence, Tuple

from model_checker import ModelConstraints, Syntax
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.theory_lib.logos.semantic import (
    LogosModelStructure,
    LogosProposition,
    LogosSemantics,
)

DEFAULT_SUBTHEORIES = ['extensional', 'modal', 'counterfactual']


def base_settings(N: int = 3, expectation: Optional[bool] = True, **overrides: Any) -> Dict[str, Any]:
    """Settings matching the counterfactual examples' shape at a chosen ``N``."""
    settings = {
        'N': N,
        'contingent': True,
        'non_null': True,
        'non_empty': True,
        'disjoint': False,
        'max_time': 10,
        'iterate': 1,
        'expectation': expectation,
        'solver': 'z3',
    }
    settings.update(overrides)
    return settings


def load_registry(subtheories: Sequence[str] = DEFAULT_SUBTHEORIES) -> LogosOperatorRegistry:
    """A fresh registry with the named subtheories loaded."""
    registry = LogosOperatorRegistry()
    registry.load_subtheories(list(subtheories))
    return registry


def solve(
    premises: List[str],
    conclusions: List[str],
    settings: Dict[str, Any],
    subtheories: Sequence[str] = DEFAULT_SUBTHEORIES,
) -> Tuple[Syntax, LogosSemantics, LogosModelStructure]:
    """Build and solve one example, interpreting every sentence on success.

    Returns the syntax (whose ``premises``/``conclusions`` carry propositions
    when a model was found), the semantics instance, and the model structure.
    ``model_structure.z3_model`` is ``None`` when no model exists.
    """
    registry = load_registry(subtheories)
    syntax = Syntax(premises, conclusions, registry.get_operators())
    semantics = LogosSemantics(settings)
    constraints = ModelConstraints(settings, syntax, semantics, LogosProposition)
    structure = LogosModelStructure(constraints, settings)
    if structure.z3_model is not None:
        structure.interpret(syntax.premises)
        structure.interpret(syntax.conclusions)
    return syntax, semantics, structure


def outcome(
    premises: List[str],
    conclusions: List[str],
    settings: Dict[str, Any],
    subtheories: Sequence[str] = DEFAULT_SUBTHEORIES,
) -> str:
    """Classify one example as ``countermodel``, ``valid`` or ``timeout``.

    ``valid`` means the solver proved no countermodel exists within the
    budget; ``timeout`` means the solve hit ``max_time`` without a verdict.
    """
    _, _, structure = solve(premises, conclusions, settings, subtheories)
    if structure.z3_model is not None:
        return 'countermodel'
    runtime = getattr(structure, 'z3_model_runtime', None)
    if getattr(structure, 'timeout', False) or (
        runtime is not None and runtime >= settings['max_time']
    ):
        return 'timeout'
    return 'valid'


def find_sentence(syntax: Syntax, name: str):
    """Return the parsed sentence object whose infix name is ``name``."""
    return syntax.all_sentences[name]


def state_int(state: Any) -> int:
    """Concrete integer of a Z3 bit-vector value."""
    return int(state.as_long())
