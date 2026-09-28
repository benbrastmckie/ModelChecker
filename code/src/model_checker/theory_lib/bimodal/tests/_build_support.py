"""Shared example-build helpers for the bimodal verification test harness.

Single home for the pipeline construction order (`Syntax -> ModelConstraints ->
BimodalStructure`) that four modules previously restated byte-for-byte:
`tests/integration/test_certificate_a2_triangle.py`,
`tests/integration/test_search_period_coverage.py`, `tests/unit/test_structure.py`, and
`tests/unit/test_pinned_eval.py`. Matches `builder/example.py`'s `BuildExample` construction
order without needing its `BuildModule` scaffolding.

Sibling of `_pinned_eval.py` and `_lean_check.py`: a test-support module, not production
`theory_lib` code, named with a leading underscore per this tree's own convention.

**Not every former call site collapses to a bare import of this module.**
`tests/unit/test_structure.py` needs `'verify'` to default to `'off'` unless a test explicitly
overrides it -- its own tests are about extraction, re-checking, and print formatting, not about
which of item 1's three verification states renders, so they must not depend on whether a real
checker binary happens to be resolvable on the machine running them (see that module's own
`_build` wrapper for the reasoning, carried over unedited from before this consolidation). The
other three call sites have no such requirement and import `_settings`/`_build` directly.
"""

from __future__ import annotations

from typing import Any, Dict, List

from model_checker.models.constraints import ModelConstraints
from model_checker.syntactic import Syntax
from model_checker.theory_lib.bimodal.operators import bimodal_operators
from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics
from model_checker.theory_lib.bimodal.semantic.model import BimodalStructure
from model_checker.theory_lib.bimodal.semantic.proposition import BimodalProposition

__all__ = ["_settings", "_build"]


def _settings(**overrides: Any) -> Dict[str, Any]:
    settings = dict(BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS)
    settings.update(overrides)
    return settings


def _build(premises: List[str], conclusions: List[str], **setting_overrides: Any) -> BimodalStructure:
    """Build one example through the real `Syntax -> ModelConstraints -> BimodalStructure`
    pipeline -- the same construction order `builder/example.py`'s `BuildExample` drives,
    without needing its `BuildModule` scaffolding."""
    settings = _settings(**setting_overrides)
    syntax = Syntax(premises, conclusions, bimodal_operators)
    model_constraints = ModelConstraints(
        settings, syntax, BimodalSemantics(settings), BimodalProposition
    )
    return BimodalStructure(model_constraints, settings)
