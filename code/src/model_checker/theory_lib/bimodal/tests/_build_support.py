"""Shared example-build helpers for the bimodal verification test harness.

Single home for the pipeline construction order (`Syntax -> ModelConstraints ->
BimodalStructure`) that duplicated helpers across the bimodal test tree previously restated
byte-for-byte (or under a locally different name). Matches `builder/example.py`'s `BuildExample`
construction order without needing its `BuildModule` scaffolding.

Sibling of `_pinned_eval.py` and `_lean_check.py`: a test-support module, not production
`theory_lib` code, named with a leading underscore per this tree's own convention.

`_settings`/`_build` are imported directly by every consolidated call site across both
`tests/integration/` and `tests/unit/` -- covering both the full pipeline (`_build`) and the
settings dict alone (`_settings`) where a module only needs the latter. One renamed call site
(`tests/integration/test_injection.py`, whose local `_build_solved` matched this module's `_build`
shape under a different name) imports the pair under their shared names, with its own call sites
renamed to match.

**Not every call site collapses to a bare import of this module.**
`tests/unit/test_structure.py` needs `'verify'` to default to `'off'` unless a test explicitly
overrides it -- its own tests are about extraction, re-checking, and print formatting, not about
which of item 1's three verification states renders, so they must not depend on whether a real
checker binary happens to be resolvable on the machine running them (see that module's own
`_build` wrapper for the reasoning). Every other call site has no such requirement and imports
`_settings`/`_build` (or `_settings` alone) directly.

`tests/unit/test_witness_constraints.py` defines its own unrelated `_build_selector_family` --
same naming prefix, no relationship to this module's pipeline, not a call site.
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
