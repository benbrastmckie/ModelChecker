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

`aligned_table_width`/`force_lasso_roles` are a second, unrelated pair of helpers added for the
`-a` (`align_vertically`) width tests: deriving the expected aligned-table line width from
whatever role mix a draw (real or forced) returns, and forcing `BimodalStructure._lasso_roles`
to return an arbitrary mix so draw-independence can be demonstrated without waiting on a live
solve to land on an unlucky vocabulary. See each function's own docstring.
"""

from __future__ import annotations

from typing import Any, Dict, List

import pytest

from model_checker.models.constraints import ModelConstraints
from model_checker.syntactic import Syntax
from model_checker.theory_lib.bimodal.operators import bimodal_operators
from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics
from model_checker.theory_lib.bimodal.semantic.model import BimodalStructure, signed_time
from model_checker.theory_lib.bimodal.semantic.proposition import BimodalProposition

__all__ = ["_settings", "_build", "aligned_table_width", "force_lasso_roles"]


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


def aligned_table_width(structure: BimodalStructure, roles: Dict[int, str], output: Any) -> int:
    """The `-a` (`align_vertically`) history-table line width `_print_history_table` would
    render for `roles`, computed by mirroring its own width formula at
    `semantic/model.py:533-574` line for line (same `time_width`, `slot_width`, per-column
    `widths`, and `" | "` separators) rather than re-running the printer. `roles` is not
    required to come from `structure`'s own live draw -- pass a role mix returned by
    `force_lasso_roles` to compute the width a *different* draw would have produced for the
    same structure.

    Intended for an **equality** assertion against the actually-rendered header length, not
    `<=`: `widths[i]` already takes the max of the header cell and every rendered body cell
    in that column (exactly as the printer does), so a real printer-geometry regression
    changes this value too and the equality check catches it loudly instead of passing
    vacuously against a merely-looser bound.
    """
    lassos = structure.certificate.lassos
    positions = list(structure.semantics.witness_registry.target_window())
    main_index = structure.main_point.get("lasso")

    headers = [f"L{index} {roles[index]}" for index in range(len(lassos))]
    cells: List[List[str]] = []
    for t in positions:
        row = []
        for index, lasso in enumerate(lassos):
            text = structure._format_label(lasso.label(t), output)
            if index == main_index and t == structure.target_time:
                text = f"[{text}]"
            row.append(text)
        cells.append(row)
    widths = [
        max([len(headers[column])] + [len(row[column]) for row in cells])
        for column in range(len(lassos))
    ]
    time_width = max(len("t"), *(len(signed_time(t)) for t in positions))
    slot_width = max(len("slot"), *(len(structure._slot_name(t)) for t in positions))
    return 8 + time_width + slot_width + sum(widths) + 3 * (len(widths) - 1)


def force_lasso_roles(monkeypatch: pytest.MonkeyPatch, roles: Dict[int, str]) -> None:
    """Patch `BimodalStructure._lasso_roles` to always return `roles`, bypassing whatever
    role mix the live Z3 solve actually drew. The live draw cannot otherwise be steered:
    `pyproject.toml` pins `z3-solver>=4.8.0` with no upper bound, so pinning a
    `PYTHONHASHSEED` or a Z3 random seed would give no cross-version guarantee and would
    only prove that one particular draw happens to pass -- not that the assertion holds
    for every draw. This lets a test exercise any role mix (e.g. extra `reserved, unused`
    columns in place of `witness` ones) deterministically instead of waiting on an unlucky
    solve.
    """
    monkeypatch.setattr(BimodalStructure, "_lasso_roles", lambda self, output: dict(roles))
