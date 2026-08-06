"""Collapse census: a construction-time structural probe for the Z3
constant-interning aliasing defect in bimodal temporal/modal operators.

For every formula produced by
`oracle.bimodal_logic.tests.test_cross_oracle_differential._enumerate_primitive_formulas`
at a given max complexity, this script builds the exact conclusion constraint
`find_countermodel()` would ask Z3 to satisfy (`conclusion_constraints[0]` of a
`ModelConstraints` instance, mirroring `Z3OracleProvider.find_countermodel`'s
own pipeline up to but not including `BimodalStructure` construction, which is
where solving would begin), applies `z3.simplify()`, and records whether the
result is a Z3 Boolean literal.

This performs ZERO solves -- it is a pure term-construction and simplification
probe, so it runs in seconds regardless of enumeration size. It is the
mechanism-level demonstration that a fixed-name bound variable in a quantified
temporal/modal operator produces a self-referential comparison that Z3's own
term simplifier folds to a constant before any quantifier closes -- the
soundness failure mode this task fixes: a conclusion constraint that is a
Boolean literal is unfalsifiable by encoding, so `find_countermodel` can never
return a countermodel for it, and the oracle would report validity it never
established.

Usage:
    PYTHONPATH=code/src:oracle python3 collapse_census.py <max_complexity> <out.json>

Output schema (JSON array of objects), one entry per enumerated formula:
    {
        "index": int,              # 0-based index into the enumeration
        "formula_json": dict,      # the primitive-tag formula JSON
        "folded": bool,            # True iff z3.simplify(...) is a Bool literal
        "folded_value": bool | null,
        "contains_bot": bool,      # True iff the formula tree contains a "bot" node
    }
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

# Make both the oracle package and the model_checker src tree importable
# regardless of CWD.
_THIS_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _THIS_DIR.parents[2]
_ORACLE_DIR = _REPO_ROOT / "oracle"
_SRC_DIR = _REPO_ROOT / "code" / "src"
for _p in (_ORACLE_DIR, _SRC_DIR):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

import z3  # noqa: E402

from model_checker.utils.context import isolated_z3_context  # noqa: E402
from model_checker import ModelConstraints, Syntax  # noqa: E402
from model_checker.theory_lib.bimodal import (  # noqa: E402
    BimodalSemantics,
    BimodalProposition,
    bimodal_operators,
)

from bimodal_logic.translation import (  # noqa: E402
    json_to_prefix,
    temporal_depth,
    prefix_to_infix,
)

# Reuse the exact enumerator the gating/exhaustive suite uses, rather than
# reinventing formula generation.
from bimodal_logic.tests.test_cross_oracle_differential import (  # noqa: E402
    _enumerate_primitive_formulas,
)


def _contains_bot(formula_json: dict) -> bool:
    """Recursively check whether a formula JSON tree contains a "bot" node."""
    tag = formula_json.get("tag")
    if tag == "bot":
        return True
    if tag in ("atom", "top"):
        return False
    if "arg" in formula_json:
        return _contains_bot(formula_json["arg"])
    if "child" in formula_json:
        return _contains_bot(formula_json["child"])
    if "left" in formula_json and "right" in formula_json:
        return _contains_bot(formula_json["left"]) or _contains_bot(formula_json["right"])
    if "event" in formula_json and "guard" in formula_json:
        return _contains_bot(formula_json["event"]) or _contains_bot(formula_json["guard"])
    raise ValueError(f"_contains_bot: unrecognized formula shape: {formula_json!r}")


def build_conclusion_constraint(formula_json: dict):
    """Build the exact conclusion_constraints[0] find_countermodel() would use.

    Mirrors Z3OracleProvider.find_countermodel()'s pipeline up to (but not
    including) BimodalStructure construction -- i.e., no solving happens here.
    """
    depth = temporal_depth(formula_json)
    M = max(depth + 2, 3)

    prefix = json_to_prefix(formula_json)
    infix = prefix_to_infix(prefix)

    settings = {
        "N": 2,
        "M": M,
        "temporal_depth": depth,
        "contingent": False,
        "disjoint": False,
        "max_time": 1.0,  # irrelevant -- no solve is performed
        "expectation": True,
        "solver": "z3",
    }

    with isolated_z3_context():
        semantics = BimodalSemantics(settings)
        syntax = Syntax([], [infix], bimodal_operators)
        model_constraints = ModelConstraints(
            settings, syntax, semantics, BimodalProposition
        )
        conclusion = model_constraints.conclusion_constraints[0]
        simplified = z3.simplify(conclusion)
        return simplified


def run_census(max_complexity: int, atoms: list[str]) -> list[dict]:
    formulas = _enumerate_primitive_formulas(max_complexity, atoms)
    entries = []
    for index, formula_json in enumerate(formulas):
        simplified = build_conclusion_constraint(formula_json)
        is_bool_literal = z3.is_true(simplified) or z3.is_false(simplified)
        folded_value = None
        if z3.is_true(simplified):
            folded_value = True
        elif z3.is_false(simplified):
            folded_value = False
        entries.append(
            {
                "index": index,
                "formula_json": formula_json,
                "folded": bool(is_bool_literal),
                "folded_value": folded_value,
                "contains_bot": _contains_bot(formula_json),
            }
        )
    return entries


def main() -> None:
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <max_complexity> <out.json>", file=sys.stderr)
        sys.exit(2)
    max_complexity = int(sys.argv[1])
    out_path = Path(sys.argv[2])
    entries = run_census(max_complexity, ["p"])
    out_path.write_text(json.dumps(entries, indent=2) + "\n", encoding="utf-8")

    total = len(entries)
    folded = [e for e in entries if e["folded"]]
    folded_true = [e for e in folded if e["folded_value"] is True]
    folded_false = [e for e in folded if e["folded_value"] is False]
    non_bot_survivors = [e for e in folded if not e["contains_bot"]]

    print(f"total_formulas: {total}")
    print(f"folded: {len(folded)} (true={len(folded_true)}, false={len(folded_false)})")
    print(f"non-bot folded survivors: {len(non_bot_survivors)}")
    for e in non_bot_survivors:
        print(f"  index={e['index']} folded_value={e['folded_value']} formula={e['formula_json']}")


if __name__ == "__main__":
    main()
