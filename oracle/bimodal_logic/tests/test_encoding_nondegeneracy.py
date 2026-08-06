"""Permanent structural regression guard against Z3 constant-interning aliasing.

Why this is a soundness test, not a style test
================================================

`z3.Int('fixed_name')` interns by `(name, sort)`: every call with the same name
returns the *literal same* Z3 term. A quantified temporal/modal operator that
declares its "fresh" bound variable with a fixed string name is therefore
aliasing-unsafe whenever its own recursion passes that not-yet-bound term back
down as another instance of the same primitive operator's `eval_time` -- the
inner call's "fresh" variable resolves to the identical term the outer call
already holds, producing a syntactically self-referential comparison
(`x < x`, or `x == x` under `NecessityOperator`'s world-quantifier form) that
Z3's own term simplifier folds to a Boolean constant *before either quantifier
closes*, independent of the argument formula's actual content.

A conclusion constraint that Z3 has already folded to a Boolean literal at
construction time is unfalsifiable by encoding: `find_countermodel` can never
return a countermodel for it (there is no residual constraint left to search
against), so a formula whose conclusion collapses to `True` gets reported by
the oracle as valid -- validity it never actually established, because no
solve ever ran against the formula's real content. This is a soundness defect
in the encoding layer, not a performance or style issue, and the guard below
tests exactly that structural property: not "does the solver return the right
answer" (which a slow/timed-out solve could mask either way) but "does the
*conclusion constraint the solver would be asked to decide* still depend on
the formula's actual content, or has it already been silently decided by term
interning before any quantifier or solve ever ran."

Fix: `z3.FreshInt(prefix)` generates a distinct term on every call regardless
of name reuse or nesting depth, eliminating the aliasing class of bug
entirely. This module performs ZERO solves -- it only builds
`ModelConstraints` and applies `z3.simplify()` -- so it belongs in the
routine gating pass (not `slow`, not `xdist_serial`) and runs in seconds.
"""

from __future__ import annotations

import z3

from model_checker import ModelConstraints, Syntax
from model_checker.theory_lib.bimodal import (
    BimodalSemantics,
    BimodalProposition,
    bimodal_operators,
)
from model_checker.utils.context import isolated_z3_context

from bimodal_logic.translation import json_to_prefix, prefix_to_infix, temporal_depth
from bimodal_logic.tests.test_cross_oracle_differential import (
    _enumerate_primitive_formulas,
)

# Complexity bound for the exhaustive sweep below. Matches the population the
# gating/exhaustive oracle suite already uses (known_conclusive_complexity5.json),
# so this guard exercises exactly the formulas that suite reasons about.
_MAX_COMPLEXITY = 5
_ATOMS = ["p"]


def _contains_bot(formula_json: dict) -> bool:
    """Return True iff the formula tree contains a "bot" node anywhere.

    A conclusion constraint folding to a Boolean literal because the formula
    genuinely contains `\\bot` (e.g. `\\bot \\Until \\bot`) is an expected,
    correct tautology/contradiction -- not evidence of the aliasing defect.
    """
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


def _build_conclusion_constraint(formula_json: dict):
    """Build conclusion_constraints[0] exactly as find_countermodel() would,
    stopping short of BimodalStructure construction so ZERO solving occurs.
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
        "max_time": 1.0,  # irrelevant: no solve is performed
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
        return z3.simplify(conclusion)


def _is_boolean_literal(term) -> bool:
    return bool(z3.is_true(term) or z3.is_false(term))


class TestNoSpuriousEncodingCollapse:
    """Exhaustive structural sweep: no non-`\\bot` formula's conclusion
    constraint may fold to a Boolean literal at construction time.
    """

    def test_no_non_bot_formula_folds_to_boolean_literal(self):
        """For every complexity<=5 primitive formula without `\\bot`, the
        conclusion constraint z3.simplify() produces must not be a Boolean
        literal -- except the small, independently-verified allowlist of
        genuine propositional/modal tautologies that involve no nested
        same-primitive quantifier at all (see module docstring and the
        allowlist comment above `_build_conclusion_constraint`).
        """
        formulas = _enumerate_primitive_formulas(_MAX_COMPLEXITY, _ATOMS)
        assert len(formulas) == 274, (
            f"enumerator population changed: expected 274, got {len(formulas)}. "
            "This guard's allowlist was derived against the 274-formula "
            "complexity<=5 population -- re-derive the allowlist if this "
            "enumerator intentionally changed."
        )

        unexpected_collapses = []
        for index, formula_json in enumerate(formulas):
            if _contains_bot(formula_json):
                continue
            simplified = _build_conclusion_constraint(formula_json)
            if not _is_boolean_literal(simplified):
                continue

            # Genuine, independently-verified non-bug tautologies: formulas
            # with no quantified operator at all (pure imp/atom trees) can
            # never exhibit the nested-eval_time aliasing this guard exists
            # to catch, because there is no bound-variable declaration to
            # alias in the first place.
            if not _contains_quantified_operator(formula_json):
                continue

            # \Box is confirmed immune to the nested-eval_time aliasing
            # mechanism (NecessityOperator.true_at never compares its bound
            # variable to eval_time -- see module docstring). A folded,
            # non-bot, box-only formula is therefore a genuine tautology
            # (e.g. \Box(p->p), \Box(p)->\Box(p)), not this defect.
            if _is_box_only(formula_json):
                continue

            unexpected_collapses.append((index, formula_json, simplified))

        assert not unexpected_collapses, (
            "Non-\\bot formula(s) whose conclusion constraint folded to a "
            "Boolean literal at construction time -- unfalsifiable by "
            "encoding, meaning find_countermodel() could never find a "
            "countermodel for them regardless of their actual content. "
            "This is the Z3 constant-interning aliasing defect: a quantified "
            "operator's bound variable collided with an outer, not-yet-bound "
            "variable of the same name. Details:\n"
            + "\n".join(
                f"  index={i} folded_to={s} formula={f}"
                for i, f, s in unexpected_collapses
            )
        )


def _contains_quantified_operator(formula_json: dict) -> bool:
    """True iff the formula tree contains box, untl, or snce anywhere --
    i.e. an operator whose true_at/false_at declares a Z3 bound variable.
    """
    tag = formula_json.get("tag")
    if tag in ("box", "untl", "snce"):
        return True
    if tag in ("atom", "bot", "top"):
        return False
    if "arg" in formula_json:
        return _contains_quantified_operator(formula_json["arg"])
    if "child" in formula_json:
        return _contains_quantified_operator(formula_json["child"])
    if "left" in formula_json and "right" in formula_json:
        return (
            _contains_quantified_operator(formula_json["left"])
            or _contains_quantified_operator(formula_json["right"])
        )
    if "event" in formula_json and "guard" in formula_json:
        return (
            _contains_quantified_operator(formula_json["event"])
            or _contains_quantified_operator(formula_json["guard"])
        )
    raise ValueError(f"_contains_quantified_operator: unrecognized shape: {formula_json!r}")


def _is_box_only(formula_json: dict) -> bool:
    """True iff the formula tree contains no `untl`/`snce` node -- i.e. its
    only quantified operator (if any) is `\\Box`, which is confirmed immune
    to the nested-eval_time aliasing mechanism this guard targets.
    """
    tag = formula_json.get("tag")
    if tag in ("untl", "snce"):
        return False
    if tag in ("atom", "bot", "top", "box"):
        # box's own child still needs checking
        if tag == "box":
            return _is_box_only(formula_json["child"])
        return True
    if "arg" in formula_json:
        return _is_box_only(formula_json["arg"])
    if "left" in formula_json and "right" in formula_json:
        return _is_box_only(formula_json["left"]) and _is_box_only(formula_json["right"])
    if "event" in formula_json and "guard" in formula_json:
        return _is_box_only(formula_json["event"]) and _is_box_only(formula_json["guard"])
    raise ValueError(f"_is_box_only: unrecognized formula shape: {formula_json!r}")


class TestNamedReproductions:
    """Targeted named tests for the three formulas whose collapse was
    directly verified pre-fix (see specs/139_.../evidence/pre-fix-state.md).
    Each asserts the specific structural property whose violation
    constitutes the soundness failure mode this task fixes.
    """

    def test_until_until_p_conclusion_not_boolean_literal(self):
        """(p \\Until p) \\Until p: pre-fix, UntilOperator's fixed-name
        `until_witness_time`/`until_guard_time` bound variables collided
        with the nested \\Until's own declarations (event-position nesting
        of the same primitive operator), folding the conclusion constraint
        to the Z3 constant `True` -- vacuously "valid" regardless of `p`.
        Post-fix, the conclusion constraint must still depend on `p`.
        """
        formula = {
            "tag": "untl",
            "event": {
                "tag": "untl",
                "event": {"tag": "atom", "name": "p"},
                "guard": {"tag": "atom", "name": "p"},
            },
            "guard": {"tag": "atom", "name": "p"},
        }
        simplified = _build_conclusion_constraint(formula)
        assert not _is_boolean_literal(simplified), (
            f"(p Until p) Until p's conclusion constraint folded to a "
            f"Boolean literal ({simplified}) -- the Until/Until nested "
            f"aliasing defect has returned."
        )

    def test_since_since_p_conclusion_not_boolean_literal(self):
        """(p \\Since p) \\Since p: the Since-operator mirror of the Until
        reproduction above -- same nested-same-primitive-in-event-position
        pattern, same pre-fix collapse to constant `True`.
        """
        formula = {
            "tag": "snce",
            "event": {
                "tag": "snce",
                "event": {"tag": "atom", "name": "p"},
                "guard": {"tag": "atom", "name": "p"},
            },
            "guard": {"tag": "atom", "name": "p"},
        }
        simplified = _build_conclusion_constraint(formula)
        assert not _is_boolean_literal(simplified), (
            f"(p Since p) Since p's conclusion constraint folded to a "
            f"Boolean literal ({simplified}) -- the Since/Since nested "
            f"aliasing defect has returned."
        )

    def test_gg_p_conclusion_not_boolean_literal(self):
        """G(G(p)) (all_future(all_future(p))): pre-fix, FutureOperator's
        fixed-name `future_true_time` collided across the two nested
        \\Future instances, folding the conclusion constraint to constant
        `False` -- trivially UNSAT, producing a fast *spurious* `None`
        (reported "no countermodel", i.e. reported valid) regardless of
        `p`. Post-fix, the conclusion constraint must still depend on `p`;
        `G(G(p))` is genuinely invalid (see test_soundness_regression.py),
        so an honest decide-or-timeout is the correct outcome, never a
        construction-time constant.
        """
        formula = {
            "tag": "all_future",
            "arg": {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}},
        }
        simplified = _build_conclusion_constraint(formula)
        assert not _is_boolean_literal(simplified), (
            f"G(G(p))'s conclusion constraint folded to a Boolean literal "
            f"({simplified}) -- the Future/Future nested aliasing defect "
            f"has returned."
        )
