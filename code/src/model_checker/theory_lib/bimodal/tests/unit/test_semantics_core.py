"""Unit tests for `BimodalSemantics`'s framework contract under the certificate redesign
(Phase 9 of the implementation plan): settings, the vestigial `N`/`all_states` attributes
(D3), `true_at` as translate-then-lookup (D5), and `finalize_certificate()`'s idempotence
(D6).
"""

from __future__ import annotations

import pytest

from model_checker import z3_shim as z3
from model_checker.syntactic import Syntax
from model_checker.theory_lib.bimodal.operators import bimodal_operators
from model_checker.theory_lib.bimodal.semantic import certificate as certificate_module
from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics
from model_checker.theory_lib.bimodal.semantic.formula import Atom, Box, translate


def _settings(**overrides):
    settings = dict(BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS)
    settings.update(overrides)
    return settings


def _sentence(infix: str):
    """Build one fully type-updated `Sentence` for `infix`, via the real `Syntax` pipeline
    (matching `test_formula.py`'s helper of the same name and purpose)."""
    syntax = Syntax([infix], [], bimodal_operators)
    return syntax.premises[0]


class TestConstruction:
    def test_construction_with_new_settings_succeeds(self):
        semantics = BimodalSemantics(_settings())
        assert semantics.back == 2
        assert semantics.mid == 1
        assert semantics.fwd == 2
        assert semantics.max_witnesses is None

    def test_n_and_all_states_present_per_d3(self):
        """`models/structure.py` unconditionally reads `semantics.N`/`semantics.all_states`
        (D3); the certificate encoding has no 'N' setting, so BimodalSemantics.__init__
        must set these explicitly rather than relying on SemanticDefaults."""
        semantics = BimodalSemantics(_settings())
        assert semantics.N == 0
        assert semantics.all_states == []

    def test_main_point_names_lasso_zero_with_no_fixed_position(self):
        semantics = BimodalSemantics(_settings())
        assert semantics.main_point == {"lasso": 0, "position": None}

    def test_frame_constraints_start_empty(self):
        semantics = BimodalSemantics(_settings())
        assert semantics.frame_constraints == []

    def test_custom_segment_lengths_and_max_witnesses_are_honored(self):
        semantics = BimodalSemantics(_settings(back=3, mid=2, fwd=4, max_witnesses=2))
        assert (semantics.back, semantics.mid, semantics.fwd) == (3, 2, 4)
        assert semantics.max_witnesses == 2
        assert semantics.witness_registry.nb == 3
        assert semantics.witness_registry.nm == 2
        assert semantics.witness_registry.nf == 4


class TestTrueAtIsTranslateThenLookup:
    def test_true_at_returns_the_registry_bit_for_an_atom(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("A")
        eval_point = {"lasso": 0, "position": 0}
        expr = semantics.true_at(sentence, eval_point)
        expected = semantics.witness_registry.bit(0, 0, Atom("A"))
        assert expr.eq(expected) if hasattr(expr, "eq") else expr == expected

    def test_true_at_agrees_with_translate_for_a_compound_sentence(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("\\Box A")
        eval_point = {"lasso": 1, "position": -1}
        expr = semantics.true_at(sentence, eval_point)
        expected_formula = translate(sentence)
        assert isinstance(expected_formula, Box)
        expected = semantics.witness_registry.bit(1, -1, expected_formula)
        assert expr.eq(expected)

    def test_false_at_is_the_negation_of_true_at(self):
        import model_checker.z3_shim as z3

        semantics = BimodalSemantics(_settings())
        sentence = _sentence("A")
        eval_point = {"lasso": 0, "position": 0}
        true_expr = semantics.true_at(sentence, eval_point)
        false_expr = semantics.false_at(sentence, eval_point)
        assert false_expr.eq(z3.Not(true_expr))


class TestPremiseAndConclusionBehavior:
    def test_premise_behavior_registers_closure_and_returns_a_bool_expr(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("A")
        expr = semantics.premise_behavior(sentence)
        assert expr is not None
        assert Atom("A") in semantics._known_closure

    def test_conclusion_behavior_registers_closure_and_returns_a_bool_expr(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("A")
        expr = semantics.conclusion_behavior(sentence)
        assert expr is not None
        assert Atom("A") in semantics._known_closure

    def test_premise_behavior_closure_includes_subformulas_of_a_box(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("\\Box A")
        semantics.premise_behavior(sentence)
        formula = translate(sentence)
        assert isinstance(formula, Box)
        assert formula in semantics._known_closure
        assert formula.child in semantics._known_closure


class TestFinalizeCertificateIsIdempotent:
    def test_finalize_certificate_called_twice_adds_constraints_only_once(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("A")
        semantics.premise_behavior(sentence)

        semantics.finalize_certificate()
        first_count = len(semantics.frame_constraints)
        assert first_count > 0

        semantics.finalize_certificate()
        second_count = len(semantics.frame_constraints)
        assert second_count == first_count

    def test_finalize_certificate_allocates_one_witness_lasso_per_box(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("\\Box A")
        semantics.premise_behavior(sentence)
        semantics.finalize_certificate()

        # Main lasso (0) plus exactly one witness lasso for the single boxed subformula.
        assert set(semantics.witness_registry._witness_lassos.values()) == {1}

    def test_finalize_certificate_mutates_frame_constraints_in_place(self):
        """D6: ModelConstraints reads semantics.frame_constraints by reference, so
        finalize_certificate() must mutate the existing list object rather than
        reassigning self.frame_constraints to a new one."""
        semantics = BimodalSemantics(_settings())
        alias = semantics.frame_constraints
        sentence = _sentence("A")
        semantics.premise_behavior(sentence)
        semantics.finalize_certificate()
        assert semantics.frame_constraints is alias
        assert len(alias) > 0


def _solve(semantics, premises, conclusions):
    """Directly assemble and solve the certificate search's constraint set, bypassing
    ModelConstraints/BimodalStructure (not yet rewritten -- Phase 12). Mirrors exactly what
    ModelConstraints.__init__ and BimodalStructure._setup_solver will do once they exist:
    premise/conclusion behavior first (so the closure is fully known), then
    finalize_certificate(), then solve."""
    premise_constraints = [semantics.premise_behavior(p) for p in premises]
    conclusion_constraints = [semantics.conclusion_behavior(c) for c in conclusions]
    semantics.finalize_certificate()

    solver = z3.Solver()
    for constraint in semantics.frame_constraints + premise_constraints + conclusion_constraints:
        solver.add(constraint)
    result = solver.check()
    return solver, result


class TestCertificateExtraction:
    def test_extracted_family_from_a_simple_countermodel_passes_the_rechecker(self):
        """A / B: A true and B false somewhere is trivially satisfiable with no boxes."""
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        premise = _sentence("A")
        conclusion = _sentence("B")
        solver, result = _solve(semantics, [premise], [conclusion])
        assert result == z3.sat

        family, target_time = semantics.extract_certificate(solver.model())
        verdict = certificate_module.recheck(
            family,
            premises=[translate(premise)],
            conclusions=[translate(conclusion)],
            target_time=target_time,
        )
        assert verdict["status"] == "countermodel", verdict

    def test_extracted_family_for_a_boxed_premise_has_a_witness_lasso_when_guessed_false(self):
        """\\Box A / B: forces the search to consider a witness lasso for A (the guess may
        end up true or false depending on segment lengths; either way extraction must
        round-trip through the re-checker without a structural violation)."""
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        premise = _sentence("\\Box A")
        conclusion = _sentence("B")
        solver, result = _solve(semantics, [premise], [conclusion])
        assert result == z3.sat

        family, target_time = semantics.extract_certificate(solver.model())
        verdict = certificate_module.recheck(
            family,
            premises=[translate(premise)],
            conclusions=[translate(conclusion)],
            target_time=target_time,
        )
        assert verdict["status"] == "countermodel", verdict
        # Main lasso plus exactly one witness lasso for the single boxed subformula.
        assert len(family.lassos) == 2

    def test_export_certificate_json_round_trips_through_recheck_json(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        premise = _sentence("A")
        conclusion = _sentence("B")
        solver, result = _solve(semantics, [premise], [conclusion])
        assert result == z3.sat

        family, target_time = semantics.extract_certificate(solver.model())
        wire = semantics.export_certificate_json(family, target_time)
        assert wire["target"]["time"] == target_time
        assert wire["target"]["premises"] == [{"tag": "atom", "name": "A"}]
        assert wire["target"]["conclusions"] == [{"tag": "atom", "name": "B"}]
        verdict = certificate_module.recheck_json(wire)
        assert verdict["status"] == "countermodel", verdict


from model_checker.theory_lib.bimodal.tests._lean_check import (  # noqa: E402
    SKIP_REASON as _LEAN_SKIP_REASON,
    run_check_certificate as _run_lean_check_certificate,
)

# This module's own per-invocation timeout bound, matching
# `test_certificate_lean_agreement.py`'s `PER_FIXTURE_TIMEOUT_SECONDS` (not shared via the
# helper: that name is specific to the fixture-corpus consumer).
_LEAN_TIMEOUT_SECONDS = 30


@pytest.mark.skipif(_LEAN_SKIP_REASON is not None, reason=_LEAN_SKIP_REASON or "")
class TestExportedCertificateAgreesWithLeanBinary:
    """Verification criterion: exported JSON for an extracted certificate is accepted by the
    live `lake exe check_certificate` binary when available (reusing
    `test_certificate_lean_agreement.py`'s resolution/subprocess plumbing rather than
    duplicating it -- matching the Phase 8 handoff's precedent of extending, not
    re-implementing, that module's harness).

    A `countermodel` verdict's `"acceptance"` field distinguishes what the binary actually did:
    `"entailment"` means it constructed the paper-countermodel existence term for this
    certificate (a kernel-checked proof); an absent field reads as `"decided"` (the weaker
    four-`Decidable`-instances claim). `"acceptance"` appears on `countermodel` only, never on
    `rejected` or `error` -- this is the one place in the suite where a certificate this
    repository actually *built* (not a fixture) gets an entailment-grade verdict."""

    def test_exported_json_for_a_simple_countermodel_agrees_with_the_lean_binary(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        premise = _sentence("A")
        conclusion = _sentence("B")
        solver, result = _solve(semantics, [premise], [conclusion])
        assert result == z3.sat

        family, target_time = semantics.extract_certificate(solver.model())
        wire = semantics.export_certificate_json(family, target_time)
        python_verdict = certificate_module.recheck_json(wire)

        lean_verdict = _run_lean_check_certificate(wire, _LEAN_TIMEOUT_SECONDS)
        assert lean_verdict is not None, "lake exe check_certificate did not respond in time"
        assert lean_verdict["status"] == python_verdict["status"] == "countermodel", (
            python_verdict,
            lean_verdict,
        )
        # Absent 'acceptance' reads as "decided" -- see class docstring.
        acceptance = lean_verdict.get("acceptance", "decided")
        assert acceptance in {"entailment", "decided"}, (
            f"unrecognized acceptance value {acceptance!r}"
        )
        assert acceptance == "entailment", (
            "expected 'entailment' (Lean constructed the paper-countermodel existence term) "
            f"for this live-extracted certificate against the current binary, got {acceptance!r}"
        )
