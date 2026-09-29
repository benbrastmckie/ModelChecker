"""Tests for the BimodalModelIterator implementation under the certificate redesign
(Phase 15): difference/non-isomorphism constraints over label bits and box guesses,
label/guess-based difference detection and display, the three shared-iterator
extension-point overrides (`_pin_theory_specific_values`, `_build_exclusion_constraints`
by way of `_create_difference_constraint`, `_check_model_isomorphism`), and live,
non-mocked end-to-end `iterate: N` coverage (`TestLiveIteration`).

HISTORY: this module's tests were previously method-level only, with a module
docstring explaining that a full live run could not be exercised correctly: the shared
`BaseModelIterator.iterate_generator()` called the theory-agnostic `ConstraintGenerator`
directly (`model_checker/iterate/constraints.py`), gated on `hasattr(semantics,
'is_world')` -- true of the other three theories, false of this one by design (D3/D4
have no state-existence predicate) -- so `BimodalModelIterator`'s own difference/
isomorphism overrides were dead code from the live loop's perspective, and a live
`iterate: N > 1` run crashed outright on `is_world` before that gap was even reached.
The shared iterate framework now exposes three theory-specific extension points
(`iterate/core.py`'s `_pin_theory_specific_values`, `_build_exclusion_constraints`, and
`_check_model_isomorphism`) that `BimodalModelIterator` overrides below, and the live
loop genuinely consults them -- `TestLiveIteration` exercises exactly this path.
"""

from __future__ import annotations

from types import SimpleNamespace
from unittest.mock import Mock, patch

import pytest

from model_checker import z3_shim as z3
from model_checker.builder.example import BuildExample
from model_checker.solver import is_true
from model_checker.theory_lib.bimodal import get_theory
from model_checker.theory_lib.bimodal.examples import (
    BM_CM_1_conclusions,
    BM_CM_1_premises,
    BM_CM_1_settings,
)
from model_checker.theory_lib.bimodal.iterate import (
    BimodalModelIterator,
    iterate_example,
)
from model_checker.theory_lib.bimodal.semantic.certificate import LabelledLasso, WitnessFamily
from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics
from model_checker.theory_lib.bimodal.semantic.formula import Atom, Box
from model_checker.theory_lib.bimodal.semantic import certificate, symmetry
from model_checker.theory_lib.bimodal.tests._build_support import _settings
from model_checker.theory_lib.bimodal.tests._pinned_eval import full_constraints


def _mock_build_example(semantics):
    """A Mock-based `build_example`, matching the construction pattern already used by
    this test module before the redesign: `BaseModelIterator.__init__`'s own
    `ConstraintGenerator` only needs `model_structure.solver` to be a live (possibly
    empty) Z3 solver, `model_constraints.all_constraints`, and `settings`."""
    mock_example = Mock(spec=BuildExample)
    mock_example.model_structure = Mock()
    mock_example.model_structure.z3_model_status = True
    mock_example.model_structure.z3_model = Mock()
    mock_example.model_structure.solver = z3.Solver()
    mock_example.model_structure.z3_model_runtime = 0.1
    mock_example.model_structure._search_duration = 0.1
    mock_example.model_structure._total_search_time = 0.1
    # IterationStatistics.add_model() calls len() on these -- must be real lists, not
    # Mock's auto-created attributes.
    mock_example.model_structure.z3_world_states = []
    mock_example.model_structure.z3_possible_states = []

    mock_example.model_constraints = Mock()
    mock_example.model_constraints.all_constraints = []
    mock_example.model_constraints.semantics = semantics

    mock_example.settings = {'iterate': 1, 'max_time': 5.0}
    return mock_example


class TestConstruction:
    def test_iterator_constructs_against_a_real_bimodal_semantics(self):
        semantics = BimodalSemantics(_settings())
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        assert iterator is not None
        assert iterator.build_example.model_constraints.semantics is semantics


class TestDifferenceConstraintOverLabelsAndGuesses:
    def _solved_model(self, semantics, premise_infix="A", conclusion_infix="B"):
        from model_checker.syntactic import Syntax
        from model_checker.theory_lib.bimodal.operators import bimodal_operators

        premise = Syntax([premise_infix], [], bimodal_operators).premises[0]
        conclusion = Syntax([conclusion_infix], [], bimodal_operators).premises[0]
        premise_constraint = semantics.premise_behavior(premise)
        conclusion_constraint = semantics.conclusion_behavior(conclusion)
        semantics.finalize_certificate()
        solver = z3.Solver()
        for c in semantics.frame_constraints + [premise_constraint, conclusion_constraint]:
            solver.add(c)
        assert solver.check() == z3.sat
        return solver.model()

    def test_create_difference_constraint_is_true_for_the_solved_model_itself(self):
        """A blocking clause built against a model must itself be FALSE when evaluated
        against that same model (every disjunct is `var != var's own value`)."""
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        model = self._solved_model(semantics)

        constraint = iterator._create_difference_constraint([model])
        result = model.eval(constraint, model_completion=True)
        assert str(result) == "False"

    def test_create_difference_constraint_with_no_variables_is_trivially_true(self):
        semantics = BimodalSemantics(_settings())
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        constraint = iterator._create_difference_constraint([])
        assert str(constraint) == "True"

    def test_create_non_isomorphic_constraint_is_false_against_its_own_model(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        model = self._solved_model(semantics)

        constraint = iterator._create_non_isomorphic_constraint(model)
        result = model.eval(constraint, model_completion=True)
        assert str(result) == "False"

    def test_build_exclusion_constraints_is_non_empty_for_a_solved_model(self):
        """`BaseModelIterator._build_exclusion_constraints` (Extension Point 2) must
        actually reach this theory's own `_create_difference_constraint` -- the live
        loop's central defect this plan fixes -- and produce a real, non-empty
        exclusion constraint, not the `[]` the generic `is_world`-gated path silently
        produced for bimodal before this phase."""
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        model = self._solved_model(semantics)

        result = iterator._build_exclusion_constraints([model])
        assert len(result) == 1
        assert not is_true(model.eval(result[0], model_completion=True))


class TestNonIsomorphicOrbitExclusion:
    """Coverage for `_create_non_isomorphic_constraint`'s Phase 4 rewrite: it now
    excludes every recheck-valid element of the handed model's rotation/permutation
    orbit (`semantic/symmetry.py`), not just the exact assignment."""

    def _solved_model(self, semantics, premise_infix="\\Future A", conclusion_infix="\\Box A"):
        from model_checker.syntactic import Syntax
        from model_checker.theory_lib.bimodal.operators import bimodal_operators

        premise = Syntax([premise_infix], [], bimodal_operators).premises[0]
        conclusion = Syntax([conclusion_infix], [], bimodal_operators).premises[0]
        premise_constraint = semantics.premise_behavior(premise)
        conclusion_constraint = semantics.conclusion_behavior(conclusion)
        semantics.finalize_certificate()
        solver = z3.Solver()
        for c in semantics.frame_constraints + [premise_constraint, conclusion_constraint]:
            solver.add(c)
        assert solver.check() == z3.sat
        return solver.model()

    def _countermodel_element_count(self, semantics, model):
        """Independently recompute, without touching `iterate.py`, how many group
        elements' transforms recheck as `"countermodel"` for the handed model -- the
        expected conjunct count `_create_non_isomorphic_constraint` must match."""
        registry = semantics.witness_registry
        family, target_time = semantics.extract_certificate(model)
        lasso_count = len(family.lassos)
        count = 0
        for element in symmetry.enumerate_group(registry.nb, registry.nf, lasso_count):
            transformed, transformed_time = symmetry.apply(element, family, target_time)
            verdict = certificate.recheck(
                transformed, semantics._premise_formulas, semantics._conclusion_formulas, transformed_time
            )
            if verdict.get("status") == "countermodel":
                count += 1
        return count

    def test_clause_is_false_against_its_own_model(self):
        semantics = BimodalSemantics(_settings(back=2, mid=1, fwd=2))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        model = self._solved_model(semantics)

        constraint = iterator._create_non_isomorphic_constraint(model)
        result = model.eval(constraint, model_completion=True)
        assert str(result) == "False"

    def test_conjunct_count_matches_the_number_of_countermodel_elements(self):
        semantics = BimodalSemantics(_settings(back=2, mid=1, fwd=2))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        model = self._solved_model(semantics)
        expected = self._countermodel_element_count(semantics, model)
        assert expected > 1, "test fixture must exercise a nontrivial orbit"

        constraint = iterator._create_non_isomorphic_constraint(model)
        assert constraint.decl().name() == "and"
        assert constraint.num_args() == expected

    def test_clause_excludes_every_retained_orbit_element_not_just_the_representative(self):
        """For each retained element `g`, the clause must evaluate to `False` under the
        assignment `g(handed_model)` -- the orbit really is excluded, not just its
        representative."""
        semantics = BimodalSemantics(_settings(back=2, mid=1, fwd=2))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        model = self._solved_model(semantics)
        registry = semantics.witness_registry
        generator = semantics.constraint_generator

        constraint = iterator._create_non_isomorphic_constraint(model)
        lasso_count = len(semantics.extract_certificate(model)[0].lassos)

        for element in symmetry.enumerate_group(registry.nb, registry.nf, lasso_count):
            substitutions = []
            for old_key, new_key in symmetry.slot_action(registry, element).items():
                old_var = registry._bits[old_key]
                new_var = registry._bits[new_key]
                value = is_true(model.eval(old_var, model_completion=True))
                substitutions.append((new_var, z3.BoolVal(value)))
            for var in registry._guesses.values():
                value = is_true(model.eval(var, model_completion=True))
                substitutions.append((var, z3.BoolVal(value)))
            for old_t, new_t in symmetry.selector_action(registry, element).items():
                old_var = generator.sel(old_t)
                new_var = generator.sel(new_t)
                value = is_true(model.eval(old_var, model_completion=True))
                substitutions.append((new_var, z3.BoolVal(value)))

            transformed = z3.substitute(constraint, *substitutions)
            simplified = z3.simplify(transformed)
            assert str(simplified) == "False", (
                f"clause did not exclude orbit element {element!r}"
            )

    def test_a_recheck_invalid_element_contributes_no_conjunct(self):
        """An element whose transform breaks a certificate condition (D-A's rotation
        risk) is dropped, not asserted -- verified by directly controlling
        `enumerate_group`/`recheck`'s verdicts rather than hunting for a naturally
        occurring counterexample among solved models (Phase 1's own measurement found
        none for the example fixtures this suite already uses)."""
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        model = self._solved_model(semantics, premise_infix="A", conclusion_infix="B")

        identity = symmetry._identity_element(1)
        other = symmetry.GroupElement(rotations=((0, 0),), perm=())
        verdicts = iter([
            {"status": "countermodel", "time": 0},
            {"status": "rejected", "failed": []},
        ])
        with patch.object(symmetry, "enumerate_group", return_value=[identity, other]), \
             patch.object(certificate, "recheck", side_effect=lambda *a, **k: next(verdicts)):
            constraint = iterator._create_non_isomorphic_constraint(model)

        # Only the first (countermodel) element contributes: with a single retained
        # element the And-of-one collapses to that element's own Or clause, not an
        # `and` application.
        assert constraint.decl().name() == "or"

    def test_trivially_true_when_no_orbit_element_survives_the_recheck_gate(self):
        """`_orbit_variables()` is never literally empty once `finalize_certificate` has
        run (the target selector always populates `_sel` for the window, independent of
        closure size -- see `_orbit_variables`'s own docstring), so the operative
        trivial-true condition for *this* clause is that every group element's transform
        fails the recheck gate (D-C), leaving zero conjuncts -- not, as for
        `_create_difference_constraint`, an empty variable set."""
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        model = self._solved_model(semantics, premise_infix="A", conclusion_infix="B")

        with patch.object(certificate, "recheck", return_value={"status": "rejected", "failed": []}):
            constraint = iterator._create_non_isomorphic_constraint(model)

        assert str(constraint) == "True"

    def test_certificate_variables_and_difference_constraint_are_unchanged(self):
        """Non-Goal 1 regression: `_certificate_variables()` still ranges over exactly
        `_bits` + `_guesses`, never `_sel` -- the orbit clause's wider variable set
        (`_orbit_variables`) must not leak into the difference constraint."""
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        model = self._solved_model(semantics, premise_infix="A", conclusion_infix="B")

        registry = semantics.witness_registry
        certificate_vars = set(iterator._certificate_variables())
        expected = set(registry._bits.values()) | set(registry._guesses.values())
        assert certificate_vars == expected

        orbit_vars = set(iterator._orbit_variables())
        generator = semantics.constraint_generator
        assert orbit_vars == expected | set(generator._sel.values())


class TestPinTheorySpecificValues:
    """Coverage for `BimodalModelIterator._pin_theory_specific_values`, the Extension
    Point 1 override that pins certificate variables since the generic `is_world`/
    `verify`/`falsify` pinning in `iterate/models.py` cannot reach this theory's model
    content at all."""

    def _solved_model(self, semantics, premise_infix="A", conclusion_infix="B"):
        from model_checker.syntactic import Syntax
        from model_checker.theory_lib.bimodal.operators import bimodal_operators

        premise = Syntax([premise_infix], [], bimodal_operators).premises[0]
        conclusion = Syntax([conclusion_infix], [], bimodal_operators).premises[0]
        premise_constraint = semantics.premise_behavior(premise)
        conclusion_constraint = semantics.conclusion_behavior(conclusion)
        semantics.finalize_certificate()
        solver = z3.Solver()
        for c in semantics.frame_constraints + [premise_constraint, conclusion_constraint]:
            solver.add(c)
        assert solver.check() == z3.sat
        return solver.model()

    def test_pin_adds_one_constraint_per_certificate_variable_matching_the_model(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        model = self._solved_model(semantics)

        registry = semantics.witness_registry
        # `_pin_theory_specific_values` also pins the target selector (`_sel`) --
        # discovered necessary while testing Phase 4's live loop: leaving `_sel`
        # unpinned let the rebuild's fresh `finalize_certificate()` pick a different
        # target position than the one the search's own model selected, which could
        # violate the (already-pinned) guarded premise/conclusion implications and
        # make the rebuild spuriously unsat. `_certificate_variables()` itself
        # (`_bits` + `_guesses` only) is unrelated and untouched -- Non-Goal 1.
        variables = (
            list(registry._bits.values())
            + list(registry._guesses.values())
            + list(semantics.constraint_generator._sel.values())
        )
        assert variables, "expected at least one certificate variable from a solved model"

        temp_solver = z3.Solver()
        model_constraints = SimpleNamespace(semantics=semantics)
        iterator._pin_theory_specific_values(temp_solver, model, model_constraints)

        assertions = list(temp_solver.assertions())
        assert len(assertions) == len(variables)
        # Every pinned assertion must hold under the very model it was pinned from.
        for assertion in assertions:
            assert is_true(model.eval(assertion, model_completion=True))

    def test_pin_still_pins_the_target_selector_when_no_bits_or_guesses_exist(self):
        """The target selector's window is a function of `back`/`mid`/`fwd` alone,
        independent of the closure -- so `_sel` gets pinned even when there is no
        premise/conclusion-derived closure content to produce any `_bits`/`_guesses`
        at all. This replaces an earlier "pin is a no-op" expectation that predates
        the `_sel`-pinning fix."""
        semantics = BimodalSemantics(_settings())
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        temp_solver = z3.Solver()
        model_constraints = SimpleNamespace(semantics=semantics)

        iterator._pin_theory_specific_values(temp_solver, Mock(), model_constraints)

        registry = semantics.witness_registry
        assert list(registry._bits.values()) == []
        assert list(registry._guesses.values()) == []
        window = list(registry.target_window())
        assertions = list(temp_solver.assertions())
        assert len(assertions) == len(window)


class TestCheckModelIsomorphism:
    """Coverage for `BimodalModelIterator._check_model_isomorphism`, the Extension
    Point 3 override: a real orbit-key detector (Phase 3 of the rotation-invariant
    isomorphism-rejection plan) that remains a complete opt-out of the shared
    `ModelGraph` path -- see the method's own docstring for why this theory cannot use
    graph-based checking at all."""

    def test_short_circuits_without_constructing_a_model_graph(self):
        semantics = BimodalSemantics(_settings())
        iterator = BimodalModelIterator(_mock_build_example(semantics))

        with patch("model_checker.iterate.graph.ModelGraph") as mock_model_graph:
            result = iterator._check_model_isomorphism(Mock(), Mock())

        assert result == (False, None)
        mock_model_graph.assert_not_called()

    def _nontrivial_family_and_target(self):
        """`back=2, mid=1, fwd=2` (nontrivial group: `(2*2)**1 * 0! = 4` elements)."""
        atom = Atom("A")
        main = LabelledLasso(
            back=(frozenset({atom}), frozenset()),
            mid=(frozenset(),),
            fwd=(frozenset({atom}), frozenset()),
        )
        return WitnessFamily(bx={}, lassos=(main,)), -1

    def test_a_rotation_of_a_previous_certificate_is_detected(self):
        semantics = BimodalSemantics(_settings(back=2, mid=1, fwd=2))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        family, target_time = self._nontrivial_family_and_target()

        prev_model = Mock(name="prev_z3_model")
        prev_structure = SimpleNamespace(certificate=family, target_time=target_time)
        iterator.model_structures = [prev_structure]
        iterator.found_models = [prev_model]

        element = symmetry.GroupElement(rotations=((1, 1),), perm=())
        rotated_family, rotated_time = symmetry.apply(element, family, target_time)
        new_structure = SimpleNamespace(certificate=rotated_family, target_time=rotated_time)

        result = iterator._check_model_isomorphism(new_structure, Mock())
        assert result == (True, prev_model)

    def test_a_witness_permuted_duplicate_is_detected(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1, max_witnesses=None))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        atom_p, atom_q = Atom("P"), Atom("Q")
        main = LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset(),))
        w1 = LabelledLasso(back=(frozenset({atom_p}),), mid=(), fwd=(frozenset({atom_p}),))
        w2 = LabelledLasso(back=(frozenset({atom_q}),), mid=(), fwd=(frozenset({atom_q}),))
        family = WitnessFamily(bx={}, lassos=(main, w1, w2))

        prev_model = Mock(name="prev_z3_model")
        prev_structure = SimpleNamespace(certificate=family, target_time=0)
        iterator.model_structures = [prev_structure]
        iterator.found_models = [prev_model]

        permuted = symmetry.permute_witnesses(family, (2, 1))
        new_structure = SimpleNamespace(certificate=permuted, target_time=0)

        result = iterator._check_model_isomorphism(new_structure, Mock())
        assert result == (True, prev_model)

    def test_a_mid_difference_is_not_detected_as_isomorphic(self):
        semantics = BimodalSemantics(_settings(back=1, mid=1, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        atom = Atom("A")
        prev_main = LabelledLasso(back=(frozenset(),), mid=(frozenset({atom}),), fwd=(frozenset(),))
        new_main = LabelledLasso(back=(frozenset(),), mid=(frozenset(),), fwd=(frozenset(),))
        prev_family = WitnessFamily(bx={}, lassos=(prev_main,))
        new_family = WitnessFamily(bx={}, lassos=(new_main,))

        prev_model = Mock(name="prev_z3_model")
        prev_structure = SimpleNamespace(certificate=prev_family, target_time=0)
        iterator.model_structures = [prev_structure]
        iterator.found_models = [prev_model]
        new_structure = SimpleNamespace(certificate=new_family, target_time=0)

        result = iterator._check_model_isomorphism(new_structure, Mock())
        assert result == (False, None)

    def test_new_structure_with_no_certificate_returns_false_none_without_raising(self):
        semantics = BimodalSemantics(_settings())
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        family, target_time = self._nontrivial_family_and_target()
        prev_structure = SimpleNamespace(certificate=family, target_time=target_time)
        iterator.model_structures = [prev_structure]
        iterator.found_models = [Mock()]

        new_structure = SimpleNamespace(certificate=None, target_time=None)
        result = iterator._check_model_isomorphism(new_structure, Mock())
        assert result == (False, None)

    def test_a_previous_structure_with_no_certificate_is_skipped_not_matched(self):
        semantics = BimodalSemantics(_settings())
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        family, target_time = self._nontrivial_family_and_target()

        prev_structure = SimpleNamespace(certificate=None, target_time=None)
        iterator.model_structures = [prev_structure]
        iterator.found_models = [Mock()]
        new_structure = SimpleNamespace(certificate=family, target_time=target_time)

        result = iterator._check_model_isomorphism(new_structure, Mock())
        assert result == (False, None)

    def test_returned_model_is_the_one_at_the_matching_index_zip_pairing_convention(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        atom = Atom("A")
        distinct_main = LabelledLasso(back=(frozenset({atom}),), mid=(), fwd=(frozenset(),))
        distinct_family = WitnessFamily(bx={}, lassos=(distinct_main,))
        matching_main = LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset(),))
        matching_family = WitnessFamily(bx={}, lassos=(matching_main,))

        model_for_distinct = Mock(name="model_0")
        model_for_matching = Mock(name="model_1")
        iterator.model_structures = [
            SimpleNamespace(certificate=distinct_family, target_time=0),
            SimpleNamespace(certificate=matching_family, target_time=0),
        ]
        iterator.found_models = [model_for_distinct, model_for_matching]

        new_structure = SimpleNamespace(certificate=matching_family, target_time=0)
        result = iterator._check_model_isomorphism(new_structure, Mock())
        assert result == (True, model_for_matching)


class TestCalculateDifferences:
    def _certificate(self, atom_in_main):
        main_label = frozenset({atom_in_main}) if atom_in_main else frozenset()
        main = LabelledLasso(back=(frozenset(),), mid=(), fwd=(main_label,))
        return WitnessFamily(bx={}, lassos=(main,))

    def test_label_difference_is_detected_between_two_structures(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))

        atom = Atom("A")
        new_structure = SimpleNamespace(
            certificate=self._certificate(atom), target_time=0, semantics=semantics
        )
        previous_structure = SimpleNamespace(
            certificate=self._certificate(None), target_time=0, semantics=semantics
        )

        differences = iterator._calculate_differences(new_structure, previous_structure)
        assert differences["labels"]
        assert 0 in differences["labels"]

    def test_no_certificate_on_either_side_yields_empty_differences(self):
        semantics = BimodalSemantics(_settings())
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        new_structure = SimpleNamespace(certificate=None, target_time=None, semantics=semantics)
        previous_structure = SimpleNamespace(certificate=None, target_time=None, semantics=semantics)
        differences = iterator._calculate_differences(new_structure, previous_structure)
        assert differences["labels"] == {}
        assert differences["box_guesses"] == {}

    def test_display_model_differences_prints_user_notation_diffs(self, capsys):
        """Golden shape (`docs/ITERATE.md`, "Displayed Differences"): one `+`/`-` line per
        changed label bit, rendered by `semantic/render.py` in user notation (never a
        dataclass repr), and box-guess changes as `□A: False -> True`."""
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        a = Atom("A")
        box_a = Box(a)
        previous = WitnessFamily(
            bx={a: False},
            lassos=(
                LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset({a}),)),
                LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset({a}),)),
            ),
        )
        new = WitnessFamily(
            bx={a: True},
            lassos=(
                LabelledLasso(back=(frozenset({box_a}),), mid=(), fwd=(frozenset({a}),)),
                LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset(),)),
            ),
        )
        new_structure = SimpleNamespace(certificate=new, target_time=0, semantics=semantics)
        previous_structure = SimpleNamespace(certificate=previous, target_time=0, semantics=semantics)
        new_structure.model_differences = iterator._calculate_differences(
            new_structure, previous_structure
        )

        iterator.display_model_differences(new_structure, output=__import__("sys").stdout)
        out = capsys.readouterr().out
        assert "=== DIFFERENCES FROM PREVIOUS MODEL ===" in out
        assert "Label Changes:" in out
        assert "  L0, position -1: + □A" in out
        assert "  L1, position 0: - A" in out
        assert "Box Guess Changes:" in out
        assert "  □A: False -> True" in out
        assert "Target Time:" not in out
        assert "Atom(" not in out and "Imp(" not in out and "Box(" not in out
        assert "\033[" not in out  # capsys is not a TTY

    def test_display_model_differences_uses_the_users_own_notation_when_a_syntax_exists(self, capsys):
        from model_checker.syntactic import Syntax
        from model_checker.theory_lib.bimodal.operators import bimodal_operators
        from model_checker.theory_lib.bimodal.semantic.formula import translate

        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        syntax = Syntax(["\\Diamond A"], [], bimodal_operators)
        diamond_a = translate(syntax.premises[0])
        previous = WitnessFamily(
            bx={}, lassos=(LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset(),)),)
        )
        new = WitnessFamily(
            bx={}, lassos=(LabelledLasso(back=(frozenset({diamond_a}),), mid=(), fwd=(frozenset(),)),)
        )
        new_structure = SimpleNamespace(certificate=new, target_time=0, semantics=semantics, syntax=syntax)
        previous_structure = SimpleNamespace(certificate=previous, target_time=0, semantics=semantics)
        new_structure.model_differences = iterator._calculate_differences(new_structure, previous_structure)

        iterator.display_model_differences(new_structure, output=__import__("sys").stdout)
        out = capsys.readouterr().out
        assert "  L0, position -1: + \\Diamond A" in out

    def test_display_model_differences_reports_lasso_count_and_target_time_changes(self, capsys):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        one = LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset(),))
        previous = WitnessFamily(bx={}, lassos=(one,))
        new = WitnessFamily(bx={}, lassos=(one, one))
        new_structure = SimpleNamespace(certificate=new, target_time=1, semantics=semantics)
        previous_structure = SimpleNamespace(certificate=previous, target_time=0, semantics=semantics)
        new_structure.model_differences = iterator._calculate_differences(new_structure, previous_structure)

        iterator.display_model_differences(new_structure, output=__import__("sys").stdout)
        out = capsys.readouterr().out
        assert "  + L1 added" in out
        assert "Target Time: 0 -> 1" in out


class TestStructurePrintsItsOwnDifferences:
    """`builder/runner.py` calls `structure.print_model_differences()` on the live path, so
    the structure itself must print the bimodal shape (not the framework's generic block)."""

    def test_print_model_differences_on_a_built_structure(self, capsys):
        from model_checker.theory_lib.bimodal.tests._build_support import _build

        structure = _build(["\\Box A"], ["B"], back=1, mid=0, fwd=1, verify="off")
        a = Atom("A")
        structure.model_differences = {
            "structural_metrics": {"worlds": 0},  # generic key the shared iterator merges in
            "labels": {0: {-1: {"added": frozenset({Box(a)}), "removed": frozenset({a})}}},
            "box_guesses": {a: {"old": False, "new": True}},
            "target_time": None,
        }
        structure.print_model_differences(output=__import__("sys").stdout)
        out = capsys.readouterr().out
        assert "  L0, position -1: + \\Box A" in out  # the user's own notation
        assert "  L0, position -1: - A" in out
        assert "  \\Box A: False -> True" in out
        assert "Structural Properties" not in out
        assert "Atom(" not in out

    def test_print_model_differences_is_silent_without_differences(self, capsys):
        from model_checker.theory_lib.bimodal.tests._build_support import _build

        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1, verify="off")
        structure.print_model_differences(output=__import__("sys").stdout)
        assert capsys.readouterr().out == ""


class TestIterateExampleFunction:
    def test_iterate_example_function(self):
        semantics = BimodalSemantics(_settings())
        mock_example = _mock_build_example(semantics)

        with patch.object(BimodalModelIterator, 'iterate', return_value=[mock_example.model_structure]):
            result = iterate_example(mock_example, max_iterations=1)
            assert isinstance(result, list)
            assert len(result) >= 1


def _real_build_example(premises, conclusions, settings, iterate_count):
    """A real, non-mocked `BuildExample` -- no Mock stands in for the solver, the model,
    or the semantics -- matching the construction pattern already used by the other three
    theories' own `test_iterate.py` (`BuildExample(mock_module, semantic_theory,
    example_case)`; only the surrounding `BuildModule` is a Mock, never the model-checking
    path itself)."""
    theory = get_theory()
    general_settings = dict(settings)
    general_settings['iterate'] = iterate_count
    mock_module = Mock()
    mock_module.semantic_theories = {"bimodal": theory}
    mock_module.general_settings = general_settings
    mock_module.raw_general_settings = general_settings
    mock_module.module_flags = SimpleNamespace(
        contingent=False, disjoint=False, non_empty=False, non_null=False,
        print_constraints=False, save_output=False, print_impossible=False,
        print_z3=False, maximize=False,
    )
    example_case = [premises, conclusions, general_settings]
    return BuildExample(mock_module, theory, example_case)


class TestLiveIteration:
    """Live, non-mocked end-to-end `iterate: 3` coverage against a real
    `BuildExample`/`BimodalModelIterator` pair. Deliberately not mocked at any point
    on the model-building path: this is exactly the path that used to crash outright
    with `AttributeError: 'BimodalSemantics' object has no attribute 'is_world'`
    (surfaced as `ModelExtractionError`) before the three shared-iterator extension
    points existed.

    This class also covers orbit-level distinctness, not just bit-level
    distinctness: two yielded certificates that are rotations or witness-
    permutations of each other are no longer treated as genuinely different models
    (`_check_model_isomorphism`'s real orbit-key detector), and the search's
    exclusion clause (`_create_non_isomorphic_constraint`) actually rules out the
    whole orbit, not just the one exact bit pattern, so the live loop keeps making
    progress rather than cycling through orbit members one bit-flip at a time. A
    dedicated rotation-validity measurement for `BM_CM_1` (recorded in this task's
    plan) answered "yes" to "is a live rotation/permutation duplicate reachable", so
    `test_a_live_run_detects_a_genuine_rotation_permutation_duplicate` below
    exercises that empirically, not via a semi-synthetic fallback.
    """

    def test_iterate_three_yields_three_pairwise_distinct_certificates(self):
        """(a) no exception raised getting here at all; (b) at least one further,
        genuinely new (non-isomorphic-as-orbit) certificate is found beyond the
        first; (c) every yielded certificate is non-`None`; (d) every pair of
        yielded certificates is pairwise distinct *as orbits*
        (`symmetry.certificate_orbit_key`), the semantically meaningful notion of
        distinctness this plan introduces -- not merely differing in some raw
        `_bits`/`_guesses` variable, which two orbit-equivalent (rotated/permuted)
        certificates can still do.

        Not asserting *exactly* `2` further models (`iterate: 3` in full): with the
        search solver now correctly coherence-constrained (a pre-existing bug fixed
        while building this plan's orbit exclusion --
        `_ensure_frame_constraints_in_search_solver`'s docstring), a *third*
        pairwise-distinct-as-orbit certificate for this small example is not always
        reachable within a bounded real-Z3 search time -- an intentional,
        documented consequence of quotienting by the rotation/permutation group
        (the plan's own Risk table: "a lower count is the expected, intended effect
        of quotienting"). `max_time` is still raised from `BM_CM_1_settings`' own
        `10` (test-local only, not a change to that shared constant) to give the
        search a fair chance at finding more than the guaranteed first extra model.
        """
        settings = dict(BM_CM_1_settings)
        settings["max_time"] = 30
        example = _real_build_example(
            BM_CM_1_premises, BM_CM_1_conclusions, settings, iterate_count=3
        )
        iterator = BimodalModelIterator(example)

        structures = list(iterator.iterate_generator())

        assert len(structures) >= 1, "expected at least one further certificate beyond the first"
        assert len(iterator.model_structures) == len(structures) + 1

        all_structures = [example.model_structure] + structures
        for structure in all_structures:
            assert structure.certificate is not None

        keys = [
            symmetry.certificate_orbit_key(structure.certificate, structure.target_time)
            for structure in all_structures
        ]
        for i in range(len(keys)):
            for j in range(i + 1, len(keys)):
                assert keys[i] != keys[j], (
                    f"structures {i} and {j} are the same certificate up to "
                    "rotation/permutation (equal orbit keys)"
                )

    def test_exclusion_constraint_for_model_two_is_enforced_not_coincidental(self):
        """Prove enforcement, not luck: the exclusion constraint list handed to the
        solver for model 2 must be non-empty, and it must evaluate to `False` under
        model 1's own assignment -- i.e. the blocking clause genuinely excludes the
        certificate the search already found, rather than model 2 merely happening to
        differ."""
        example = _real_build_example(
            BM_CM_1_premises, BM_CM_1_conclusions, BM_CM_1_settings, iterate_count=3
        )
        iterator = BimodalModelIterator(example)
        model_one = example.model_structure.z3_model

        exclusion_constraints = iterator._build_exclusion_constraints([model_one])

        assert len(exclusion_constraints) == 1
        result = model_one.eval(exclusion_constraints[0], model_completion=True)
        assert not is_true(result), (
            "the exclusion constraint for model 2 must be FALSE under model 1's own "
            "assignment -- otherwise it excludes nothing"
        )

    def test_iterate_beyond_the_admitted_certificate_space_exhausts_cleanly(self):
        """When `iterate:` asks for more certificates than the settings admit, the
        live loop must terminate with a clean "solver returned unsat" exhaustion
        message rather than hanging or looping forever on isomorphic skips -- with
        the orbit-key detector/excluder now live (`back=nf=1` here makes the
        rotation/permutation group trivial -- `(1*1)**L * factorial(L-1) == 1` -- so
        this specific example still exercises exact-bit exclusion only; the group is
        nontrivial for `BM_CM_1`'s `back=2, mid=1, fwd=2`, covered by
        `test_a_live_run_detects_a_genuine_rotation_permutation_duplicate` below)."""
        settings = _settings(back=1, mid=0, fwd=1, iterate=20, max_time=5)
        example = _real_build_example(["A"], ["B"], settings, iterate_count=20)
        iterator = BimodalModelIterator(example)

        structures = list(iterator.iterate_generator())

        assert len(structures) < 19  # fewer than the 20 requested -- the space ran out
        assert len(iterator.model_structures) == len(structures) + 1
        assert any(
            "solver returned unsat" in message for message in iterator.debug_messages
        )

    def test_the_detector_covers_the_whole_orbit_of_a_solver_produced_certificate(self):
        """The orbit-key detector fires on every rotation/permutation image of a
        certificate the solver genuinely produced -- not a hand-built one. The
        certificate comes from `BM_CM_1`'s own live, non-mocked first solve; only the
        group action applied to it is synthetic, which is precisely the mathematical
        content under test.

        HISTORY -- why this is not the `isomorphic_model_count >= 1` assertion it
        replaces. The earlier form drove a live `iterate: 15` run and asserted the
        counter had advanced, on the stated premise that a run asking for models until
        the reachable orbits run out "does, empirically, always hit at least one genuine
        duplicate along the way". That premise is false, and the assertion was a
        release-gating flake: it failed on CI's Python 3.11 leg while 3.10 and 3.12
        passed on the same commit, and reproduced locally at 2 failures in 15 runs of the
        same interpreter. A `PYTHONHASHSEED` sweep isolated the mechanism and showed it
        is not a budget overrun (8.6) and not repairable by a longer drive:

        - The search order depends on hash ordering, so the whole run is
          seed-determined: `iterate: 15` yields `isomorphic_model_count == 0` for seeds
          7, 8, 11, 12, 13 and 25, and a nonzero count for the rest.
        - Zero duplicates is the *lucky* path, not a degenerate one. Those zero-count
          seeds are exactly the runs that cleanly fill the whole request (14 new
          structures); the seeds with large counts are runs that churn on duplicates and
          return far fewer models (e.g. 149 duplicates, 1 model). Encountering a
          duplicate is therefore evidence of the search struggling -- nothing the
          detector's correctness entitles the test to demand.
        - Raising the drive does not close it. At `iterate: 30`, seed 48 still yields
          `isomorphic_model_count == 0` (1 of 30 seeds swept), while the seeds that churn
          push the run into its 30s `max_time` -- strictly worse on both axes.

        What this asserts instead holds for *every* solve, however the draw falls: each
        image of the first solve's certificate under the symmetry group must be reported
        as a duplicate of it, and a certificate outside that orbit must not be. Whether
        the group actually *moves* this particular certificate is itself solve-dependent
        and deliberately not asserted -- measured both ways on the same commit (an orbit
        of 2 distinct certificates from a fresh process, a rotation fixed point when the
        preceding tests in this module have run first), which is exactly the kind of
        incidental property the replaced assertion mistook for a guarantee. The negative
        control below is what keeps the positive half honest when the orbit is a single
        point: it fails if the detector degenerates into a constant `True`. Deterministic
        coverage of a rotation that provably moves its certificate is
        `TestCheckModelIsomorphism::test_a_rotation_of_a_previous_certificate_is_detected`
        (hand-built precisely so the group action is guaranteed nontrivial), and live
        end-to-end coverage of the detector on the real iteration path stays with
        `test_live_iterate_yields_pairwise_orbit_distinct_certificates` and
        `test_iterate_beyond_the_admitted_certificate_space_exhausts_cleanly` -- none of
        which depends on which way a search draw happened to fall.
        """
        settings = dict(BM_CM_1_settings)
        settings["max_time"] = 30
        example = _real_build_example(
            BM_CM_1_premises, BM_CM_1_conclusions, settings, iterate_count=2
        )
        iterator = BimodalModelIterator(example)

        first_structure = example.model_structure
        certificate_family = first_structure.certificate
        assert isinstance(certificate_family, WitnessFamily)
        target_time = first_structure.target_time

        iterator.model_structures = [first_structure]
        iterator.found_models = [first_structure.z3_model]

        group = list(
            symmetry.enumerate_group(
                settings["back"], settings["fwd"], len(certificate_family.lassos)
            )
        )
        images = [
            symmetry.apply(element, certificate_family, target_time) for element in group
        ]
        assert len(images) == len(group) > 1

        for rotated_family, rotated_target_time in images:
            rotated_structure = SimpleNamespace(
                certificate=rotated_family, target_time=rotated_target_time
            )

            is_isomorphic, matched_model = iterator._check_model_isomorphism(
                rotated_structure, Mock(name="rotated_z3_model")
            )

            assert is_isomorphic, (
                "an image of the first certificate under the symmetry group must be "
                "detected as a duplicate of it"
            )
            assert matched_model is first_structure.z3_model

        # Negative control: a certificate carrying one more witness lasso than the found
        # one cannot be any group image of it -- `certificate_orbit_key`'s witness tuple
        # is a different length, and no rotation or witness permutation changes a
        # family's lasso count. A detector that answered `True` unconditionally, or that
        # compared nothing at all, would fail here.
        out_of_orbit = SimpleNamespace(
            certificate=WitnessFamily(
                bx=dict(certificate_family.bx),
                lassos=certificate_family.lassos + (certificate_family.lassos[0],),
            ),
            target_time=target_time,
        )

        assert iterator._check_model_isomorphism(
            out_of_orbit, Mock(name="out_of_orbit_z3_model")
        ) == (False, None)


class TestAllConstraintsReflectsCertificateAfterSolve:
    """Regression coverage for the stale `ModelConstraints.all_constraints` snapshot
    (`models/constraints.py`): bimodal's encoding is deliberately two-phase (decision D6)
    -- `frame_constraints` starts empty and is populated later by
    `BimodalSemantics.finalize_certificate()`, once every boxed subformula is known. A
    plain eager-concatenation `all_constraints`, computed once in `ModelConstraints.__init__`
    before `finalize_certificate()` ever runs, permanently omits the entire (C1)-(C4)
    certificate encoding -- for every real solve, not only iterated ones (this class uses
    `iterate_count=1`, i.e. no iteration at all, to isolate that). `full_constraints()`
    (`tests/_pinned_eval.py`) re-concatenates the four live component lists post-solve and
    is the ground truth for what Z3 actually solved; `all_constraints` must match it once
    the property fix lands."""

    def test_all_constraints_contains_certificate_encoding_after_solve(self):
        example = _real_build_example(
            BM_CM_1_premises, BM_CM_1_conclusions, BM_CM_1_settings, iterate_count=1
        )
        structure = example.model_structure

        true_constraints = full_constraints(structure)
        snapshot_constraints = structure.model_constraints.all_constraints

        assert len(snapshot_constraints) == len(true_constraints), (
            f"all_constraints ({len(snapshot_constraints)}) must match the true post-solve "
            f"constraint set ({len(true_constraints)}) -- a stale snapshot omits the "
            "certificate encoding installed by finalize_certificate() after construction"
        )
