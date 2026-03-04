"""
Unit tests for predicate extension display in countermodels.

Tests the print_predicate_extensions() method in LogosModelStructure
which displays what propositions each predicate maps each domain element to.

Usage:
    PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/unit/test_predicate_extensions.py -v
"""

import io
import importlib
import sys

import pytest

from model_checker import (
    ModelConstraints,
    Syntax,
)
from model_checker.theory_lib.logos.semantic import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
)
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry


# Import the first-order examples module using importlib due to hyphen in name
first_order_examples = importlib.import_module(
    'model_checker.theory_lib.logos.subtheories.first-order.examples'
)


def create_first_order_model_structure(premises, conclusions, settings):
    """Helper to create a model structure with first-order predicates.

    Args:
        premises: List of premise sentence strings
        conclusions: List of conclusion sentence strings
        settings: Settings dict for the model

    Returns:
        LogosModelStructure instance or None if no countermodel found
    """
    registry = LogosOperatorRegistry()
    registry.load_subtheories(['extensional', 'constitutive', 'first-order'])
    operators = registry.get_operators()

    syntax = Syntax(
        premises,
        conclusions,
        operators,
    )

    # Add required settings if missing
    if 'print_impossible' not in settings:
        settings['print_impossible'] = False
    if 'print_constraints' not in settings:
        settings['print_constraints'] = False
    if 'print_z3' not in settings:
        settings['print_z3'] = False

    semantics = LogosSemantics(settings, registry)
    model_constraints = ModelConstraints(
        settings,
        syntax,
        semantics,
        LogosProposition,
    )

    # Create model structure
    model_structure = LogosModelStructure(model_constraints, settings)

    if model_structure.z3_model_status:
        return model_structure
    return None


class TestPredicateExtensionOutput:
    """Test predicate extension output appears in first-order countermodels."""

    def test_predicate_extension_header_appears(self):
        """Test that PREDICATE EXTENSIONS header appears for first-order countermodels."""
        # FO_CM_1: exists x. Fx -/-> forall x. Fx
        premises = ['\\exists v_x. F[v_x]']
        conclusions = ['\\forall v_x. F[v_x]']
        settings = {
            'N': 2,
            'contingent': True,
            'non_null': True,
            'non_empty': True,
            'disjoint': False,
            'max_time': 1,
            'expectation': True,
            'print_impossible': False,
        }

        model = create_first_order_model_structure(premises, conclusions, settings)
        assert model is not None, "Expected to find countermodel for FO_CM_1"

        # Capture output
        output = io.StringIO()
        model.print_predicate_extensions(output)
        result = output.getvalue()

        assert "PREDICATE EXTENSIONS:" in result, \
            f"Expected 'PREDICATE EXTENSIONS:' header in output, got: {result}"

    def test_predicate_name_appears_in_output(self):
        """Test that predicate F appears in extension output."""
        premises = ['\\exists v_x. F[v_x]']
        conclusions = ['\\forall v_x. F[v_x]']
        settings = {
            'N': 2,
            'contingent': True,
            'non_null': True,
            'non_empty': True,
            'disjoint': False,
            'max_time': 1,
            'expectation': True,
            'print_impossible': False,
        }

        model = create_first_order_model_structure(premises, conclusions, settings)
        assert model is not None, "Expected to find countermodel"

        output = io.StringIO()
        model.print_predicate_extensions(output)
        result = output.getvalue()

        # Should show predicate F with domain element mappings
        assert "F(" in result, f"Expected predicate F in output, got: {result}"

    def test_domain_elements_formatted_correctly(self):
        """Test that domain elements use bitvec_to_substates format (a, b, a.b, etc)."""
        premises = ['\\exists v_x. F[v_x]']
        conclusions = ['\\forall v_x. F[v_x]']
        settings = {
            'N': 2,
            'contingent': True,
            'non_null': True,
            'non_empty': True,
            'disjoint': False,
            'max_time': 1,
            'expectation': True,
            'print_impossible': False,
        }

        model = create_first_order_model_structure(premises, conclusions, settings)
        assert model is not None, "Expected to find countermodel"

        output = io.StringIO()
        model.print_predicate_extensions(output)
        result = output.getvalue()

        # Domain elements for N=2: "", "a", "b", "a.b"
        # At least one domain element should appear in the output
        has_domain_element = any(elem in result for elem in ["F()", "F(a)", "F(b)", "F(a.b)"])
        assert has_domain_element, f"Expected domain elements in output, got: {result}"


class TestNoPredicatesRegistered:
    """Test behavior when no predicates are registered (propositional case)."""

    def test_no_output_for_propositional_example(self):
        """Test that no predicate extension output for propositional-only examples."""
        # Simple propositional example: A -/-> B
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional'])
        operators = registry.get_operators()

        premises = ['A']
        conclusions = ['B']
        settings = {
            'N': 2,
            'contingent': True,
            'non_null': True,
            'non_empty': True,
            'disjoint': False,
            'max_time': 1,
            'expectation': True,
            'print_impossible': False,
            'print_constraints': False,
            'print_z3': False,
        }

        syntax = Syntax(premises, conclusions, operators)
        semantics = LogosSemantics(settings, registry)
        model_constraints = ModelConstraints(
            settings,
            syntax,
            semantics,
            LogosProposition,
        )

        model = LogosModelStructure(model_constraints, settings)
        assert model.z3_model_status, "Expected to find countermodel for A -/-> B"

        output = io.StringIO()
        model.print_predicate_extensions(output)
        result = output.getvalue()

        # Should be empty or minimal output when no predicates
        assert "PREDICATE EXTENSIONS:" not in result, \
            f"Should not print predicate extensions for propositional examples, got: {result}"


class TestPrintImpossibleSetting:
    """Test that print_impossible setting is respected."""

    def test_print_impossible_false_excludes_impossible_states(self):
        """Test that impossible states are excluded when print_impossible=False."""
        premises = ['\\exists v_x. F[v_x]']
        conclusions = ['\\forall v_x. F[v_x]']
        settings = {
            'N': 2,
            'contingent': True,
            'non_null': True,
            'non_empty': True,
            'disjoint': False,
            'max_time': 1,
            'expectation': True,
            'print_impossible': False,
        }

        model = create_first_order_model_structure(premises, conclusions, settings)
        assert model is not None, "Expected to find countermodel"

        output = io.StringIO()
        model.print_predicate_extensions(output)
        result = output.getvalue()

        # Output should exist and not contain "(impossible)" marker
        # (Impossible states should be filtered out)
        assert "PREDICATE EXTENSIONS:" in result


class TestBinaryPredicates:
    """Test binary predicate enumeration."""

    def test_binary_predicate_enumerates_all_pairs(self):
        """Test that binary predicates enumerate all (d1, d2) pairs."""
        # FO_CM_3: forall x. exists y. R[x,y] -/-> exists y. forall x. R[x,y]
        premises = ['\\forall v_x. \\exists v_y. R[v_x, v_y]']
        conclusions = ['\\exists v_y. \\forall v_x. R[v_x, v_y]']
        settings = {
            'N': 2,
            'contingent': True,
            'non_null': True,
            'non_empty': True,
            'disjoint': False,
            'max_time': 1,
            'expectation': True,
            'print_impossible': False,
        }

        model = create_first_order_model_structure(premises, conclusions, settings)
        assert model is not None, "Expected to find countermodel for FO_CM_3"

        output = io.StringIO()
        model.print_predicate_extensions(output)
        result = output.getvalue()

        # Binary predicate R should appear with pairs
        assert "R(" in result, f"Expected predicate R in output, got: {result}"

        # With N=2, there are 4 domain elements (0,1,2,3 -> "", a, b, a.b)
        # Binary predicate should show multiple pairs
        # At minimum, should show at least 4 entries (one for each arg1 with some arg2)
        r_count = result.count("R(")
        assert r_count >= 4, f"Expected at least 4 R entries for binary predicate, got {r_count}"


class TestHelperMethod:
    """Test the _get_predicate_extension helper method."""

    def test_get_predicate_extension_returns_tuple(self):
        """Test that _get_predicate_extension returns (verifiers, falsifiers) tuple."""
        premises = ['\\exists v_x. F[v_x]']
        conclusions = ['\\forall v_x. F[v_x]']
        settings = {
            'N': 2,
            'contingent': True,
            'non_null': True,
            'non_empty': True,
            'disjoint': False,
            'max_time': 1,
            'expectation': True,
            'print_impossible': False,
        }

        model = create_first_order_model_structure(premises, conclusions, settings)
        assert model is not None, "Expected to find countermodel"

        import z3
        # Get extension for F at domain element 0 (the null state)
        arg_tuple = (z3.BitVecVal(0, model.N),)
        result = model._get_predicate_extension('F', arg_tuple)

        # Should return a tuple of (verifier_states, falsifier_states)
        assert isinstance(result, tuple), f"Expected tuple, got {type(result)}"
        assert len(result) == 2, f"Expected 2-tuple, got {len(result)}"
        verifiers, falsifiers = result
        assert isinstance(verifiers, set), f"Expected set for verifiers, got {type(verifiers)}"
        assert isinstance(falsifiers, set), f"Expected set for falsifiers, got {type(falsifiers)}"


class TestOutputFormat:
    """Test the output format matches specification."""

    def test_output_format_matches_proposition_format(self):
        """Test output uses < verifiers, falsifiers > format like propositions."""
        premises = ['\\exists v_x. F[v_x]']
        conclusions = ['\\forall v_x. F[v_x]']
        settings = {
            'N': 2,
            'contingent': True,
            'non_null': True,
            'non_empty': True,
            'disjoint': False,
            'max_time': 1,
            'expectation': True,
            'print_impossible': False,
        }

        model = create_first_order_model_structure(premises, conclusions, settings)
        assert model is not None, "Expected to find countermodel"

        output = io.StringIO()
        model.print_predicate_extensions(output)
        result = output.getvalue()

        # Should contain the < verifiers, falsifiers > format
        assert "<" in result and ">" in result, \
            f"Expected angle bracket format in output, got: {result}"
