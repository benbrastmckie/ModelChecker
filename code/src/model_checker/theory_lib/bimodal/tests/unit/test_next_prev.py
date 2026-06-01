"""Tests for DefNextOperator and DefPrevOperator in BimodalSemantics.

These are defined temporal operators:
- Next(phi) = U(phi, bot): phi holds at the immediately next time (first future time
  with no guard condition in between, since bot is never true)
- Prev(phi) = S(phi, bot): phi held at the immediately previous time (first past time
  with no guard condition in between)

Following the TDD pattern established in test_until_since.py.
"""

import pytest

from model_checker import (
    ModelConstraints,
    Syntax,
    run_test,
)
from model_checker.theory_lib.bimodal import (
    BimodalStructure,
    BimodalProposition,
    BimodalSemantics,
    bimodal_operators,
)
from model_checker.theory_lib.bimodal.operators import (
    DefNextOperator,
    DefPrevOperator,
    UntilOperator,
    SinceOperator,
    BotOperator,
)
from model_checker.utils.context import isolated_z3_context
import model_checker.syntactic as syntactic


# ---------------------------------------------------------------------------
# Signature tests
# ---------------------------------------------------------------------------

class TestDefNextOperatorSignature:
    """Tests for DefNextOperator basic structure and interface."""

    def test_next_operator_exists(self):
        """Test that DefNextOperator class exists and is importable."""
        assert DefNextOperator is not None
        assert hasattr(DefNextOperator, 'name')
        assert hasattr(DefNextOperator, 'arity')

    def test_next_operator_arity(self):
        """Test that DefNextOperator has arity 1 (unary operator)."""
        assert DefNextOperator.arity == 1

    def test_next_operator_name(self):
        """Test that DefNextOperator has correct name."""
        assert DefNextOperator.name == "\\next"

    def test_next_is_defined_operator_subclass(self):
        """Test that DefNextOperator is a subclass of DefinedOperator."""
        assert issubclass(DefNextOperator, syntactic.DefinedOperator)

    def test_next_has_derived_definition(self):
        """Test that DefNextOperator has derived_definition method."""
        assert hasattr(DefNextOperator, 'derived_definition')
        assert callable(DefNextOperator.derived_definition)

    def test_next_has_print_method(self):
        """Test that DefNextOperator has print_method."""
        assert hasattr(DefNextOperator, 'print_method')
        assert callable(DefNextOperator.print_method)

    def test_next_not_primitive(self):
        """Test that DefNextOperator is not primitive (it is defined)."""
        assert DefNextOperator.primitive is False


class TestDefPrevOperatorSignature:
    """Tests for DefPrevOperator basic structure and interface."""

    def test_prev_operator_exists(self):
        """Test that DefPrevOperator class exists and is importable."""
        assert DefPrevOperator is not None
        assert hasattr(DefPrevOperator, 'name')
        assert hasattr(DefPrevOperator, 'arity')

    def test_prev_operator_arity(self):
        """Test that DefPrevOperator has arity 1 (unary operator)."""
        assert DefPrevOperator.arity == 1

    def test_prev_operator_name(self):
        """Test that DefPrevOperator has correct name."""
        assert DefPrevOperator.name == "\\prev"

    def test_prev_is_defined_operator_subclass(self):
        """Test that DefPrevOperator is a subclass of DefinedOperator."""
        assert issubclass(DefPrevOperator, syntactic.DefinedOperator)

    def test_prev_has_derived_definition(self):
        """Test that DefPrevOperator has derived_definition method."""
        assert hasattr(DefPrevOperator, 'derived_definition')
        assert callable(DefPrevOperator.derived_definition)

    def test_prev_has_print_method(self):
        """Test that DefPrevOperator has print_method."""
        assert hasattr(DefPrevOperator, 'print_method')
        assert callable(DefPrevOperator.print_method)

    def test_prev_not_primitive(self):
        """Test that DefPrevOperator is not primitive (it is defined)."""
        assert DefPrevOperator.primitive is False


# ---------------------------------------------------------------------------
# Derived definition structure tests
# ---------------------------------------------------------------------------

class TestDefNextDefinition:
    """Tests for DefNextOperator.derived_definition structure."""

    def test_next_derived_definition_returns_list(self):
        """Test that derived_definition returns a list."""
        semantics_settings = {
            'N': 3, 'M': 2, 'contingent': False, 'disjoint': False,
            'max_time': 1, 'expectation': True, 'iterate': 1
        }
        sem = BimodalSemantics(semantics_settings)
        op = DefNextOperator(sem)
        argument = ['A']
        result = op.derived_definition(argument)
        assert isinstance(result, list), "derived_definition should return a list"

    def test_next_derived_definition_uses_until_operator(self):
        """Test that Next is defined using UntilOperator as the outer operator."""
        semantics_settings = {
            'N': 3, 'M': 2, 'contingent': False, 'disjoint': False,
            'max_time': 1, 'expectation': True, 'iterate': 1
        }
        sem = BimodalSemantics(semantics_settings)
        op = DefNextOperator(sem)
        argument = ['A']
        result = op.derived_definition(argument)
        assert result[0] is UntilOperator, \
            "Next definition should use UntilOperator as the outer operator"

    def test_next_derived_definition_argument_is_event(self):
        """Test that the argument appears as the event (first arg) of Until."""
        semantics_settings = {
            'N': 3, 'M': 2, 'contingent': False, 'disjoint': False,
            'max_time': 1, 'expectation': True, 'iterate': 1
        }
        sem = BimodalSemantics(semantics_settings)
        op = DefNextOperator(sem)
        argument = ['A']
        result = op.derived_definition(argument)
        assert result[1] == argument, \
            "Argument should appear as the event (first arg) of Until"

    def test_next_derived_definition_guard_is_bot(self):
        """Test that the guard argument of Until is [BotOperator]."""
        semantics_settings = {
            'N': 3, 'M': 2, 'contingent': False, 'disjoint': False,
            'max_time': 1, 'expectation': True, 'iterate': 1
        }
        sem = BimodalSemantics(semantics_settings)
        op = DefNextOperator(sem)
        argument = ['A']
        result = op.derived_definition(argument)
        assert result[2] == [BotOperator], \
            "Guard should be [BotOperator] (bot operator wrapped in list)"

    def test_next_derived_definition_full_structure(self):
        """Test the complete structure: [UntilOperator, argument, [BotOperator]]."""
        semantics_settings = {
            'N': 3, 'M': 2, 'contingent': False, 'disjoint': False,
            'max_time': 1, 'expectation': True, 'iterate': 1
        }
        sem = BimodalSemantics(semantics_settings)
        op = DefNextOperator(sem)
        argument = ['A']
        result = op.derived_definition(argument)
        assert len(result) == 3, "derived_definition should return a 3-element list"
        assert result[0] is UntilOperator
        assert result[1] == argument
        assert result[2] == [BotOperator]


class TestDefPrevDefinition:
    """Tests for DefPrevOperator.derived_definition structure."""

    def test_prev_derived_definition_returns_list(self):
        """Test that derived_definition returns a list."""
        semantics_settings = {
            'N': 3, 'M': 2, 'contingent': False, 'disjoint': False,
            'max_time': 1, 'expectation': True, 'iterate': 1
        }
        sem = BimodalSemantics(semantics_settings)
        op = DefPrevOperator(sem)
        argument = ['A']
        result = op.derived_definition(argument)
        assert isinstance(result, list), "derived_definition should return a list"

    def test_prev_derived_definition_uses_since_operator(self):
        """Test that Prev is defined using SinceOperator as the outer operator."""
        semantics_settings = {
            'N': 3, 'M': 2, 'contingent': False, 'disjoint': False,
            'max_time': 1, 'expectation': True, 'iterate': 1
        }
        sem = BimodalSemantics(semantics_settings)
        op = DefPrevOperator(sem)
        argument = ['A']
        result = op.derived_definition(argument)
        assert result[0] is SinceOperator, \
            "Prev definition should use SinceOperator as the outer operator"

    def test_prev_derived_definition_argument_is_event(self):
        """Test that the argument appears as the event (first arg) of Since."""
        semantics_settings = {
            'N': 3, 'M': 2, 'contingent': False, 'disjoint': False,
            'max_time': 1, 'expectation': True, 'iterate': 1
        }
        sem = BimodalSemantics(semantics_settings)
        op = DefPrevOperator(sem)
        argument = ['A']
        result = op.derived_definition(argument)
        assert result[1] == argument, \
            "Argument should appear as the event (first arg) of Since"

    def test_prev_derived_definition_guard_is_bot(self):
        """Test that the guard argument of Since is [BotOperator]."""
        semantics_settings = {
            'N': 3, 'M': 2, 'contingent': False, 'disjoint': False,
            'max_time': 1, 'expectation': True, 'iterate': 1
        }
        sem = BimodalSemantics(semantics_settings)
        op = DefPrevOperator(sem)
        argument = ['A']
        result = op.derived_definition(argument)
        assert result[2] == [BotOperator], \
            "Guard should be [BotOperator] (bot operator wrapped in list)"

    def test_prev_derived_definition_full_structure(self):
        """Test the complete structure: [SinceOperator, argument, [BotOperator]]."""
        semantics_settings = {
            'N': 3, 'M': 2, 'contingent': False, 'disjoint': False,
            'max_time': 1, 'expectation': True, 'iterate': 1
        }
        sem = BimodalSemantics(semantics_settings)
        op = DefPrevOperator(sem)
        argument = ['A']
        result = op.derived_definition(argument)
        assert len(result) == 3, "derived_definition should return a 3-element list"
        assert result[0] is SinceOperator
        assert result[1] == argument
        assert result[2] == [BotOperator]


# ---------------------------------------------------------------------------
# Registration tests
# ---------------------------------------------------------------------------

class TestOperatorRegistration:
    """Tests that DefNextOperator and DefPrevOperator are registered in bimodal_operators."""

    def test_next_in_bimodal_operators(self):
        """Test that DefNextOperator is registered in bimodal_operators."""
        operator_names = bimodal_operators.operator_dictionary.keys()
        assert "\\next" in operator_names, \
            "DefNextOperator should be registered with name '\\\\next' in bimodal_operators"

    def test_prev_in_bimodal_operators(self):
        """Test that DefPrevOperator is registered in bimodal_operators."""
        operator_names = bimodal_operators.operator_dictionary.keys()
        assert "\\prev" in operator_names, \
            "DefPrevOperator should be registered with name '\\\\prev' in bimodal_operators"

    def test_next_resolves_to_correct_class(self):
        """Test that '\\next' resolves to DefNextOperator."""
        op_class = bimodal_operators.operator_dictionary["\\next"]
        assert op_class is DefNextOperator, \
            "'\\\\next' should resolve to DefNextOperator class"

    def test_prev_resolves_to_correct_class(self):
        """Test that '\\prev' resolves to DefPrevOperator."""
        op_class = bimodal_operators.operator_dictionary["\\prev"]
        assert op_class is DefPrevOperator, \
            "'\\\\prev' should resolve to DefPrevOperator class"


# ---------------------------------------------------------------------------
# Prefix construction tests
# ---------------------------------------------------------------------------

class TestPrefixConstruction:
    """Tests that the parser can construct prefix formulas using \\next and \\prev."""

    def test_next_syntax_parses(self):
        """Test that Syntax can parse a formula with \\next."""
        syntax = Syntax(["\\next A"], [], bimodal_operators)
        assert syntax is not None

    def test_prev_syntax_parses(self):
        """Test that Syntax can parse a formula with \\prev."""
        syntax = Syntax(["\\prev A"], [], bimodal_operators)
        assert syntax is not None

    def test_next_in_compound_formula(self):
        """Test \\next in a compound formula with implication."""
        syntax = Syntax(["(\\next A \\rightarrow \\next B)"], [], bimodal_operators)
        assert syntax is not None

    def test_prev_in_compound_formula(self):
        """Test \\prev in a compound formula with implication."""
        syntax = Syntax(["(\\prev A \\rightarrow \\prev B)"], [], bimodal_operators)
        assert syntax is not None


# ---------------------------------------------------------------------------
# Semantic equivalence tests via run_test
# ---------------------------------------------------------------------------

def make_next_equiv_example():
    """Create example: \\next A <-> (A \\Until \\bot) should be a theorem."""
    premises = []
    conclusions = ['(\\next A \\leftrightarrow (A \\Until \\bot))']
    settings = {
        'N': 2,
        'M': 2,
        'contingent': False,
        'disjoint': False,
        'max_time': 5,
        'expectation': False,
    }
    return [premises, conclusions, settings]


def make_prev_equiv_example():
    """Create example: \\prev A <-> (A \\Since \\bot) should be a theorem."""
    premises = []
    conclusions = ['(\\prev A \\leftrightarrow (A \\Since \\bot))']
    settings = {
        'N': 2,
        'M': 2,
        'contingent': False,
        'disjoint': False,
        'max_time': 5,
        'expectation': False,
    }
    return [premises, conclusions, settings]


class TestSemanticEquivalence:
    """Tests that Next(A) <-> U(A, bot) and Prev(A) <-> S(A, bot) are theorems."""

    def test_next_equivalent_to_until_bot(self):
        """Test that \\next A is semantically equivalent to (A \\Until \\bot)."""
        example = make_next_equiv_example()
        with isolated_z3_context():
            result = run_test(
                example,
                BimodalSemantics,
                BimodalProposition,
                bimodal_operators,
                Syntax,
                ModelConstraints,
                BimodalStructure,
            )
        assert result, "\\next A <-> (A \\Until \\bot) should be a theorem (no countermodel)"

    def test_prev_equivalent_to_since_bot(self):
        """Test that \\prev A is semantically equivalent to (A \\Since \\bot)."""
        example = make_prev_equiv_example()
        with isolated_z3_context():
            result = run_test(
                example,
                BimodalSemantics,
                BimodalProposition,
                bimodal_operators,
                Syntax,
                ModelConstraints,
                BimodalStructure,
            )
        assert result, "\\prev A <-> (A \\Since \\bot) should be a theorem (no countermodel)"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
