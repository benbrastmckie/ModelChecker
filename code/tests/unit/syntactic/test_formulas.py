"""Unit tests for formulas module - free variable computation and WFF checking.

Tests the compute_formula_free_variables() and is_syntactically_wff() functions
from the formulas module.
"""

import pytest
from model_checker.syntactic.formulas import (
    compute_formula_free_variables,
    is_syntactically_wff,
)
from model_checker.syntactic.terms import Variable, Constant, FunctionApplication


class TestComputeFormulaFreeVariables:
    """Tests for compute_formula_free_variables function."""

    # --- Atomic formulas ---

    def test_fv_zero_arity_predicate(self):
        """Zero-arity predicate P[] has no free variables."""
        prefix = ['P']
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset()

    def test_fv_unary_predicate_with_variable(self):
        """Predicate P[v_x] has free variable v_x."""
        v_x = Variable('v_x')
        prefix = ['P', v_x]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset({v_x})

    def test_fv_predicate_with_constant(self):
        """Predicate P[a<>] has no free variables."""
        const_a = Constant('a')
        prefix = ['P', const_a]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset()

    def test_fv_binary_predicate_with_variables(self):
        """Predicate R[v_x, v_y] has free variables {v_x, v_y}."""
        v_x = Variable('v_x')
        v_y = Variable('v_y')
        prefix = ['R', v_x, v_y]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset({v_x, v_y})

    def test_fv_predicate_with_function_application(self):
        """Predicate P[f<v_x>] has free variable v_x."""
        v_x = Variable('v_x')
        func = FunctionApplication('f', (v_x,))
        prefix = ['P', func]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset({v_x})

    # --- Extremal constants ---

    def test_fv_top(self):
        """\\top has no free variables."""
        prefix = ['\\top']
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset()

    def test_fv_bot(self):
        """\\bot has no free variables."""
        prefix = ['\\bot']
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset()

    # --- Negation ---

    def test_fv_negation(self):
        """FV(\\neg phi) = FV(phi)."""
        v_x = Variable('v_x')
        prefix = ['\\neg', ['P', v_x]]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset({v_x})

    def test_fv_negation_closed(self):
        """FV(\\neg P[]) = {}."""
        prefix = ['\\neg', ['P']]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset()

    # --- Binary connectives ---

    def test_fv_conjunction(self):
        """FV(phi \\wedge psi) = FV(phi) union FV(psi)."""
        v_x = Variable('v_x')
        v_y = Variable('v_y')
        prefix = ['\\wedge', ['P', v_x], ['Q', v_y]]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset({v_x, v_y})

    def test_fv_disjunction(self):
        """FV(phi \\vee psi) = FV(phi) union FV(psi)."""
        v_x = Variable('v_x')
        prefix = ['\\vee', ['P', v_x], ['Q']]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset({v_x})

    def test_fv_implication(self):
        """FV(phi \\rightarrow psi)."""
        v_x = Variable('v_x')
        v_y = Variable('v_y')
        prefix = ['\\rightarrow', ['P', v_x], ['Q', v_y]]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset({v_x, v_y})

    def test_fv_equivalence(self):
        """FV(phi \\equiv psi)."""
        v_x = Variable('v_x')
        prefix = ['\\equiv', ['P', v_x], ['P', v_x]]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset({v_x})

    # --- Quantifiers ---

    def test_fv_universal_quantifier_binds_variable(self):
        """FV(\\forall v_x. P[v_x]) = {} - quantifier binds the variable."""
        v_x = Variable('v_x')
        prefix = ['\\forall', ['\\lambda', v_x, ['P', v_x]]]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset()

    def test_fv_existential_quantifier_binds_variable(self):
        """FV(\\exists v_x. P[v_x]) = {} - quantifier binds the variable."""
        v_x = Variable('v_x')
        prefix = ['\\exists', ['\\lambda', v_x, ['P', v_x]]]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset()

    def test_fv_quantifier_with_free_variable_in_body(self):
        """FV(\\forall v_x. R[v_x, v_y]) = {v_y} - v_y is free."""
        v_x = Variable('v_x')
        v_y = Variable('v_y')
        prefix = ['\\forall', ['\\lambda', v_x, ['R', v_x, v_y]]]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset({v_y})

    # --- Lambda application ---

    def test_fv_lambda_application_closed(self):
        """FV((\\lambda v_x. P[v_x])(a<>)) = {} - closed by application."""
        v_x = Variable('v_x')
        const_a = Constant('a')
        prefix = ['\\lambdaApp', v_x, ['P', v_x], const_a]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset()

    def test_fv_lambda_application_with_free_var_in_argument(self):
        """FV((\\lambda v_x. P[v_x])(v_y)) = {v_y} - v_y is free in arg."""
        v_x = Variable('v_x')
        v_y = Variable('v_y')
        prefix = ['\\lambdaApp', v_x, ['P', v_x], v_y]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset({v_y})

    def test_fv_lambda_application_with_free_var_in_body(self):
        """FV((\\lambda v_x. R[v_x, v_y])(a<>)) = {v_y}."""
        v_x = Variable('v_x')
        v_y = Variable('v_y')
        const_a = Constant('a')
        prefix = ['\\lambdaApp', v_x, ['R', v_x, v_y], const_a]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset({v_y})

    # --- Bare lambda (not WFF, but FV computed for error messages) ---

    def test_fv_bare_lambda(self):
        """FV(\\lambda v_x. P[v_x]) = {} - variable bound by lambda."""
        v_x = Variable('v_x')
        prefix = ['\\lambda', v_x, ['P', v_x]]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset()

    def test_fv_bare_lambda_with_free_var(self):
        """FV(\\lambda v_x. R[v_x, v_y]) = {v_y}."""
        v_x = Variable('v_x')
        v_y = Variable('v_y')
        prefix = ['\\lambda', v_x, ['R', v_x, v_y]]
        fv = compute_formula_free_variables(prefix)
        assert fv == frozenset({v_y})

    # --- Terms (should delegate to term's free_variables) ---

    def test_fv_variable_term(self):
        """Variable term has itself as free variable."""
        v_x = Variable('v_x')
        fv = compute_formula_free_variables(v_x)
        assert fv == frozenset({v_x})

    def test_fv_constant_term(self):
        """Constant term has no free variables."""
        const = Constant('a')
        fv = compute_formula_free_variables(const)
        assert fv == frozenset()

    def test_fv_function_application_term(self):
        """FunctionApplication term's free vars come from args."""
        v_x = Variable('v_x')
        func = FunctionApplication('f', (v_x,))
        fv = compute_formula_free_variables(func)
        assert fv == frozenset({v_x})

    # --- Edge cases ---

    def test_fv_empty_list(self):
        """Empty list returns empty set."""
        fv = compute_formula_free_variables([])
        assert fv == frozenset()

    def test_fv_none(self):
        """None returns empty set."""
        fv = compute_formula_free_variables(None)
        assert fv == frozenset()


class TestIsSyntacticallyWff:
    """Tests for is_syntactically_wff function."""

    # --- Valid formulas ---

    def test_zero_arity_predicate_is_wff(self):
        """Zero-arity predicate P[] is a WFF."""
        prefix = ['P']
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True
        assert msg == ""

    def test_unary_predicate_is_wff(self):
        """Predicate P[v_x] is a WFF (may be open, but syntactically valid)."""
        v_x = Variable('v_x')
        prefix = ['P', v_x]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_top_is_wff(self):
        """\\top is a WFF."""
        prefix = ['\\top']
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_bot_is_wff(self):
        """\\bot is a WFF."""
        prefix = ['\\bot']
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_negation_is_wff(self):
        """\\neg phi is a WFF."""
        prefix = ['\\neg', ['P']]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_conjunction_is_wff(self):
        """phi \\wedge psi is a WFF."""
        prefix = ['\\wedge', ['P'], ['Q']]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_disjunction_is_wff(self):
        """phi \\vee psi is a WFF."""
        prefix = ['\\vee', ['P'], ['Q']]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_implication_is_wff(self):
        """phi \\rightarrow psi is a WFF."""
        prefix = ['\\rightarrow', ['P'], ['Q']]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_equivalence_is_wff(self):
        """phi \\equiv psi is a WFF."""
        prefix = ['\\equiv', ['P'], ['Q']]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_universal_quantifier_is_wff(self):
        """\\forall v_x. phi is a WFF."""
        v_x = Variable('v_x')
        prefix = ['\\forall', ['\\lambda', v_x, ['P', v_x]]]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_existential_quantifier_is_wff(self):
        """\\exists v_x. phi is a WFF."""
        v_x = Variable('v_x')
        prefix = ['\\exists', ['\\lambda', v_x, ['P', v_x]]]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_lambda_application_is_wff(self):
        """(\\lambda v_x. phi)(t) is a WFF."""
        v_x = Variable('v_x')
        const_a = Constant('a')
        prefix = ['\\lambdaApp', v_x, ['P', v_x], const_a]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    # --- Invalid formulas (terms) ---

    def test_variable_is_not_wff(self):
        """Variable v_x is not a WFF."""
        v_x = Variable('v_x')
        prefix = [v_x]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is False
        assert "variable" in msg.lower()
        assert "v_x" in msg

    def test_constant_is_not_wff(self):
        """Constant a<> is not a WFF."""
        const_a = Constant('a')
        prefix = [const_a]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is False
        assert "constant" in msg.lower()

    def test_function_application_is_not_wff(self):
        """Function application f<v_x> is not a WFF."""
        v_x = Variable('v_x')
        func = FunctionApplication('f', (v_x,))
        prefix = [func]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is False
        assert "function application" in msg.lower()

    # --- Invalid formulas (bare lambda) ---

    def test_bare_lambda_is_not_wff(self):
        """Bare lambda \\lambda v_x. phi is not a WFF."""
        v_x = Variable('v_x')
        prefix = ['\\lambda', v_x, ['P', v_x]]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is False
        assert "lambda" in msg.lower()

    # --- Edge cases ---

    def test_empty_list_is_not_wff(self):
        """Empty list is not a WFF."""
        is_wff, msg = is_syntactically_wff([])
        assert is_wff is False
        assert "empty" in msg.lower()

    def test_non_list_is_not_wff(self):
        """Non-list input is not a WFF."""
        is_wff, msg = is_syntactically_wff("P")
        assert is_wff is False
        assert "expected list" in msg.lower()
