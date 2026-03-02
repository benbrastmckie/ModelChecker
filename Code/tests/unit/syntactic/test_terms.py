"""Unit tests for first-order term algebra.

Tests the Term abstract base class and its concrete implementations:
Variable, Constant, and FunctionApplication.
"""

import pytest
from abc import ABC


# =============================================================================
# Phase 1: Term ABC Tests
# =============================================================================

class TestTermABC:
    """Tests for Term abstract base class structure."""

    def test_term_is_abstract_class(self):
        """Term should be an abstract base class."""
        from model_checker.syntactic.terms import Term
        assert isinstance(Term, type)
        assert issubclass(Term, ABC)

    def test_term_cannot_be_instantiated(self):
        """Cannot instantiate Term directly."""
        from model_checker.syntactic.terms import Term
        with pytest.raises(TypeError):
            Term()

    def test_term_requires_free_variables_method(self):
        """Term should define abstract free_variables method."""
        from model_checker.syntactic.terms import Term
        # Check that free_variables is in the abstract methods
        assert 'free_variables' in Term.__abstractmethods__

    def test_term_requires_substitute_method(self):
        """Term should define abstract substitute method."""
        from model_checker.syntactic.terms import Term
        # Check that substitute is in the abstract methods
        assert 'substitute' in Term.__abstractmethods__


# =============================================================================
# Phase 2: Variable Tests
# =============================================================================

class TestVariableCreation:
    """Tests for Variable instantiation and validation."""

    def test_create_variable_with_valid_name(self):
        """Variable with v_ prefix should be created."""
        from model_checker.syntactic.terms import Variable
        v = Variable("v_1")
        assert v.name == "v_1"

    def test_create_variable_with_alphabetic_suffix(self):
        """Variable with alphabetic suffix like v_x should work."""
        from model_checker.syntactic.terms import Variable
        v = Variable("v_x")
        assert v.name == "v_x"

    def test_create_variable_with_complex_name(self):
        """Variable with complex name like v_foo_bar should work."""
        from model_checker.syntactic.terms import Variable
        v = Variable("v_foo_bar")
        assert v.name == "v_foo_bar"

    def test_variable_missing_prefix_raises_error(self):
        """Variable without v_ prefix should raise ValueError."""
        from model_checker.syntactic.terms import Variable
        with pytest.raises(ValueError, match="v_"):
            Variable("x")

    def test_variable_numeric_name_raises_error(self):
        """Variable with just number should raise ValueError."""
        from model_checker.syntactic.terms import Variable
        with pytest.raises(ValueError, match="v_"):
            Variable("1")

    def test_variable_wrong_prefix_raises_error(self):
        """Variable with wrong prefix should raise ValueError."""
        from model_checker.syntactic.terms import Variable
        with pytest.raises(ValueError, match="v_"):
            Variable("foo")


class TestVariableEquality:
    """Tests for Variable equality and hashing."""

    def test_same_name_variables_equal(self):
        """Variables with same name should be equal."""
        from model_checker.syntactic.terms import Variable
        v1 = Variable("v_x")
        v2 = Variable("v_x")
        assert v1 == v2

    def test_different_name_variables_not_equal(self):
        """Variables with different names should not be equal."""
        from model_checker.syntactic.terms import Variable
        v1 = Variable("v_x")
        v2 = Variable("v_y")
        assert v1 != v2

    def test_variable_hashable(self):
        """Variables should be hashable (usable in sets/dicts)."""
        from model_checker.syntactic.terms import Variable
        v = Variable("v_x")
        s = {v}
        assert v in s

    def test_equal_variables_same_hash(self):
        """Equal variables should have same hash."""
        from model_checker.syntactic.terms import Variable
        v1 = Variable("v_x")
        v2 = Variable("v_x")
        assert hash(v1) == hash(v2)


class TestVariableFreeVariables:
    """Tests for Variable.free_variables() method."""

    def test_variable_free_variables_returns_set(self):
        """free_variables() should return a set."""
        from model_checker.syntactic.terms import Variable
        v = Variable("v_x")
        result = v.free_variables()
        assert isinstance(result, (set, frozenset))

    def test_variable_free_variables_contains_self(self):
        """free_variables() should contain the variable itself."""
        from model_checker.syntactic.terms import Variable
        v = Variable("v_x")
        result = v.free_variables()
        assert v in result

    def test_variable_free_variables_singleton(self):
        """free_variables() should return singleton set."""
        from model_checker.syntactic.terms import Variable
        v = Variable("v_x")
        result = v.free_variables()
        assert len(result) == 1


class TestVariableSubstitute:
    """Tests for Variable.substitute() method."""

    def test_substitute_matching_variable(self):
        """Substituting v for v should return replacement."""
        from model_checker.syntactic.terms import Variable, Constant
        v = Variable("v_x")
        replacement = Constant("a")
        result = v.substitute(replacement, v)
        assert result == replacement

    def test_substitute_non_matching_variable(self):
        """Substituting different variable returns self."""
        from model_checker.syntactic.terms import Variable, Constant
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        replacement = Constant("a")
        result = v_x.substitute(replacement, v_y)
        assert result == v_x

    def test_substitute_preserves_immutability(self):
        """Substitution should not modify original variable."""
        from model_checker.syntactic.terms import Variable, Constant
        v = Variable("v_x")
        replacement = Constant("a")
        v.substitute(replacement, v)
        # Original should still be intact
        assert v.name == "v_x"


class TestVariableString:
    """Tests for Variable string representation."""

    def test_variable_str_returns_name(self):
        """str(Variable) should return the name."""
        from model_checker.syntactic.terms import Variable
        v = Variable("v_x")
        assert str(v) == "v_x"

    def test_variable_repr(self):
        """repr(Variable) should be informative."""
        from model_checker.syntactic.terms import Variable
        v = Variable("v_x")
        repr_str = repr(v)
        assert "Variable" in repr_str
        assert "v_x" in repr_str


# =============================================================================
# Phase 3: Constant Tests
# =============================================================================

class TestConstantCreation:
    """Tests for Constant instantiation."""

    def test_create_constant(self):
        """Constant should be creatable with a name."""
        from model_checker.syntactic.terms import Constant
        c = Constant("a")
        assert c.name == "a"

    def test_create_constant_zero(self):
        """Constant with name 'zero' should work."""
        from model_checker.syntactic.terms import Constant
        c = Constant("zero")
        assert c.name == "zero"

    def test_constant_is_term(self):
        """Constant should be a Term."""
        from model_checker.syntactic.terms import Term, Constant
        c = Constant("a")
        assert isinstance(c, Term)


class TestConstantEquality:
    """Tests for Constant equality and hashing."""

    def test_same_name_constants_equal(self):
        """Constants with same name should be equal."""
        from model_checker.syntactic.terms import Constant
        c1 = Constant("a")
        c2 = Constant("a")
        assert c1 == c2

    def test_different_name_constants_not_equal(self):
        """Constants with different names should not be equal."""
        from model_checker.syntactic.terms import Constant
        c1 = Constant("a")
        c2 = Constant("b")
        assert c1 != c2

    def test_constant_hashable(self):
        """Constants should be hashable."""
        from model_checker.syntactic.terms import Constant
        c = Constant("a")
        s = {c}
        assert c in s

    def test_constant_different_from_variable(self):
        """Constant should not equal Variable with same-ish name."""
        from model_checker.syntactic.terms import Constant, Variable
        c = Constant("v_x")  # Constants can have any name
        v = Variable("v_x")
        assert c != v


class TestConstantFreeVariables:
    """Tests for Constant.free_variables() method."""

    def test_constant_free_variables_empty(self):
        """Constants should have no free variables."""
        from model_checker.syntactic.terms import Constant
        c = Constant("a")
        result = c.free_variables()
        assert len(result) == 0

    def test_constant_free_variables_is_set(self):
        """free_variables() should return a set."""
        from model_checker.syntactic.terms import Constant
        c = Constant("a")
        result = c.free_variables()
        assert isinstance(result, (set, frozenset))


class TestConstantSubstitute:
    """Tests for Constant.substitute() method."""

    def test_constant_substitute_unchanged(self):
        """Substituting in a constant returns the constant."""
        from model_checker.syntactic.terms import Constant, Variable
        c = Constant("a")
        v = Variable("v_x")
        replacement = Constant("b")
        result = c.substitute(replacement, v)
        assert result == c

    def test_constant_substitute_returns_self(self):
        """Substituting in a constant returns same object (immutable)."""
        from model_checker.syntactic.terms import Constant, Variable
        c = Constant("a")
        v = Variable("v_x")
        replacement = Constant("b")
        result = c.substitute(replacement, v)
        assert result is c


class TestConstantString:
    """Tests for Constant string representation."""

    def test_constant_str_returns_name(self):
        """str(Constant) should return the name."""
        from model_checker.syntactic.terms import Constant
        c = Constant("zero")
        assert str(c) == "zero"


# =============================================================================
# Phase 4: FunctionApplication Tests
# =============================================================================

class TestFunctionApplicationCreation:
    """Tests for FunctionApplication instantiation."""

    def test_create_function_application(self):
        """FunctionApplication should be creatable."""
        from model_checker.syntactic.terms import FunctionApplication, Variable
        v = Variable("v_x")
        f = FunctionApplication("succ", (v,))
        assert f.name == "succ"
        assert f.arguments == (v,)

    def test_function_application_with_multiple_args(self):
        """FunctionApplication with multiple args should work."""
        from model_checker.syntactic.terms import FunctionApplication, Variable
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        f = FunctionApplication("plus", (v_x, v_y))
        assert len(f.arguments) == 2

    def test_function_application_with_constant_args(self):
        """FunctionApplication with constant args should work."""
        from model_checker.syntactic.terms import FunctionApplication, Constant
        zero = Constant("zero")
        f = FunctionApplication("succ", (zero,))
        assert f.arguments == (zero,)

    def test_function_application_is_term(self):
        """FunctionApplication should be a Term."""
        from model_checker.syntactic.terms import Term, FunctionApplication, Constant
        c = Constant("a")
        f = FunctionApplication("f", (c,))
        assert isinstance(f, Term)

    def test_function_application_tuple_conversion(self):
        """Arguments should be stored as tuple."""
        from model_checker.syntactic.terms import FunctionApplication, Variable
        v = Variable("v_x")
        # Even if passed as list, should be stored as tuple
        f = FunctionApplication("f", [v])
        assert isinstance(f.arguments, tuple)


class TestFunctionApplicationEquality:
    """Tests for FunctionApplication equality and hashing."""

    def test_same_function_applications_equal(self):
        """Same name and args should be equal."""
        from model_checker.syntactic.terms import FunctionApplication, Variable
        v = Variable("v_x")
        f1 = FunctionApplication("succ", (v,))
        f2 = FunctionApplication("succ", (v,))
        assert f1 == f2

    def test_different_names_not_equal(self):
        """Different names should not be equal."""
        from model_checker.syntactic.terms import FunctionApplication, Variable
        v = Variable("v_x")
        f1 = FunctionApplication("f", (v,))
        f2 = FunctionApplication("g", (v,))
        assert f1 != f2

    def test_different_args_not_equal(self):
        """Different args should not be equal."""
        from model_checker.syntactic.terms import FunctionApplication, Variable
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        f1 = FunctionApplication("f", (v_x,))
        f2 = FunctionApplication("f", (v_y,))
        assert f1 != f2

    def test_function_application_hashable(self):
        """FunctionApplication should be hashable."""
        from model_checker.syntactic.terms import FunctionApplication, Constant
        c = Constant("a")
        f = FunctionApplication("f", (c,))
        s = {f}
        assert f in s


class TestFunctionApplicationFreeVariables:
    """Tests for FunctionApplication.free_variables() method."""

    def test_free_variables_with_variable_arg(self):
        """free_variables should include variable arguments."""
        from model_checker.syntactic.terms import FunctionApplication, Variable
        v = Variable("v_x")
        f = FunctionApplication("succ", (v,))
        result = f.free_variables()
        assert v in result

    def test_free_variables_with_constant_arg(self):
        """free_variables with only constants should be empty."""
        from model_checker.syntactic.terms import FunctionApplication, Constant
        c = Constant("zero")
        f = FunctionApplication("succ", (c,))
        result = f.free_variables()
        assert len(result) == 0

    def test_free_variables_union_of_args(self):
        """free_variables should be union of all arg free vars."""
        from model_checker.syntactic.terms import FunctionApplication, Variable
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        f = FunctionApplication("plus", (v_x, v_y))
        result = f.free_variables()
        assert v_x in result
        assert v_y in result
        assert len(result) == 2

    def test_free_variables_nested(self):
        """free_variables should work for nested applications."""
        from model_checker.syntactic.terms import FunctionApplication, Variable, Constant
        v = Variable("v_x")
        c = Constant("zero")
        inner = FunctionApplication("succ", (v,))
        outer = FunctionApplication("plus", (inner, c))
        result = outer.free_variables()
        assert v in result
        assert len(result) == 1


class TestFunctionApplicationSubstitute:
    """Tests for FunctionApplication.substitute() method."""

    def test_substitute_in_function_arg(self):
        """Substitute should apply to arguments."""
        from model_checker.syntactic.terms import FunctionApplication, Variable, Constant
        v = Variable("v_x")
        c = Constant("zero")
        f = FunctionApplication("succ", (v,))
        result = f.substitute(c, v)
        expected = FunctionApplication("succ", (c,))
        assert result == expected

    def test_substitute_no_match(self):
        """Substitute with no matching var returns equivalent term."""
        from model_checker.syntactic.terms import FunctionApplication, Variable, Constant
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        c = Constant("zero")
        f = FunctionApplication("succ", (v_x,))
        result = f.substitute(c, v_y)
        assert result == f

    def test_substitute_nested(self):
        """Substitute should work recursively."""
        from model_checker.syntactic.terms import FunctionApplication, Variable, Constant
        v = Variable("v_x")
        c = Constant("zero")
        inner = FunctionApplication("succ", (v,))
        outer = FunctionApplication("f", (inner,))
        result = outer.substitute(c, v)
        expected_inner = FunctionApplication("succ", (c,))
        expected = FunctionApplication("f", (expected_inner,))
        assert result == expected

    def test_substitute_multiple_occurrences(self):
        """Substitute should replace all occurrences."""
        from model_checker.syntactic.terms import FunctionApplication, Variable, Constant
        v = Variable("v_x")
        c = Constant("zero")
        f = FunctionApplication("plus", (v, v))
        result = f.substitute(c, v)
        expected = FunctionApplication("plus", (c, c))
        assert result == expected


class TestFunctionApplicationString:
    """Tests for FunctionApplication string representation."""

    def test_function_application_str_format(self):
        """str format should be name<args>."""
        from model_checker.syntactic.terms import FunctionApplication, Variable
        v = Variable("v_x")
        f = FunctionApplication("succ", (v,))
        result = str(f)
        assert result == "succ<v_x>"

    def test_function_application_str_multiple_args(self):
        """Multiple args should be comma-separated."""
        from model_checker.syntactic.terms import FunctionApplication, Variable
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        f = FunctionApplication("plus", (v_x, v_y))
        result = str(f)
        assert result == "plus<v_x, v_y>"

    def test_function_application_str_nested(self):
        """Nested applications should show nested format."""
        from model_checker.syntactic.terms import FunctionApplication, Constant
        zero = Constant("zero")
        inner = FunctionApplication("succ", (zero,))
        outer = FunctionApplication("succ", (inner,))
        result = str(outer)
        assert result == "succ<succ<zero>>"


# =============================================================================
# Phase 5: Integration Tests
# =============================================================================

class TestComplexTermCompositions:
    """Integration tests for complex term structures."""

    def test_arithmetic_expression(self):
        """Test arithmetic-like term: plus<succ<v_x>, zero>."""
        from model_checker.syntactic.terms import (
            FunctionApplication, Variable, Constant
        )
        v_x = Variable("v_x")
        zero = Constant("zero")
        succ_x = FunctionApplication("succ", (v_x,))
        plus_expr = FunctionApplication("plus", (succ_x, zero))

        assert v_x in plus_expr.free_variables()
        assert len(plus_expr.free_variables()) == 1

    def test_deeply_nested_term(self):
        """Test deeply nested term: succ<succ<succ<zero>>>."""
        from model_checker.syntactic.terms import FunctionApplication, Constant
        zero = Constant("zero")
        succ1 = FunctionApplication("succ", (zero,))
        succ2 = FunctionApplication("succ", (succ1,))
        succ3 = FunctionApplication("succ", (succ2,))

        assert len(succ3.free_variables()) == 0
        assert str(succ3) == "succ<succ<succ<zero>>>"

    def test_term_with_many_variables(self):
        """Test term with multiple distinct variables."""
        from model_checker.syntactic.terms import FunctionApplication, Variable
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        v_z = Variable("v_z")
        term = FunctionApplication("f", (v_x, v_y, v_z))

        fv = term.free_variables()
        assert len(fv) == 3
        assert v_x in fv and v_y in fv and v_z in fv


class TestSubstitutionChains:
    """Tests for multiple substitution operations."""

    def test_two_substitutions(self):
        """Apply two substitutions in sequence."""
        from model_checker.syntactic.terms import (
            FunctionApplication, Variable, Constant
        )
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        a = Constant("a")
        b = Constant("b")

        term = FunctionApplication("f", (v_x, v_y))
        after_first = term.substitute(a, v_x)
        after_second = after_first.substitute(b, v_y)

        expected = FunctionApplication("f", (a, b))
        assert after_second == expected

    def test_substitution_does_not_affect_other_vars(self):
        """Substituting one var should not affect others."""
        from model_checker.syntactic.terms import (
            FunctionApplication, Variable, Constant
        )
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        a = Constant("a")

        term = FunctionApplication("f", (v_x, v_y))
        result = term.substitute(a, v_x)

        assert v_y in result.free_variables()
        assert v_x not in result.free_variables()

    def test_substitution_with_term(self):
        """Substitute a variable with a complex term."""
        from model_checker.syntactic.terms import (
            FunctionApplication, Variable, Constant
        )
        v_x = Variable("v_x")
        zero = Constant("zero")
        replacement = FunctionApplication("succ", (zero,))

        original = FunctionApplication("f", (v_x,))
        result = original.substitute(replacement, v_x)

        expected = FunctionApplication("f", (replacement,))
        assert result == expected


class TestModuleExports:
    """Tests for module-level exports."""

    def test_import_from_terms_module(self):
        """Direct import from terms module should work."""
        from model_checker.syntactic.terms import (
            Term, Variable, Constant, FunctionApplication
        )
        assert Term is not None
        assert Variable is not None
        assert Constant is not None
        assert FunctionApplication is not None

    def test_import_from_syntactic_package(self):
        """Import from syntactic package should work."""
        from model_checker.syntactic import (
            Term, Variable, Constant, FunctionApplication
        )
        assert Term is not None
        assert Variable is not None
        assert Constant is not None
        assert FunctionApplication is not None
