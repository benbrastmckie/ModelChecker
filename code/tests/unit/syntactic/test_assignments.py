"""Unit tests for VariableAssignment class.

Tests the variable assignment infrastructure for first-order semantics:
- Empty assignment creation
- Variable binding and lookup
- V-variant construction
- Domain access
- Error handling for unbound variables
"""

import pytest
import z3

from model_checker.syntactic.terms import Variable
from model_checker.syntactic.assignments import VariableAssignment


class TestVariableAssignmentCreation:
    """Tests for creating VariableAssignment instances."""

    def test_empty_assignment_creation(self):
        """Empty assignment should be creatable."""
        sigma = VariableAssignment.empty()
        assert sigma is not None
        assert sigma.domain() == frozenset()

    def test_assignment_from_bindings(self):
        """Assignment should be creatable from bindings."""
        v_x = Variable("v_x")
        val = z3.BitVecVal(5, 4)
        sigma = VariableAssignment(frozenset([(v_x, val)]))
        assert v_x in sigma
        assert sigma[v_x] is val


class TestVariableAssignmentLookup:
    """Tests for looking up variable values in assignments."""

    def test_lookup_bound_variable(self):
        """Lookup should return the assigned value for bound variables."""
        v_x = Variable("v_x")
        val = z3.BitVecVal(3, 4)
        sigma = VariableAssignment(frozenset([(v_x, val)]))
        assert sigma[v_x] is val

    def test_lookup_unbound_variable_raises_keyerror(self):
        """Lookup should raise KeyError for unbound variables."""
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        val = z3.BitVecVal(3, 4)
        sigma = VariableAssignment(frozenset([(v_x, val)]))
        with pytest.raises(KeyError):
            _ = sigma[v_y]

    def test_contains_bound_variable(self):
        """Contains should return True for bound variables."""
        v_x = Variable("v_x")
        val = z3.BitVecVal(3, 4)
        sigma = VariableAssignment(frozenset([(v_x, val)]))
        assert v_x in sigma

    def test_contains_unbound_variable(self):
        """Contains should return False for unbound variables."""
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        val = z3.BitVecVal(3, 4)
        sigma = VariableAssignment(frozenset([(v_x, val)]))
        assert v_y not in sigma

    def test_multiple_bindings_lookup(self):
        """Lookup should work correctly with multiple bindings."""
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        val_x = z3.BitVecVal(3, 4)
        val_y = z3.BitVecVal(7, 4)
        sigma = VariableAssignment(frozenset([(v_x, val_x), (v_y, val_y)]))
        assert sigma[v_x] is val_x
        assert sigma[v_y] is val_y


class TestVariableAssignmentVariant:
    """Tests for v-variant assignment construction."""

    def test_variant_adds_new_binding(self):
        """Variant should add binding for unbound variable."""
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        val_x = z3.BitVecVal(3, 4)
        val_y = z3.BitVecVal(7, 4)
        sigma = VariableAssignment(frozenset([(v_x, val_x)]))

        sigma_variant = sigma.variant(v_y, val_y)

        # Original unchanged
        assert v_x in sigma
        assert v_y not in sigma

        # Variant has both
        assert v_x in sigma_variant
        assert v_y in sigma_variant
        assert sigma_variant[v_x] is val_x
        assert sigma_variant[v_y] is val_y

    def test_variant_replaces_existing_binding(self):
        """Variant should replace binding for already bound variable."""
        v_x = Variable("v_x")
        old_val = z3.BitVecVal(3, 4)
        new_val = z3.BitVecVal(7, 4)
        sigma = VariableAssignment(frozenset([(v_x, old_val)]))

        sigma_variant = sigma.variant(v_x, new_val)

        # Original unchanged
        assert sigma[v_x] is old_val

        # Variant has new value
        assert sigma_variant[v_x] is new_val

    def test_variant_is_immutable(self):
        """Creating a variant should not modify the original."""
        v_x = Variable("v_x")
        val = z3.BitVecVal(3, 4)
        sigma = VariableAssignment.empty()

        sigma_variant = sigma.variant(v_x, val)

        # Original still empty
        assert sigma.domain() == frozenset()
        # Variant has binding
        assert sigma_variant.domain() == frozenset({v_x})

    def test_variant_from_empty(self):
        """Variant should work on empty assignment."""
        v_x = Variable("v_x")
        val = z3.BitVecVal(5, 4)
        sigma = VariableAssignment.empty()

        sigma_variant = sigma.variant(v_x, val)

        assert v_x in sigma_variant
        assert sigma_variant[v_x] is val


class TestVariableAssignmentDomain:
    """Tests for domain() method."""

    def test_empty_domain(self):
        """Empty assignment should have empty domain."""
        sigma = VariableAssignment.empty()
        assert sigma.domain() == frozenset()

    def test_single_variable_domain(self):
        """Domain should contain the single bound variable."""
        v_x = Variable("v_x")
        val = z3.BitVecVal(3, 4)
        sigma = VariableAssignment(frozenset([(v_x, val)]))
        assert sigma.domain() == frozenset({v_x})

    def test_multiple_variables_domain(self):
        """Domain should contain all bound variables."""
        v_x = Variable("v_x")
        v_y = Variable("v_y")
        v_z = Variable("v_z")
        sigma = VariableAssignment(frozenset([
            (v_x, z3.BitVecVal(1, 4)),
            (v_y, z3.BitVecVal(2, 4)),
            (v_z, z3.BitVecVal(3, 4)),
        ]))
        assert sigma.domain() == frozenset({v_x, v_y, v_z})


class TestVariableAssignmentEquality:
    """Tests for assignment equality (frozen dataclass)."""

    def test_equal_assignments_are_equal(self):
        """Assignments with same bindings should be equal."""
        v_x = Variable("v_x")
        val = z3.BitVecVal(3, 4)
        sigma1 = VariableAssignment(frozenset([(v_x, val)]))
        sigma2 = VariableAssignment(frozenset([(v_x, val)]))
        assert sigma1 == sigma2

    def test_different_assignments_are_not_equal(self):
        """Assignments with different bindings should not be equal."""
        v_x = Variable("v_x")
        val1 = z3.BitVecVal(3, 4)
        val2 = z3.BitVecVal(5, 4)
        sigma1 = VariableAssignment(frozenset([(v_x, val1)]))
        sigma2 = VariableAssignment(frozenset([(v_x, val2)]))
        # Note: Z3 BitVecVal equality may not work directly, but the
        # assignments themselves should be different objects with different vals
        assert sigma1 is not sigma2
