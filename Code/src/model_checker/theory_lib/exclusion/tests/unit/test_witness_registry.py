"""
Unit tests for exclusion witness registry implementation.

Tests the WitnessRegistry class functionality including
predicate registration, retrieval, and management.
"""

import pytest
import z3
from typing import Dict, Set

from model_checker.theory_lib.exclusion.semantic.registry import WitnessRegistry


class TestWitnessRegistry:
    """Test the WitnessRegistry class."""

    @pytest.fixture
    def registry(self) -> WitnessRegistry:
        """Create a WitnessRegistry instance for testing."""
        return WitnessRegistry(N=3)

    def test_initialization(self, registry: WitnessRegistry) -> None:
        """Test that WitnessRegistry initializes correctly."""
        assert registry.N == 3
        assert isinstance(registry.predicates, dict)
        assert isinstance(registry.formula_mapping, dict)
        assert len(registry.predicates) == 0
        assert len(registry.formula_mapping) == 0

    def test_register_witness_predicates(self, registry: WitnessRegistry) -> None:
        """Test registering witness predicates for a formula."""
        formula_str = "test_formula"

        h_pred, y_pred = registry.register_witness_predicates(formula_str)

        # Check return values
        assert isinstance(h_pred, z3.FuncDeclRef)
        assert isinstance(y_pred, z3.FuncDeclRef)

        # Check predicates are stored
        assert f"{formula_str}_h" in registry.predicates
        assert f"{formula_str}_y" in registry.predicates
        assert registry.predicates[f"{formula_str}_h"] is h_pred
        assert registry.predicates[f"{formula_str}_y"] is y_pred

        # Check formula mapping
        assert formula_str in registry.formula_mapping
        expected_mapping = {f"{formula_str}_h", f"{formula_str}_y"}
        assert registry.formula_mapping[formula_str] == expected_mapping

    def test_register_multiple_formulas(self, registry: WitnessRegistry) -> None:
        """Test registering witness predicates for multiple formulas."""
        formulas = ["formula_A", "formula_B", "formula_C"]

        for formula in formulas:
            h_pred, y_pred = registry.register_witness_predicates(formula)
            assert h_pred is not None
            assert y_pred is not None

        # Check all predicates are stored
        assert len(registry.predicates) == 6  # 3 formulas × 2 predicates each
        assert len(registry.formula_mapping) == 3

        # Check specific mappings
        for formula in formulas:
            assert formula in registry.formula_mapping
            assert f"{formula}_h" in registry.predicates
            assert f"{formula}_y" in registry.predicates

    def test_register_same_formula_twice(self, registry: WitnessRegistry) -> None:
        """Test registering the same formula twice overwrites previous registration."""
        formula_str = "duplicate_formula"

        # First registration
        h_pred1, y_pred1 = registry.register_witness_predicates(formula_str)

        # Second registration
        h_pred2, y_pred2 = registry.register_witness_predicates(formula_str)

        # Check that new predicates are stored (old ones overwritten)
        assert registry.predicates[f"{formula_str}_h"] is h_pred2
        assert registry.predicates[f"{formula_str}_y"] is y_pred2

        # Formula mapping should still exist and be updated
        assert formula_str in registry.formula_mapping
        assert len(registry.formula_mapping[formula_str]) == 2

        # Check that we still have only 2 predicates total (overwritten, not duplicated)
        assert len(registry.predicates) == 2

    def test_predicate_function_signatures(self, registry: WitnessRegistry) -> None:
        """Test that registered predicates have correct Z3 function signatures."""
        formula_str = "signature_test"
        h_pred, y_pred = registry.register_witness_predicates(formula_str)

        # Check function domain and range
        assert h_pred.domain(0) == z3.BitVecSort(3)  # Input: BitVec(3)
        assert h_pred.range() == z3.BitVecSort(3)    # Output: BitVec(3)

        assert y_pred.domain(0) == z3.BitVecSort(3)  # Input: BitVec(3)
        assert y_pred.range() == z3.BitVecSort(3)    # Output: BitVec(3)

        # Check function names
        assert h_pred.name() == f"{formula_str}_h"
        assert y_pred.name() == f"{formula_str}_y"

    def test_get_all_predicates(self, registry: WitnessRegistry) -> None:
        """Test get_all_predicates returns correct dictionary."""
        # Start with empty registry
        all_predicates = registry.get_all_predicates()
        assert isinstance(all_predicates, dict)
        assert len(all_predicates) == 0

        # Add some predicates
        formulas = ["A", "B"]
        for formula in formulas:
            registry.register_witness_predicates(formula)

        all_predicates = registry.get_all_predicates()
        assert len(all_predicates) == 4  # 2 formulas × 2 predicates each

        expected_keys = {"A_h", "A_y", "B_h", "B_y"}
        assert set(all_predicates.keys()) == expected_keys

        # Verify it's a copy (not the original)
        all_predicates["new_key"] = "new_value"
        assert "new_key" not in registry.predicates

    def test_get_all_predicates_types(self, registry: WitnessRegistry) -> None:
        """Test that get_all_predicates returns correct types."""
        registry.register_witness_predicates("test")
        all_predicates = registry.get_all_predicates()

        for name, predicate in all_predicates.items():
            assert isinstance(name, str)
            assert isinstance(predicate, z3.FuncDeclRef)

    def test_clear_method(self, registry: WitnessRegistry) -> None:
        """Test the clear method removes all predicates."""
        # Add some predicates
        formulas = ["formula1", "formula2", "formula3"]
        for formula in formulas:
            registry.register_witness_predicates(formula)

        # Verify predicates exist
        assert len(registry.predicates) > 0
        assert len(registry.formula_mapping) > 0

        # Clear registry
        registry.clear()

        # Verify everything is cleared
        assert len(registry.predicates) == 0
        assert len(registry.formula_mapping) == 0
        assert isinstance(registry.predicates, dict)
        assert isinstance(registry.formula_mapping, dict)

    def test_formula_mapping_structure(self, registry: WitnessRegistry) -> None:
        """Test that formula mapping has correct structure."""
        formula = "mapping_test"
        registry.register_witness_predicates(formula)

        mapping = registry.formula_mapping[formula]
        assert isinstance(mapping, set)
        assert len(mapping) == 2
        assert f"{formula}_h" in mapping
        assert f"{formula}_y" in mapping

    def test_n_parameter_usage(self) -> None:
        """Test that N parameter is correctly used in function creation."""
        # Test with different N values
        for n in [2, 3, 4, 5]:
            registry = WitnessRegistry(N=n)
            h_pred, y_pred = registry.register_witness_predicates("test_n")

            # Check that functions use correct bit vector size
            assert h_pred.domain(0) == z3.BitVecSort(n)
            assert h_pred.range() == z3.BitVecSort(n)
            assert y_pred.domain(0) == z3.BitVecSort(n)
            assert y_pred.range() == z3.BitVecSort(n)

    def test_special_formula_names(self, registry: WitnessRegistry) -> None:
        """Test registering predicates with special formula names."""
        special_formulas = [
            "formula_with_underscores",
            "formula.with.dots",
            "formula-with-hyphens",
            "formula with spaces",
            "123numeric_formula",
            "UPPERCASE_FORMULA",
            "",  # empty string
        ]

        for formula in special_formulas:
            h_pred, y_pred = registry.register_witness_predicates(formula)

            # Check that predicates are created successfully
            assert isinstance(h_pred, z3.FuncDeclRef)
            assert isinstance(y_pred, z3.FuncDeclRef)

            # Check that mapping is correct
            expected_h_name = f"{formula}_h"
            expected_y_name = f"{formula}_y"
            assert expected_h_name in registry.predicates
            assert expected_y_name in registry.predicates


class TestWitnessRegistryIntegration:
    """Integration tests for WitnessRegistry with Z3 solver."""

    def test_predicates_in_z3_solver(self) -> None:
        """Test that registered predicates can be used in Z3 solver."""
        registry = WitnessRegistry(N=3)
        h_pred, y_pred = registry.register_witness_predicates("A")

        # Create a Z3 solver and use the predicates
        solver = z3.Solver()

        # Create bit vector variables
        state1 = z3.BitVecVal(1, 3)
        state2 = z3.BitVecVal(2, 3)

        # Use predicates in constraints
        solver.add(h_pred(state1) == state2)
        solver.add(y_pred(state1) != state1)

        # Check that solver can handle these constraints
        result = solver.check()
        assert result in [z3.sat, z3.unsat]  # Should not error

    def test_predicate_evaluation_in_model(self) -> None:
        """Test that predicates can be evaluated in a Z3 model."""
        registry = WitnessRegistry(N=3)
        h_pred, y_pred = registry.register_witness_predicates("test")

        # Create a solver with specific constraints
        solver = z3.Solver()
        state = z3.BitVecVal(1, 3)
        result_state = z3.BitVecVal(2, 3)

        solver.add(h_pred(state) == result_state)

        assert solver.check() == z3.sat
        model = solver.model()

        # Evaluate the predicate in the model
        evaluated = model.eval(h_pred(state))
        assert evaluated is not None

    def test_multiple_registrations_in_solver(self) -> None:
        """Test multiple formula registrations work together in solver."""
        registry = WitnessRegistry(N=2)

        # Register multiple formulas
        formulas = ["A", "B", "C"]
        predicates = {}
        for formula in formulas:
            h_pred, y_pred = registry.register_witness_predicates(formula)
            predicates[f"{formula}_h"] = h_pred
            predicates[f"{formula}_y"] = y_pred

        # Create constraints involving multiple predicates
        solver = z3.Solver()
        state = z3.BitVecVal(1, 2)

        for formula in formulas:
            h_pred = predicates[f"{formula}_h"]
            y_pred = predicates[f"{formula}_y"]
            solver.add(h_pred(state) != y_pred(state))

        # Should be satisfiable
        assert solver.check() == z3.sat