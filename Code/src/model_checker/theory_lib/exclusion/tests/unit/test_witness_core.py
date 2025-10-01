"""
Unit tests for exclusion witness core semantics.

Tests the WitnessSemantics class core functionality including
witness predicate registration and constraint generation.
"""

import pytest
import z3
from unittest.mock import Mock, patch
from typing import Dict, Any

from model_checker.theory_lib.exclusion.semantic.core import WitnessSemantics
from model_checker.theory_lib.exclusion.semantic.registry import WitnessRegistry
from model_checker.theory_lib.exclusion.semantic.constraints import WitnessConstraintGenerator
from model_checker import syntactic


class TestWitnessSemantics:
    """Test the WitnessSemantics core class."""

    @pytest.fixture
    def basic_settings(self) -> Dict[str, Any]:
        """Basic settings for WitnessSemantics."""
        return {
            'N': 3,
            'possible': False,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'fusion_closure': False,
            'iterate': 1,
            'max_time': 1,
            'expectation': None,
        }

    @pytest.fixture
    def witness_semantics(self, basic_settings: Dict[str, Any]) -> WitnessSemantics:
        """Create a WitnessSemantics instance for testing."""
        return WitnessSemantics(basic_settings)

    def test_initialization(self, witness_semantics: WitnessSemantics) -> None:
        """Test that WitnessSemantics initializes correctly."""
        assert witness_semantics.N == 3
        assert isinstance(witness_semantics.witness_registry, WitnessRegistry)
        assert isinstance(witness_semantics.constraint_generator, WitnessConstraintGenerator)
        assert isinstance(witness_semantics._processed_formulas, set)
        assert isinstance(witness_semantics._formula_ast_mapping, dict)

    def test_z3_function_creation(self, witness_semantics: WitnessSemantics) -> None:
        """Test that Z3 functions are created correctly."""
        assert witness_semantics.verify is not None
        assert witness_semantics.excludes is not None
        assert witness_semantics.main_world is not None
        assert isinstance(witness_semantics.main_point, dict)
        assert 'world' in witness_semantics.main_point

    def test_counter_initialization(self, witness_semantics: WitnessSemantics) -> None:
        """Test that counter starts at 0."""
        assert witness_semantics.counter == 0

    def test_conflicts_method(self, witness_semantics: WitnessSemantics) -> None:
        """Test the conflicts method returns correct Z3 expression."""
        bit_e1 = z3.BitVecVal(1, 3)
        bit_e2 = z3.BitVecVal(2, 3)

        result = witness_semantics.conflicts(bit_e1, bit_e2)
        assert isinstance(result, z3.BoolRef)

    def test_coheres_method(self, witness_semantics: WitnessSemantics) -> None:
        """Test the coheres method returns correct Z3 expression."""
        bit_e1 = z3.BitVecVal(1, 3)
        bit_e2 = z3.BitVecVal(2, 3)

        result = witness_semantics.coheres(bit_e1, bit_e2)
        assert isinstance(result, z3.BoolRef)

    def test_possible_method(self, witness_semantics: WitnessSemantics) -> None:
        """Test the possible method returns correct Z3 expression."""
        bit_e = z3.BitVecVal(1, 3)

        result = witness_semantics.possible(bit_e)
        assert isinstance(result, z3.BoolRef)

    def test_compossible_method(self, witness_semantics: WitnessSemantics) -> None:
        """Test the compossible method returns correct Z3 expression."""
        bit_e1 = z3.BitVecVal(1, 3)
        bit_e2 = z3.BitVecVal(2, 3)

        result = witness_semantics.compossible(bit_e1, bit_e2)
        assert isinstance(result, z3.BoolRef)

    def test_necessary_method(self, witness_semantics: WitnessSemantics) -> None:
        """Test the necessary method returns correct Z3 expression."""
        bit_e1 = z3.BitVecVal(1, 3)

        result = witness_semantics.necessary(bit_e1)
        assert isinstance(result, z3.BoolRef)

    def test_product_method(self, witness_semantics: WitnessSemantics) -> None:
        """Test the product method returns correct fusion product."""
        set_x = {1, 2}
        set_y = {3, 4}

        result = witness_semantics.product(set_x, set_y)
        # Product computes fusion (bitwise OR) of all pairs
        # fusion(1, 3) = 1 | 3 = 3
        # fusion(1, 4) = 1 | 4 = 5
        # fusion(2, 3) = 2 | 3 = 3
        # fusion(2, 4) = 2 | 4 = 6
        expected = {3, 5, 6}  # Set removes duplicate 3
        assert result == expected

    def test_is_world_method(self, witness_semantics: WitnessSemantics) -> None:
        """Test the is_world method returns correct Z3 expression."""
        bit_s = z3.BitVecVal(1, 3)

        result = witness_semantics.is_world(bit_s)
        assert isinstance(result, z3.BoolRef)

    def test_build_model_with_none_eval_point(self, witness_semantics: WitnessSemantics) -> None:
        """Test build_model returns None when given None eval_point."""
        result = witness_semantics.build_model(None)
        assert result is None

    def test_formula_processing_tracking(self, witness_semantics: WitnessSemantics) -> None:
        """Test that formula processing is tracked correctly."""
        assert len(witness_semantics._processed_formulas) == 0
        assert len(witness_semantics._formula_ast_mapping) == 0

    def test_inherits_from_logos_semantics(self, witness_semantics: WitnessSemantics) -> None:
        """Test that WitnessSemantics properly inherits from LogosSemantics."""
        from model_checker.theory_lib.logos.semantic import LogosSemantics
        assert isinstance(witness_semantics, LogosSemantics)

    def test_default_example_settings(self) -> None:
        """Test that default example settings are properly defined."""
        expected_keys = {
            'N', 'possible', 'contingent', 'non_empty', 'non_null',
            'disjoint', 'fusion_closure', 'iterate', 'max_time', 'expectation'
        }
        assert set(WitnessSemantics.DEFAULT_EXAMPLE_SETTINGS.keys()) == expected_keys
        assert WitnessSemantics.DEFAULT_EXAMPLE_SETTINGS['N'] == 3

    def test_witness_registry_n_parameter(self, witness_semantics: WitnessSemantics) -> None:
        """Test that witness registry is initialized with correct N parameter."""
        assert witness_semantics.witness_registry.N == witness_semantics.N

    def test_constraint_generator_semantics_reference(self, witness_semantics: WitnessSemantics) -> None:
        """Test that constraint generator has correct semantics reference."""
        assert witness_semantics.constraint_generator.semantics is witness_semantics
        assert witness_semantics.constraint_generator.N == witness_semantics.N


class TestWitnessSemanticsIntegration:
    """Integration tests for WitnessSemantics with other components."""

    @pytest.fixture
    def semantics_with_registry(self) -> WitnessSemantics:
        """Create semantics instance with registry interactions."""
        settings = {
            'N': 2,
            'possible': False,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'fusion_closure': False,
            'iterate': 1,
            'max_time': 1,
            'expectation': None,
        }
        return WitnessSemantics(settings)

    def test_registry_integration(self, semantics_with_registry: WitnessSemantics) -> None:
        """Test integration between semantics and witness registry."""
        # Test that registry is properly connected
        assert semantics_with_registry.witness_registry is not None

        # Test that we can register witness predicates
        h_pred, y_pred = semantics_with_registry.witness_registry.register_witness_predicates("test_formula")

        assert h_pred is not None
        assert y_pred is not None
        assert isinstance(h_pred, z3.FuncDeclRef)
        assert isinstance(y_pred, z3.FuncDeclRef)

    def test_constraint_generator_integration(self, semantics_with_registry: WitnessSemantics) -> None:
        """Test integration between semantics and constraint generator."""
        # Test that constraint generator is properly connected
        assert semantics_with_registry.constraint_generator is not None
        assert semantics_with_registry.constraint_generator.semantics is semantics_with_registry

    def test_z3_function_compatibility(self, semantics_with_registry: WitnessSemantics) -> None:
        """Test that Z3 functions work with bit vector operations."""
        N = semantics_with_registry.N

        # Create test bit vectors
        state1 = z3.BitVecVal(1, N)
        state2 = z3.BitVecVal(2, N)

        # Test that functions can be called
        verify_result = semantics_with_registry.verify(state1, z3.Const('test_atom', syntactic.AtomSort))
        excludes_result = semantics_with_registry.excludes(state1, state2)

        assert isinstance(verify_result, z3.BoolRef)
        assert isinstance(excludes_result, z3.BoolRef)