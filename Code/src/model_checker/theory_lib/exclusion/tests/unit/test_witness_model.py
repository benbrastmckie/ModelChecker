"""
Unit tests for exclusion witness model implementation.

Tests the WitnessAwareModel class functionality including
witness predicate access and Z3 model evaluation.
"""

import pytest
import z3
from unittest.mock import Mock, MagicMock, patch
from typing import Dict

from model_checker.theory_lib.exclusion.semantic.model import WitnessAwareModel


class TestWitnessAwareModel:
    """Test the WitnessAwareModel class."""

    @pytest.fixture
    def mock_z3_model(self) -> Mock:
        """Create a mock Z3 model for testing."""
        mock_model = Mock(spec=z3.ModelRef)
        mock_model.eval = Mock(return_value=z3.BitVecVal(1, 3))
        return mock_model

    @pytest.fixture
    def mock_semantics(self) -> Mock:
        """Create a mock semantics object for testing."""
        mock_semantics = Mock()
        mock_semantics.N = 3
        return mock_semantics

    @pytest.fixture
    def sample_witness_predicates(self) -> Dict[str, z3.FuncDeclRef]:
        """Create sample witness predicates for testing."""
        return {
            "test_formula_h": z3.Function("test_formula_h", z3.BitVecSort(3), z3.BitVecSort(3)),
            "test_formula_y": z3.Function("test_formula_y", z3.BitVecSort(3), z3.BitVecSort(3)),
            "another_formula_h": z3.Function("another_formula_h", z3.BitVecSort(3), z3.BitVecSort(3)),
        }

    @pytest.fixture
    def witness_model(self, mock_z3_model: Mock, mock_semantics: Mock,
                     sample_witness_predicates: Dict[str, z3.FuncDeclRef]) -> WitnessAwareModel:
        """Create a WitnessAwareModel instance for testing."""
        return WitnessAwareModel(mock_z3_model, mock_semantics, sample_witness_predicates)

    def test_initialization(self, witness_model: WitnessAwareModel, mock_z3_model: Mock,
                           mock_semantics: Mock, sample_witness_predicates: Dict[str, z3.FuncDeclRef]) -> None:
        """Test that WitnessAwareModel initializes correctly."""
        assert witness_model.z3_model is mock_z3_model
        assert witness_model.semantics is mock_semantics
        assert witness_model.witness_predicates == sample_witness_predicates
        assert isinstance(witness_model._cache, dict)
        assert len(witness_model._cache) == 0

    def test_eval_method(self, witness_model: WitnessAwareModel) -> None:
        """Test that eval method delegates to Z3 model."""
        test_expr = z3.BitVecVal(1, 3)
        result = witness_model.eval(test_expr)

        witness_model.z3_model.eval.assert_called_once_with(test_expr)
        assert result == z3.BitVecVal(1, 3)

    def test_has_witness_for_existing_formula(self, witness_model: WitnessAwareModel) -> None:
        """Test has_witness_for returns True for existing formula."""
        assert witness_model.has_witness_for("test_formula") is True
        assert witness_model.has_witness_for("another_formula") is True

    def test_has_witness_for_non_existing_formula(self, witness_model: WitnessAwareModel) -> None:
        """Test has_witness_for returns False for non-existing formula."""
        assert witness_model.has_witness_for("nonexistent_formula") is False

    def test_get_h_witness_existing_predicate(self, witness_model: WitnessAwareModel) -> None:
        """Test get_h_witness for existing predicate."""
        # Mock the Z3 evaluation to return a bit vector value
        mock_result = Mock()
        mock_result.__bool__ = Mock(return_value=True)  # Make z3.is_bv_value return True
        mock_result.as_long = Mock(return_value=5)

        # Configure the mock to simulate z3.is_bv_value returning True
        with patch('z3.is_bv_value', return_value=True):
            witness_model.z3_model.eval.return_value = mock_result

            result = witness_model.get_h_witness("test_formula", 1)
            assert result == 5

    def test_get_h_witness_non_existing_predicate(self, witness_model: WitnessAwareModel) -> None:
        """Test get_h_witness returns None for non-existing predicate."""
        result = witness_model.get_h_witness("nonexistent_formula", 1)
        assert result is None

    def test_get_h_witness_with_invalid_result(self, witness_model: WitnessAwareModel) -> None:
        """Test get_h_witness returns None when Z3 evaluation fails."""
        # Mock Z3 evaluation to return non-bit-vector value
        witness_model.z3_model.eval.return_value = Mock()

        with patch('z3.is_bv_value', return_value=False):
            result = witness_model.get_h_witness("test_formula", 1)
            assert result is None

    def test_get_y_witness_existing_predicate(self, witness_model: WitnessAwareModel) -> None:
        """Test get_y_witness for existing predicate."""
        # Mock the Z3 evaluation to return a bit vector value
        mock_result = Mock()
        mock_result.__bool__ = Mock(return_value=True)  # Make z3.is_bv_value return True
        mock_result.as_long = Mock(return_value=7)

        # Configure the mock to simulate z3.is_bv_value returning True
        with patch('z3.is_bv_value', return_value=True):
            witness_model.z3_model.eval.return_value = mock_result

            result = witness_model.get_y_witness("test_formula", 2)
            assert result == 7

    def test_get_y_witness_non_existing_predicate(self, witness_model: WitnessAwareModel) -> None:
        """Test get_y_witness returns None for non-existing predicate."""
        result = witness_model.get_y_witness("nonexistent_formula", 1)
        assert result is None

    def test_witness_predicate_names_format(self, witness_model: WitnessAwareModel) -> None:
        """Test that witness predicate names follow expected format."""
        # Check that predicates follow the formula_h and formula_y naming convention
        expected_h_names = {"test_formula_h", "another_formula_h"}
        expected_y_names = {"test_formula_y"}

        actual_h_names = {name for name in witness_model.witness_predicates.keys() if name.endswith("_h")}
        actual_y_names = {name for name in witness_model.witness_predicates.keys() if name.endswith("_y")}

        assert actual_h_names == expected_h_names
        assert actual_y_names == expected_y_names

    def test_cache_initialization(self, witness_model: WitnessAwareModel) -> None:
        """Test that cache is properly initialized and accessible."""
        assert hasattr(witness_model, '_cache')
        assert isinstance(witness_model._cache, dict)
        assert len(witness_model._cache) == 0

    def test_z3_bitvec_val_creation(self, witness_model: WitnessAwareModel) -> None:
        """Test that Z3 BitVecVal can be created with semantics N parameter."""
        N = witness_model.semantics.N
        state_bv = z3.BitVecVal(1, N)

        assert isinstance(state_bv, z3.BitVecNumRef)
        assert state_bv.size() == N

    def test_witness_predicate_call_integration(self, witness_model: WitnessAwareModel) -> None:
        """Test that witness predicates can be called with bit vector arguments."""
        h_pred = witness_model.witness_predicates["test_formula_h"]
        state_bv = z3.BitVecVal(1, witness_model.semantics.N)

        # This should not raise an exception
        result_expr = h_pred(state_bv)
        assert isinstance(result_expr, z3.ExprRef)


class TestWitnessAwareModelIntegration:
    """Integration tests for WitnessAwareModel with real Z3 components."""

    @pytest.fixture
    def real_z3_model(self) -> z3.ModelRef:
        """Create a real Z3 model for integration testing."""
        solver = z3.Solver()

        # Create simple constraints to get a satisfiable model
        x = z3.BitVec("x", 3)
        solver.add(x == 1)

        assert solver.check() == z3.sat
        return solver.model()

    @pytest.fixture
    def real_semantics(self) -> Mock:
        """Create a real-like semantics object."""
        semantics = Mock()
        semantics.N = 3
        return semantics

    @pytest.fixture
    def real_witness_predicates(self) -> Dict[str, z3.FuncDeclRef]:
        """Create real Z3 function declarations for witness predicates."""
        return {
            "A_h": z3.Function("A_h", z3.BitVecSort(3), z3.BitVecSort(3)),
            "A_y": z3.Function("A_y", z3.BitVecSort(3), z3.BitVecSort(3)),
        }

    def test_real_z3_integration(self, real_z3_model: z3.ModelRef, real_semantics: Mock,
                                real_witness_predicates: Dict[str, z3.FuncDeclRef]) -> None:
        """Test WitnessAwareModel with real Z3 components."""
        model = WitnessAwareModel(real_z3_model, real_semantics, real_witness_predicates)

        # Test that the model can be created and basic methods work
        assert model.has_witness_for("A") is True
        assert model.has_witness_for("B") is False

        # Test that eval works with real Z3 model
        test_expr = z3.BitVecVal(1, 3)
        result = model.eval(test_expr)
        assert result is not None

    def test_witness_function_evaluation(self, real_z3_model: z3.ModelRef, real_semantics: Mock) -> None:
        """Test evaluation of witness functions with constrained model."""
        # Create a solver with constraints on witness functions
        solver = z3.Solver()

        # Define witness functions
        A_h = z3.Function("A_h", z3.BitVecSort(3), z3.BitVecSort(3))
        A_y = z3.Function("A_y", z3.BitVecSort(3), z3.BitVecSort(3))

        # Add constraints: A_h(1) = 2, A_y(1) = 3
        solver.add(A_h(z3.BitVecVal(1, 3)) == z3.BitVecVal(2, 3))
        solver.add(A_y(z3.BitVecVal(1, 3)) == z3.BitVecVal(3, 3))

        assert solver.check() == z3.sat
        constrained_model = solver.model()

        witness_predicates = {"A_h": A_h, "A_y": A_y}
        model = WitnessAwareModel(constrained_model, real_semantics, witness_predicates)

        # Test witness evaluation
        h_result = model.get_h_witness("A", 1)
        y_result = model.get_y_witness("A", 1)

        assert h_result == 2
        assert y_result == 3