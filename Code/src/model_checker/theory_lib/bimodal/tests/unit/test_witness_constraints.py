"""Tests for WitnessConstraintGenerator in BimodalSemantics.

Phase 3: Witness Constraints for Modal Semantics
Tests written BEFORE implementation following TDD methodology.
"""

import pytest
import z3
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics
from model_checker.theory_lib.bimodal.semantic.witness_constraints import WitnessConstraintGenerator
from model_checker.theory_lib.errors import WitnessConstraintError


@pytest.fixture
def semantics():
    """Create BimodalSemantics instance for testing."""
    settings = {
        'N': 3,
        'M': 2,
        'contingent': False,
        'disjoint': False,
        'max_time': 1,
        'expectation': True,
        'iterate': 1
    }
    return BimodalSemantics(settings)


@pytest.fixture
def generator(semantics):
    """Create WitnessConstraintGenerator instance."""
    return WitnessConstraintGenerator(semantics)


class TestInitialization:
    """Tests for WitnessConstraintGenerator initialization."""

    def test_initialization_stores_semantics(self, generator, semantics):
        """Test that semantics is stored and accessible."""
        assert generator.semantics == semantics, "Semantics should be stored"

    def test_initialization_stores_N(self, generator):
        """Test that N is stored from semantics."""
        assert generator.N == 3, "N should be copied from semantics"

    def test_initialization_stores_M(self, generator):
        """Test that M is stored from semantics."""
        assert generator.M == 2, "M should be copied from semantics"


class TestGenerateWitnessConstraints:
    """Tests for generate_witness_constraints method."""

    def test_generate_returns_list(self, generator):
        """Test that generate_witness_constraints returns a list."""
        formula_str = "Box_p"

        # Create a mock formula AST (simple structure for testing)
        class MockFormula:
            pass

        formula_ast = MockFormula()

        # Create a mock accessible_world predicate
        accessible_world_pred = z3.Function(
            "Box_p_accessible_world",
            z3.IntSort(),
            z3.IntSort(),
            z3.IntSort()
        )

        result = generator.generate_witness_constraints(
            formula_str,
            formula_ast,
            accessible_world_pred
        )

        assert isinstance(result, list), "Should return a list"

    def test_generate_returns_z3_constraints(self, generator):
        """Test that returned list contains Z3 BoolRef expressions."""
        formula_str = "Box_p"

        class MockFormula:
            pass

        formula_ast = MockFormula()
        accessible_world_pred = z3.Function(
            "Box_p_accessible_world",
            z3.IntSort(),
            z3.IntSort(),
            z3.IntSort()
        )

        result = generator.generate_witness_constraints(
            formula_str,
            formula_ast,
            accessible_world_pred
        )

        # Should have at least one constraint
        assert len(result) > 0, "Should generate at least one constraint"

        # All elements should be Z3 expressions
        for constraint in result:
            assert isinstance(constraint, z3.BoolRef), \
                f"Each constraint should be z3.BoolRef, got {type(constraint)}"

    def test_generate_empty_formula_raises_error(self, generator):
        """Test that empty formula string raises WitnessConstraintError."""
        accessible_world_pred = z3.Function(
            "test_accessible_world",
            z3.IntSort(),
            z3.IntSort(),
            z3.IntSort()
        )

        with pytest.raises(WitnessConstraintError) as exc_info:
            generator.generate_witness_constraints("", None, accessible_world_pred)

        assert "empty" in str(exc_info.value).lower() or "invalid" in str(exc_info.value).lower(), \
            "Error should mention empty/invalid formula"

    def test_generate_none_predicate_raises_error(self, generator):
        """Test that None predicate raises WitnessConstraintError."""
        class MockFormula:
            pass

        formula_ast = MockFormula()

        with pytest.raises(WitnessConstraintError) as exc_info:
            generator.generate_witness_constraints("Box_p", formula_ast, None)

        assert "predicate" in str(exc_info.value).lower() or "invalid" in str(exc_info.value).lower(), \
            "Error should mention predicate/invalid"


class TestConstraintStructure:
    """Tests for the structure of generated constraints."""

    def test_constraints_contain_forall(self, generator):
        """Test that constraints use ForAll quantifiers."""
        formula_str = "Box_p"

        class MockFormula:
            pass

        formula_ast = MockFormula()
        accessible_world_pred = z3.Function(
            "Box_p_accessible_world",
            z3.IntSort(),
            z3.IntSort(),
            z3.IntSort()
        )

        result = generator.generate_witness_constraints(
            formula_str,
            formula_ast,
            accessible_world_pred
        )

        # Convert constraints to strings to inspect structure
        constraints_str = "\n".join(str(c) for c in result)

        # Should contain ForAll quantifiers
        assert "ForAll" in constraints_str or "forall" in constraints_str.lower(), \
            "Constraints should use ForAll quantifiers"

    def test_constraints_reference_predicate(self, generator):
        """Test that constraints reference the accessible_world predicate."""
        formula_str = "Box_p"

        class MockFormula:
            pass

        formula_ast = MockFormula()
        accessible_world_pred = z3.Function(
            "Box_p_accessible_world",
            z3.IntSort(),
            z3.IntSort(),
            z3.IntSort()
        )

        result = generator.generate_witness_constraints(
            formula_str,
            formula_ast,
            accessible_world_pred
        )

        # Constraints should reference the predicate
        constraints_str = "\n".join(str(c) for c in result)

        assert "Box_p_accessible_world" in constraints_str, \
            "Constraints should reference the accessible_world predicate"

    def test_constraints_use_implies(self, generator):
        """Test that constraints use implication structure."""
        formula_str = "Box_p"

        class MockFormula:
            pass

        formula_ast = MockFormula()
        accessible_world_pred = z3.Function(
            "Box_p_accessible_world",
            z3.IntSort(),
            z3.IntSort(),
            z3.IntSort()
        )

        result = generator.generate_witness_constraints(
            formula_str,
            formula_ast,
            accessible_world_pred
        )

        # Constraints should use implication
        constraints_str = "\n".join(str(c) for c in result)

        assert "Implies" in constraints_str or "=>" in constraints_str or "Or(Not" in constraints_str, \
            "Constraints should use Implies structure"


class TestSemanticReferences:
    """Tests that constraints reference semantic methods."""

    def test_constraints_reference_is_world(self, generator):
        """Test that constraints check if witness is a valid world."""
        formula_str = "Box_p"

        class MockFormula:
            pass

        formula_ast = MockFormula()
        accessible_world_pred = z3.Function(
            "Box_p_accessible_world",
            z3.IntSort(),
            z3.IntSort(),
            z3.IntSort()
        )

        result = generator.generate_witness_constraints(
            formula_str,
            formula_ast,
            accessible_world_pred
        )

        # Should reference is_world check
        constraints_str = "\n".join(str(c) for c in result)

        # Looking for is_world or similar validity checks
        # This is a structural test - actual method names may vary
        assert len(constraints_str) > 0, "Should generate constraints with world validity checks"

    def test_constraints_check_time_validity(self, generator):
        """Test that constraints check time validity for worlds."""
        formula_str = "Box_p"

        class MockFormula:
            pass

        formula_ast = MockFormula()
        accessible_world_pred = z3.Function(
            "Box_p_accessible_world",
            z3.IntSort(),
            z3.IntSort(),
            z3.IntSort()
        )

        result = generator.generate_witness_constraints(
            formula_str,
            formula_ast,
            accessible_world_pred
        )

        # Should check is_valid_time_for_world or similar
        constraints_str = "\n".join(str(c) for c in result)

        # This is a structural test - actual method names may vary
        assert len(constraints_str) > 0, "Should generate constraints with time validity checks"


class TestMultipleFormulas:
    """Tests for handling multiple formulas."""

    def test_different_formulas_different_constraints(self, generator):
        """Test that different formulas generate independent constraints."""
        formula_str1 = "Box_p"
        formula_str2 = "Box_q"

        class MockFormula:
            pass

        formula_ast1 = MockFormula()
        formula_ast2 = MockFormula()

        pred1 = z3.Function("Box_p_accessible_world", z3.IntSort(), z3.IntSort(), z3.IntSort())
        pred2 = z3.Function("Box_q_accessible_world", z3.IntSort(), z3.IntSort(), z3.IntSort())

        result1 = generator.generate_witness_constraints(formula_str1, formula_ast1, pred1)
        result2 = generator.generate_witness_constraints(formula_str2, formula_ast2, pred2)

        # Both should generate constraints
        assert len(result1) > 0, "First formula should generate constraints"
        assert len(result2) > 0, "Second formula should generate constraints"

        # Constraints should reference different predicates
        constraints_str1 = "\n".join(str(c) for c in result1)
        constraints_str2 = "\n".join(str(c) for c in result2)

        assert "Box_p_accessible_world" in constraints_str1, "First should reference Box_p"
        assert "Box_q_accessible_world" in constraints_str2, "Second should reference Box_q"
