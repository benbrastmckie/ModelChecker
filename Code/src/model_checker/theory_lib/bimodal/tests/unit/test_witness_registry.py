"""Tests for WitnessRegistry in BimodalSemantics.

Phase 2: Witness Registry for Modal Operators
Tests written BEFORE implementation following TDD methodology.
"""

import pytest
import z3
from model_checker.theory_lib.bimodal.semantic.witness_registry import WitnessRegistry
from model_checker.theory_lib.errors import WitnessRegistryError, WitnessPredicateError


@pytest.fixture
def registry():
    """Create WitnessRegistry instance for testing."""
    return WitnessRegistry(N=3, M=2)


class TestInitialization:
    """Tests for WitnessRegistry initialization."""

    def test_initialization_stores_parameters(self, registry):
        """Test that N and M are stored correctly."""
        assert registry.N == 3, "N should be stored"
        assert registry.M == 2, "M should be stored"

    def test_initialization_empty_dicts(self, registry):
        """Test that registries start empty."""
        assert registry.predicates == {}, "predicates dict should start empty"
        assert registry.formula_mapping == {}, "formula_mapping should start empty"
        assert registry._predicate_cache == {}, "cache should start empty"


class TestRegisterWitnessPredicate:
    """Tests for register_witness_predicate method."""

    def test_register_single_predicate(self, registry):
        """Test registering a single witness predicate."""
        formula_str = "Box_p"
        predicate = registry.register_witness_predicate(formula_str)

        # Should return a Z3 function
        assert isinstance(predicate, z3.FuncDeclRef), "Should return Z3 function"
        assert predicate.name() == f"{formula_str}_accessible_world", "Name should follow pattern"

    def test_register_predicate_signature(self, registry):
        """Test that predicate has correct signature: (Int, Int) → Int."""
        formula_str = "Box_p"
        predicate = registry.register_witness_predicate(formula_str)

        # Check arity (2 inputs)
        assert predicate.arity() == 2, "Should take 2 arguments (world, time)"

        # Check domain (Int, Int)
        assert predicate.domain(0) == z3.IntSort(), "First arg should be IntSort (world)"
        assert predicate.domain(1) == z3.IntSort(), "Second arg should be IntSort (time)"

        # Check range (Int)
        assert predicate.range() == z3.IntSort(), "Return type should be IntSort (world)"

    def test_register_predicate_naming_convention(self, registry):
        """Test that predicate names follow {formula}_accessible_world pattern."""
        formula_str = "Diamond_q"
        predicate = registry.register_witness_predicate(formula_str)

        expected_name = f"{formula_str}_accessible_world"
        assert predicate.name() == expected_name, f"Name should be {expected_name}"

    def test_register_multiple_formulas(self, registry):
        """Test registering multiple independent formulas."""
        formula1 = "Box_p"
        formula2 = "Box_q"

        pred1 = registry.register_witness_predicate(formula1)
        pred2 = registry.register_witness_predicate(formula2)

        # Should be different predicates
        assert pred1.name() != pred2.name(), "Different formulas should have different predicates"
        assert len(registry.predicates) == 2, "Should have 2 predicates registered"
        assert len(registry.formula_mapping) == 2, "Should have 2 formula mappings"

    def test_register_same_formula_twice_raises_error(self, registry):
        """Test that registering the same formula twice raises WitnessRegistryError."""
        formula_str = "Box_p"
        registry.register_witness_predicate(formula_str)

        # Second registration should raise error
        with pytest.raises(WitnessRegistryError) as exc_info:
            registry.register_witness_predicate(formula_str)

        assert "already registered" in str(exc_info.value).lower(), \
            "Error message should mention 'already registered'"

    def test_register_empty_formula_raises_error(self, registry):
        """Test that empty formula string raises WitnessPredicateError."""
        with pytest.raises(WitnessPredicateError):
            registry.register_witness_predicate("")

    def test_register_stores_in_all_structures(self, registry):
        """Test that registration updates all internal structures."""
        formula_str = "Box_p"
        predicate = registry.register_witness_predicate(formula_str)

        pred_name = f"{formula_str}_accessible_world"

        # Check predicates dict
        assert pred_name in registry.predicates, "Predicate should be in predicates dict"
        assert registry.predicates[pred_name] == predicate, "Stored predicate should match"

        # Check formula_mapping
        assert formula_str in registry.formula_mapping, "Formula should be in mapping"
        assert pred_name in registry.formula_mapping[formula_str], "Predicate name should be in formula's set"

        # Check cache
        assert formula_str in registry._predicate_cache, "Formula should be cached"
        assert registry._predicate_cache[formula_str] == predicate, "Cached predicate should match"


class TestGetWitnessPredicate:
    """Tests for get_witness_predicate retrieval."""

    def test_get_registered_predicate(self, registry):
        """Test retrieving a registered predicate."""
        formula_str = "Box_p"
        registered = registry.register_witness_predicate(formula_str)

        retrieved = registry.get_witness_predicate(formula_str)

        assert retrieved == registered, "Retrieved predicate should match registered"

    def test_get_predicate_uses_cache(self, registry):
        """Test that second retrieval uses cache."""
        formula_str = "Box_p"
        registry.register_witness_predicate(formula_str)

        # First call
        first = registry.get_witness_predicate(formula_str)

        # Second call should use cache
        second = registry.get_witness_predicate(formula_str)

        assert first == second, "Both calls should return same predicate"
        assert formula_str in registry._predicate_cache, "Should be in cache"

    def test_get_unregistered_predicate_raises_error(self, registry):
        """Test that getting unregistered predicate raises WitnessPredicateError."""
        with pytest.raises(WitnessPredicateError) as exc_info:
            registry.get_witness_predicate("nonexistent_formula")

        assert "retrieval" in str(exc_info.value).lower() or "not" in str(exc_info.value).lower(), \
            "Error should mention retrieval failure"


class TestHasWitnessPredicate:
    """Tests for has_witness_predicate check."""

    def test_has_predicate_existing_returns_true(self, registry):
        """Test that has_witness_predicate returns True for registered formula."""
        formula_str = "Box_p"
        registry.register_witness_predicate(formula_str)

        assert registry.has_witness_predicate(formula_str) is True, \
            "Should return True for registered formula"

    def test_has_predicate_nonexistent_returns_false(self, registry):
        """Test that has_witness_predicate returns False for unregistered formula."""
        assert registry.has_witness_predicate("nonexistent") is False, \
            "Should return False for unregistered formula"

    def test_has_predicate_no_error(self, registry):
        """Test that has_witness_predicate doesn't raise error for nonexistent formula."""
        # Should not raise any exception
        try:
            result = registry.has_witness_predicate("nonexistent")
            assert result is False, "Should return False, not raise error"
        except Exception as e:
            pytest.fail(f"has_witness_predicate should not raise error, got {e}")


class TestGetAllPredicates:
    """Tests for get_all_predicates method."""

    def test_get_all_predicates_empty(self, registry):
        """Test get_all_predicates on empty registry."""
        all_preds = registry.get_all_predicates()

        assert all_preds == {}, "Should return empty dict for empty registry"

    def test_get_all_predicates_returns_copy(self, registry):
        """Test that get_all_predicates returns a copy, not reference."""
        formula_str = "Box_p"
        registry.register_witness_predicate(formula_str)

        all_preds = registry.get_all_predicates()

        # Modify returned dict
        all_preds["new_key"] = "new_value"

        # Original should be unchanged
        assert "new_key" not in registry.predicates, \
            "Modifying returned dict should not affect internal registry"

    def test_get_all_predicates_contents(self, registry):
        """Test that get_all_predicates contains registered predicates."""
        formula1 = "Box_p"
        formula2 = "Diamond_q"

        pred1 = registry.register_witness_predicate(formula1)
        pred2 = registry.register_witness_predicate(formula2)

        all_preds = registry.get_all_predicates()

        assert len(all_preds) == 2, "Should have 2 predicates"
        assert f"{formula1}_accessible_world" in all_preds, "Should contain first predicate"
        assert f"{formula2}_accessible_world" in all_preds, "Should contain second predicate"


class TestClear:
    """Tests for clear method."""

    def test_clear_empties_all_structures(self, registry):
        """Test that clear() empties all internal structures."""
        # Register some predicates
        registry.register_witness_predicate("Box_p")
        registry.register_witness_predicate("Diamond_q")

        # Verify they're registered
        assert len(registry.predicates) > 0
        assert len(registry.formula_mapping) > 0
        assert len(registry._predicate_cache) > 0

        # Clear
        registry.clear()

        # Verify all empty
        assert registry.predicates == {}, "predicates should be empty after clear"
        assert registry.formula_mapping == {}, "formula_mapping should be empty after clear"
        assert registry._predicate_cache == {}, "cache should be empty after clear"

    def test_clear_allows_reregistration(self, registry):
        """Test that after clear(), formulas can be registered again."""
        formula_str = "Box_p"

        # Register, clear, register again
        registry.register_witness_predicate(formula_str)
        registry.clear()

        # Should not raise error
        try:
            registry.register_witness_predicate(formula_str)
        except WitnessRegistryError:
            pytest.fail("Should allow re-registration after clear()")
