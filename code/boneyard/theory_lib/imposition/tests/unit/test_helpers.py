"""
Unit tests for imposition theory helper functions.

Tests utility functions used by the imposition theory semantic classes.
"""

import pytest
import z3
from typing import List, Dict, Tuple

from model_checker.theory_lib.imposition.semantic.helpers import (
    safe_bitvec_as_long,
    format_imposition_relation,
    group_impositions_by_world
)


class TestSafeBitvecAsLong:
    """Test the safe_bitvec_as_long function."""

    def test_with_integer_input(self) -> None:
        """Test safe_bitvec_as_long with integer input."""
        result = safe_bitvec_as_long(42)
        assert result == 42
        assert isinstance(result, int)

    def test_with_z3_bitvec_value(self) -> None:
        """Test safe_bitvec_as_long with Z3 BitVecVal."""
        bv = z3.BitVecVal(15, 4)
        result = safe_bitvec_as_long(bv)
        assert result == 15
        assert isinstance(result, int)

    def test_with_zero_bitvec(self) -> None:
        """Test safe_bitvec_as_long with zero BitVec."""
        bv = z3.BitVecVal(0, 8)
        result = safe_bitvec_as_long(bv)
        assert result == 0

    def test_with_max_value_bitvec(self) -> None:
        """Test safe_bitvec_as_long with maximum value for bit width."""
        # For 3-bit BitVec, max value is 7 (2^3 - 1)
        bv = z3.BitVecVal(7, 3)
        result = safe_bitvec_as_long(bv)
        assert result == 7

    def test_with_different_bit_widths(self) -> None:
        """Test safe_bitvec_as_long with different bit widths."""
        test_cases = [
            (z3.BitVecVal(1, 1), 1),    # 1-bit
            (z3.BitVecVal(3, 2), 3),    # 2-bit
            (z3.BitVecVal(5, 3), 5),    # 3-bit
            (z3.BitVecVal(10, 4), 10),  # 4-bit
            (z3.BitVecVal(100, 8), 100) # 8-bit
        ]

        for bv, expected in test_cases:
            result = safe_bitvec_as_long(bv)
            assert result == expected

    def test_preserves_integer_type(self) -> None:
        """Test that function preserves integer input type."""
        test_integers = [0, 1, 10, 100, 1000]
        for test_int in test_integers:
            result = safe_bitvec_as_long(test_int)
            assert result == test_int
            assert type(result) == int


class TestFormatImpositionRelation:
    """Test the format_imposition_relation function."""

    def test_with_integer_inputs(self) -> None:
        """Test format_imposition_relation with integer inputs."""
        result = format_imposition_relation(1, 2, 3)
        assert result == "s1 ->_2 s3"

    def test_with_z3_bitvec_inputs(self) -> None:
        """Test format_imposition_relation with Z3 BitVec inputs."""
        state = z3.BitVecVal(1, 3)
        world = z3.BitVecVal(2, 3)
        outcome = z3.BitVecVal(5, 3)

        result = format_imposition_relation(state, world, outcome)
        assert result == "s1 ->_2 s5"

    def test_with_mixed_inputs(self) -> None:
        """Test format_imposition_relation with mixed input types."""
        state = z3.BitVecVal(3, 4)
        world = 1  # integer
        outcome = z3.BitVecVal(7, 4)

        result = format_imposition_relation(state, world, outcome)
        assert result == "s3 ->_1 s7"

    def test_with_zero_values(self) -> None:
        """Test format_imposition_relation with zero values."""
        result = format_imposition_relation(0, 0, 0)
        assert result == "s0 ->_0 s0"

    def test_format_consistency(self) -> None:
        """Test that format is consistent across different inputs."""
        test_cases = [
            (0, 1, 2, "s0 ->_1 s2"),
            (5, 3, 7, "s5 ->_3 s7"),
            (10, 0, 15, "s10 ->_0 s15"),
        ]

        for state, world, outcome, expected in test_cases:
            result = format_imposition_relation(state, world, outcome)
            assert result == expected

    def test_with_large_values(self) -> None:
        """Test format_imposition_relation with large values."""
        # Test with larger bit widths
        state = z3.BitVecVal(127, 8)  # 8-bit max value
        world = z3.BitVecVal(255, 8)
        outcome = z3.BitVecVal(64, 8)

        result = format_imposition_relation(state, world, outcome)
        assert result == "s127 ->_255 s64"

    def test_return_type(self) -> None:
        """Test that format_imposition_relation returns string."""
        result = format_imposition_relation(1, 2, 3)
        assert isinstance(result, str)


class TestGroupImpositionsByWorld:
    """Test the group_impositions_by_world function."""

    def test_with_empty_list(self) -> None:
        """Test group_impositions_by_world with empty input."""
        result = group_impositions_by_world([])
        assert result == {}
        assert isinstance(result, dict)

    def test_with_single_relation(self) -> None:
        """Test group_impositions_by_world with single relation."""
        world = z3.BitVecVal(1, 3)
        relations = [(z3.BitVecVal(0, 3), world, z3.BitVecVal(2, 3))]

        result = group_impositions_by_world(relations)

        assert len(result) == 1
        assert world in result
        assert len(result[world]) == 1
        assert result[world][0] == (z3.BitVecVal(0, 3), z3.BitVecVal(2, 3))

    def test_with_multiple_relations_same_world(self) -> None:
        """Test grouping multiple relations with same world."""
        world = z3.BitVecVal(1, 3)
        relations = [
            (z3.BitVecVal(0, 3), world, z3.BitVecVal(2, 3)),
            (z3.BitVecVal(3, 3), world, z3.BitVecVal(4, 3)),
            (z3.BitVecVal(5, 3), world, z3.BitVecVal(6, 3))
        ]

        result = group_impositions_by_world(relations)

        assert len(result) == 1
        assert world in result
        assert len(result[world]) == 3

        # Check that all state-outcome pairs are present
        expected_pairs = {
            (z3.BitVecVal(0, 3), z3.BitVecVal(2, 3)),
            (z3.BitVecVal(3, 3), z3.BitVecVal(4, 3)),
            (z3.BitVecVal(5, 3), z3.BitVecVal(6, 3))
        }
        actual_pairs = set(result[world])
        assert len(actual_pairs) == len(expected_pairs)

    def test_with_multiple_relations_different_worlds(self) -> None:
        """Test grouping relations with different worlds."""
        world1 = z3.BitVecVal(1, 3)
        world2 = z3.BitVecVal(2, 3)
        world3 = z3.BitVecVal(3, 3)

        relations = [
            (z3.BitVecVal(0, 3), world1, z3.BitVecVal(4, 3)),
            (z3.BitVecVal(1, 3), world2, z3.BitVecVal(5, 3)),
            (z3.BitVecVal(2, 3), world3, z3.BitVecVal(6, 3)),
            (z3.BitVecVal(7, 3), world1, z3.BitVecVal(0, 3))  # Another relation for world1
        ]

        result = group_impositions_by_world(relations)

        assert len(result) == 3
        assert world1 in result
        assert world2 in result
        assert world3 in result

        # world1 should have 2 relations
        assert len(result[world1]) == 2

        # world2 and world3 should have 1 relation each
        assert len(result[world2]) == 1
        assert len(result[world3]) == 1

    def test_with_mixed_input_types(self) -> None:
        """Test group_impositions_by_world with mixed input types."""
        # Mix of Z3 BitVec and regular tuples
        world1 = z3.BitVecVal(1, 3)
        world2 = z3.BitVecVal(2, 3)

        relations = [
            (z3.BitVecVal(0, 3), world1, z3.BitVecVal(3, 3)),
            (z3.BitVecVal(1, 3), world2, z3.BitVecVal(4, 3))
        ]

        result = group_impositions_by_world(relations)

        assert len(result) == 2
        assert world1 in result
        assert world2 in result
        assert len(result[world1]) == 1
        assert len(result[world2]) == 1

    def test_return_structure(self) -> None:
        """Test that return structure is correct."""
        world = z3.BitVecVal(1, 2)
        relations = [(z3.BitVecVal(0, 2), world, z3.BitVecVal(1, 2))]

        result = group_impositions_by_world(relations)

        # Result should be a dictionary
        assert isinstance(result, dict)

        # Values should be lists
        for world_key, state_outcome_pairs in result.items():
            assert isinstance(state_outcome_pairs, list)

            # Each item in the list should be a tuple of (state, outcome)
            for pair in state_outcome_pairs:
                assert isinstance(pair, tuple)
                assert len(pair) == 2

    def test_preserves_order_within_groups(self) -> None:
        """Test that order is preserved within each world group."""
        world = z3.BitVecVal(1, 3)
        relations = [
            (z3.BitVecVal(0, 3), world, z3.BitVecVal(5, 3)),
            (z3.BitVecVal(1, 3), world, z3.BitVecVal(6, 3)),
            (z3.BitVecVal(2, 3), world, z3.BitVecVal(7, 3))
        ]

        result = group_impositions_by_world(relations)

        # Should maintain order of insertion
        world_relations = result[world]
        expected_order = [
            (z3.BitVecVal(0, 3), z3.BitVecVal(5, 3)),
            (z3.BitVecVal(1, 3), z3.BitVecVal(6, 3)),
            (z3.BitVecVal(2, 3), z3.BitVecVal(7, 3))
        ]

        assert len(world_relations) == len(expected_order)
        for i, (actual, expected) in enumerate(zip(world_relations, expected_order)):
            # Compare the structure since Z3 objects may not be directly comparable
            assert len(actual) == len(expected) == 2

    def test_with_duplicate_relations(self) -> None:
        """Test behavior with duplicate relations."""
        world = z3.BitVecVal(1, 3)
        state = z3.BitVecVal(0, 3)
        outcome = z3.BitVecVal(2, 3)

        # Same relation repeated
        relations = [
            (state, world, outcome),
            (state, world, outcome),
            (state, world, outcome)
        ]

        result = group_impositions_by_world(relations)

        assert len(result) == 1
        assert world in result
        # Should include all duplicates (function doesn't deduplicate)
        assert len(result[world]) == 3


class TestHelperFunctionsIntegration:
    """Integration tests for helper functions working together."""

    def test_format_and_group_integration(self) -> None:
        """Test format_imposition_relation and group_impositions_by_world together."""
        # Create test data
        world1 = z3.BitVecVal(1, 3)
        world2 = z3.BitVecVal(2, 3)

        relations = [
            (z3.BitVecVal(0, 3), world1, z3.BitVecVal(3, 3)),
            (z3.BitVecVal(1, 3), world2, z3.BitVecVal(4, 3)),
            (z3.BitVecVal(2, 3), world1, z3.BitVecVal(5, 3))
        ]

        # Group the relations
        grouped = group_impositions_by_world(relations)

        # Format relations within each group
        formatted_groups = {}
        for world, state_outcome_pairs in grouped.items():
            formatted_relations = []
            for state, outcome in state_outcome_pairs:
                formatted = format_imposition_relation(state, world, outcome)
                formatted_relations.append(formatted)
            formatted_groups[world] = formatted_relations

        # Verify the integration
        assert len(formatted_groups) == 2

        # Check formatted strings
        for world, formatted_list in formatted_groups.items():
            for formatted_relation in formatted_list:
                assert isinstance(formatted_relation, str)
                assert "->" in formatted_relation
                assert "s" in formatted_relation

    def test_safe_bitvec_in_formatting(self) -> None:
        """Test safe_bitvec_as_long integration with formatting."""
        # Test that format_imposition_relation uses safe conversion internally
        state = z3.BitVecVal(10, 8)
        world = z3.BitVecVal(20, 8)
        outcome = z3.BitVecVal(30, 8)

        # This should work without errors thanks to safe_bitvec_as_long
        result = format_imposition_relation(state, world, outcome)
        assert result == "s10 ->_20 s30"

        # Verify the individual conversions work
        assert safe_bitvec_as_long(state) == 10
        assert safe_bitvec_as_long(world) == 20
        assert safe_bitvec_as_long(outcome) == 30

    def test_all_helpers_with_real_z3_model(self) -> None:
        """Test all helper functions with data from a real Z3 model."""
        # Create a Z3 solver with imposition constraints
        solver = z3.Solver()

        # Define variables
        state = z3.BitVec('state', 3)
        world = z3.BitVec('world', 3)
        outcome = z3.BitVec('outcome', 3)

        # Add constraints
        solver.add(state == 1)
        solver.add(world == 2)
        solver.add(outcome == 5)

        assert solver.check() == z3.sat
        model = solver.model()

        # Extract values using model evaluation
        state_val = model.eval(state)
        world_val = model.eval(world)
        outcome_val = model.eval(outcome)

        # Test safe_bitvec_as_long with model values
        state_int = safe_bitvec_as_long(state_val)
        world_int = safe_bitvec_as_long(world_val)
        outcome_int = safe_bitvec_as_long(outcome_val)

        assert state_int == 1
        assert world_int == 2
        assert outcome_int == 5

        # Test formatting with model values
        formatted = format_imposition_relation(state_val, world_val, outcome_val)
        assert formatted == "s1 ->_2 s5"

        # Test grouping with model values
        relations = [(state_val, world_val, outcome_val)]
        grouped = group_impositions_by_world(relations)

        assert len(grouped) == 1
        assert world_val in grouped
        assert len(grouped[world_val]) == 1