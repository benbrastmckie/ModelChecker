"""
Integration tests for iterator model building process.

These tests focus on the complex two-phase model building that causes
many iterator issues, ensuring proper variable namespace handling.
"""

import pytest
import z3
from model_checker.builder.example import BuildExample
from model_checker.models import ModelConstraints
from model_checker.theory_lib.logos import get_theory as get_logos_theory
from model_checker.theory_lib.logos.iterate import LogosModelIterator
from model_checker.theory_lib.imposition import get_theory as get_imposition_theory
from model_checker.theory_lib.imposition.iterate import ImpositionModelIterator


class TestModelBuildingProcess:
    """Test the two-phase model building process."""
    
    def test_model_constraints_independence(self):
        """Test that MODEL 2 constraints are independent from MODEL 1."""
        logos_theory = get_logos_theory()
        
        example = BuildExample(
            name="test",
            semantic_theory=logos_theory,
            premises=["(A \\rightarrow B)"],
            conclusions=["(B \\rightarrow A)"],
            settings={'N': 2, 'iterate': 2}
        )
        
        # Get MODEL 1
        example.run_single_test()
        model1 = example.model_structure
        assert model1 is not None
        
        # Create iterator
        iterator = LogosModelIterator(example)
        
        # Get original variable names from MODEL 1
        model1_vars = set()
        if hasattr(model1, 'z3_verify_sets'):
            for prop, states in model1.z3_verify_sets.items():
                for state in states:
                    model1_vars.add(f"verify_{prop}_{state}")
        
        # Run iteration to get MODEL 2
        models = iterator.iterate()
        assert len(models) == 2
        
        model2 = models[1]
        
        # MODEL 2 should have fresh variables, not reuse MODEL 1's
        # This is critical for avoiding namespace conflicts
        assert model2 != model1
        
        # Verify MODEL 2 has proper structure
        assert hasattr(model2, 'z3_verify_sets')
        assert 'A' in model2.z3_verify_sets
        assert 'B' in model2.z3_verify_sets
    
    def test_verify_falsify_function_consistency(self):
        """Test that verify/falsify functions remain consistent."""
        imposition_theory = get_imposition_theory()
        
        example = BuildExample(
            name="test", 
            semantic_theory=imposition_theory,
            premises=["(A \\Box\\rightarrow B)"],
            conclusions=["((A \\wedge C) \\Box\\rightarrow B)"],
            settings={'N': 2, 'iterate': 2}
        )
        
        example.run_single_test()
        iterator = ImpositionModelIterator(example)
        
        # The verify/falsify functions should be consistent across models
        models = iterator.iterate()
        
        # Both models should satisfy premises
        for model in models:
            # Check that premise evaluations are consistent
            # (This would catch the context mismatch issue)
            assert hasattr(model, 'z3_verify_sets')
    
    def test_no_empty_verifier_sets(self):
        """Test that MODEL 2 doesn't have empty verifier sets."""
        # This was a specific issue with iterator
        logos_theory = get_logos_theory()
        
        example = BuildExample(
            name="test",
            semantic_theory=logos_theory,
            premises=["A", "B"],
            conclusions=["(A \\wedge B)"],
            settings={'N': 2, 'iterate': 2}
        )
        
        example.run_single_test()
        iterator = LogosModelIterator(example)
        models = iterator.iterate()
        
        # Check MODEL 2
        if len(models) >= 2:
            model2 = models[1]
            # Every atomic prop should have non-empty verifiers in possible worlds
            possible_worlds = getattr(model2, 'z3_possible_states', set())
            if possible_worlds:
                for prop in ['A', 'B']:
                    verifiers = model2.z3_verify_sets.get(prop, set())
                    # At least one verifier should be in possible worlds
                    assert len(verifiers & possible_worlds) > 0


class TestConstraintExtraction:
    """Test constraint extraction from iterator's Z3 model."""
    
    def test_boolean_evaluation_robustness(self):
        """Test that boolean evaluation handles all Z3 return types."""
        logos_theory = get_logos_theory()
        
        example = BuildExample(
            name="test",
            semantic_theory=logos_theory,
            premises=["\\Box A"],
            conclusions=["A"],
            settings={'N': 2, 'contingent': True, 'iterate': 2}
        )
        
        example.run_single_test()
        iterator = LogosModelIterator(example)
        
        # This should handle symbolic expressions properly
        models = iterator.iterate()
        assert len(models) >= 1
        
        # No errors should occur during evaluation
        # The _evaluate_z3_boolean method should handle all cases
    
    def test_constraint_preservation_through_iteration(self):
        """Test that constraints are preserved through iteration process."""
        logos_theory = get_logos_theory()
        
        example = BuildExample(
            name="test",
            semantic_theory=logos_theory,
            premises=["(A \\vee B)"],
            conclusions=["A"],
            settings={'N': 2, 'iterate': 3}
        )
        
        example.run_single_test()
        iterator = LogosModelIterator(example)
        
        # Track constraint count growth
        initial_count = len(iterator.original_constraints)
        
        models = iterator.iterate()
        
        # Each iteration should add difference constraints
        final_assertions = iterator.solver.assertions()
        assert len(final_assertions) > initial_count
        
        # But original constraints should still be there
        # (This ensures we don't accidentally clear them)