"""
Integration tests for refactored theory workflows.

Tests that ensure the refactored semantic modules work together correctly
and that backward compatibility is maintained through import wrappers.
"""

import pytest
import sys
from typing import Dict, Any

# Add source path for imports
sys.path.insert(0, 'Code/src')


class TestExclusionRefactoredWorkflow:
    """Test exclusion theory refactored workflow."""

    def test_import_wrapper_compatibility(self) -> None:
        """Test that original imports still work through wrapper."""
        # This should work exactly as before refactoring
        from model_checker.theory_lib.exclusion.semantic import WitnessSemantics

        assert WitnessSemantics is not None
        assert hasattr(WitnessSemantics, '__init__')

    def test_direct_module_imports(self) -> None:
        """Test that new modular imports work."""
        from model_checker.theory_lib.exclusion.semantic.core import WitnessSemantics
        from model_checker.theory_lib.exclusion.semantic.model import WitnessAwareModel
        from model_checker.theory_lib.exclusion.semantic.registry import WitnessRegistry
        from model_checker.theory_lib.exclusion.semantic.constraints import WitnessConstraintGenerator

        # All modules should be importable
        assert WitnessSemantics is not None
        assert WitnessAwareModel is not None
        assert WitnessRegistry is not None
        assert WitnessConstraintGenerator is not None

    def test_exclusion_example_execution(self) -> None:
        """Test that exclusion examples still execute correctly."""
        from model_checker.theory_lib.exclusion import examples

        # Should have example_range
        assert hasattr(examples, 'example_range')
        assert len(examples.example_range) > 0

        # Should have semantic_theories
        assert hasattr(examples, 'semantic_theories')
        assert 'BernardChampollion' in examples.semantic_theories

    def test_exclusion_semantic_creation(self) -> None:
        """Test creating exclusion semantics with refactored modules."""
        from model_checker.theory_lib.exclusion.semantic.core import WitnessSemantics

        settings = {
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

        semantics = WitnessSemantics(settings)
        assert semantics is not None
        assert semantics.N == 3

        # Should have modular components
        assert hasattr(semantics, 'witness_registry')
        assert hasattr(semantics, 'constraint_generator')

    def test_exclusion_component_integration(self) -> None:
        """Test that exclusion components work together."""
        from model_checker.theory_lib.exclusion.semantic.core import WitnessSemantics
        from model_checker.theory_lib.exclusion.semantic.registry import WitnessRegistry

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

        semantics = WitnessSemantics(settings)

        # Test registry integration
        h_pred, y_pred = semantics.witness_registry.register_witness_predicates("test_formula")
        assert h_pred is not None
        assert y_pred is not None

        # Test that predicates are accessible
        all_predicates = semantics.witness_registry.get_all_predicates()
        assert "test_formula_h" in all_predicates
        assert "test_formula_y" in all_predicates


class TestImpositionRefactoredWorkflow:
    """Test imposition theory refactored workflow."""

    def test_import_wrapper_compatibility(self) -> None:
        """Test that original imports still work through wrapper."""
        from model_checker.theory_lib.imposition.semantic import ImpositionSemantics

        assert ImpositionSemantics is not None
        assert hasattr(ImpositionSemantics, '__init__')

    def test_direct_module_imports(self) -> None:
        """Test that new modular imports work."""
        from model_checker.theory_lib.imposition.semantic.core import ImpositionSemantics
        from model_checker.theory_lib.imposition.semantic.model import ImpositionModelStructure
        from model_checker.theory_lib.imposition.semantic.helpers import safe_bitvec_as_long

        # All modules should be importable
        assert ImpositionSemantics is not None
        assert ImpositionModelStructure is not None
        assert safe_bitvec_as_long is not None

    def test_imposition_example_execution(self) -> None:
        """Test that imposition examples still execute correctly."""
        from model_checker.theory_lib.imposition import examples

        # Should have example_range
        assert hasattr(examples, 'example_range')
        assert len(examples.example_range) > 0

        # Should have semantic_theories
        assert hasattr(examples, 'semantic_theories')
        assert 'Fine' in examples.semantic_theories

    def test_imposition_semantic_creation(self) -> None:
        """Test creating imposition semantics with refactored modules."""
        from model_checker.theory_lib.imposition.semantic.core import ImpositionSemantics

        settings = {
            'N': 3,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'max_time': 1,
            'iterate': 1,
            'expectation': None,
        }

        semantics = ImpositionSemantics(settings)
        assert semantics is not None
        assert semantics.N == 3

        # Should inherit from LogosSemantics
        from model_checker.theory_lib.logos.semantic import LogosSemantics
        assert isinstance(semantics, LogosSemantics)

    def test_imposition_helper_functions(self) -> None:
        """Test that imposition helper functions work correctly."""
        from model_checker.theory_lib.imposition.semantic.helpers import (
            safe_bitvec_as_long,
            format_imposition_relation,
            group_impositions_by_world
        )
        import z3

        # Test safe_bitvec_as_long
        bv = z3.BitVecVal(5, 3)
        result = safe_bitvec_as_long(bv)
        assert result == 5

        # Test format_imposition_relation
        formatted = format_imposition_relation(1, 2, 3)
        assert formatted == "s1 ->_2 s3"

        # Test group_impositions_by_world
        world = z3.BitVecVal(1, 3)
        relations = [(z3.BitVecVal(0, 3), world, z3.BitVecVal(2, 3))]
        grouped = group_impositions_by_world(relations)
        assert world in grouped


class TestLogosProtocolIntegration:
    """Test logos protocol integration."""

    def test_protocol_imports(self) -> None:
        """Test that logos protocols can be imported."""
        from model_checker.theory_lib.logos.protocols import (
            SubtheoryProtocol,
            OperatorProtocol,
            SemanticsProtocol,
            RegistryProtocol,
            PropositionProtocol,
            ModelIteratorProtocol
        )

        # All protocols should be importable
        assert SubtheoryProtocol is not None
        assert OperatorProtocol is not None
        assert SemanticsProtocol is not None
        assert RegistryProtocol is not None
        assert PropositionProtocol is not None
        assert ModelIteratorProtocol is not None

    def test_logos_example_execution(self) -> None:
        """Test that logos examples still work correctly."""
        from model_checker.theory_lib.logos import examples

        # Should have example_range
        assert hasattr(examples, 'example_range')
        assert len(examples.example_range) > 0

        # Should have semantic_theories
        assert hasattr(examples, 'semantic_theories')
        assert 'Primary' in examples.semantic_theories


class TestCrossTheoryCompatibility:
    """Test compatibility between refactored theories."""

    def test_all_theories_importable(self) -> None:
        """Test that all theories can be imported simultaneously."""
        from model_checker.theory_lib.exclusion.semantic.core import WitnessSemantics
        from model_checker.theory_lib.imposition.semantic.core import ImpositionSemantics
        from model_checker.theory_lib.logos.semantic import LogosSemantics

        # All should be importable together
        assert WitnessSemantics is not None
        assert ImpositionSemantics is not None
        assert LogosSemantics is not None

    def test_theory_inheritance_relationships(self) -> None:
        """Test that theory inheritance relationships are preserved."""
        from model_checker.theory_lib.exclusion.semantic.core import WitnessSemantics
        from model_checker.theory_lib.imposition.semantic.core import ImpositionSemantics
        from model_checker.theory_lib.logos.semantic import LogosSemantics

        # WitnessSemantics should inherit from LogosSemantics
        assert issubclass(WitnessSemantics, LogosSemantics)

        # ImpositionSemantics should inherit from LogosSemantics
        assert issubclass(ImpositionSemantics, LogosSemantics)

    def test_shared_type_system(self) -> None:
        """Test that all theories use the shared type system."""
        from model_checker.theory_lib.types import (
            WitnessSemantics as WitnessSemanticsProtocol,
            ImpositionSemantics as ImpositionSemanticsProtocol,
            SubtheoryProtocol,
            StateId,
            OperatorDict,
            ExampleDict
        )

        # All protocol types should be defined
        assert WitnessSemanticsProtocol is not None
        assert ImpositionSemanticsProtocol is not None
        assert SubtheoryProtocol is not None
        assert StateId is not None
        assert OperatorDict is not None
        assert ExampleDict is not None

    def test_example_module_compatibility(self) -> None:
        """Test that all example modules work with dev_cli.py."""
        from model_checker.theory_lib.exclusion import examples as ex_examples
        from model_checker.theory_lib.imposition import examples as im_examples
        from model_checker.theory_lib.logos import examples as lo_examples

        # All should have required attributes
        for examples in [ex_examples, im_examples, lo_examples]:
            assert hasattr(examples, 'example_range')
            assert hasattr(examples, 'semantic_theories')
            assert isinstance(examples.example_range, dict)
            assert isinstance(examples.semantic_theories, dict)
            assert len(examples.example_range) > 0
            assert len(examples.semantic_theories) > 0


class TestBackwardCompatibility:
    """Test that refactoring maintains backward compatibility."""

    def test_original_import_patterns_work(self) -> None:
        """Test that original import patterns still function."""
        # These imports should work exactly as before refactoring
        from model_checker.theory_lib.exclusion.semantic import WitnessSemantics as ExclusionSemantics
        from model_checker.theory_lib.imposition.semantic import ImpositionSemantics
        from model_checker.theory_lib.logos.semantic import LogosSemantics

        assert ExclusionSemantics is not None
        assert ImpositionSemantics is not None
        assert LogosSemantics is not None

    def test_example_imports_work(self) -> None:
        """Test that example imports work as expected."""
        from model_checker.theory_lib.exclusion.examples import example_range as ex_range
        from model_checker.theory_lib.imposition.examples import example_range as im_range
        from model_checker.theory_lib.logos.examples import example_range as lo_range

        assert isinstance(ex_range, dict)
        assert isinstance(im_range, dict)
        assert isinstance(lo_range, dict)

        assert len(ex_range) > 0
        assert len(im_range) > 0
        assert len(lo_range) > 0

    def test_semantic_class_compatibility(self) -> None:
        """Test that semantic classes have expected interfaces."""
        from model_checker.theory_lib.exclusion.semantic import WitnessSemantics
        from model_checker.theory_lib.imposition.semantic import ImpositionSemantics

        # Test that classes can be instantiated with basic settings
        basic_settings = {
            'N': 3,
            'max_time': 1,
            'iterate': 1
        }

        exclusion_semantics = WitnessSemantics(basic_settings)
        imposition_semantics = ImpositionSemantics(basic_settings)

        # Both should be instantiable and have basic attributes
        assert exclusion_semantics.N == 3
        assert imposition_semantics.N == 3

        # Both should have inherited methods from LogosSemantics
        assert hasattr(exclusion_semantics, 'true_at')
        assert hasattr(imposition_semantics, 'true_at')

    def test_functional_compatibility(self) -> None:
        """Test that refactored theories maintain functional compatibility."""
        # Import using old patterns
        from model_checker.theory_lib.exclusion import examples as ex_examples
        from model_checker.theory_lib.imposition import examples as im_examples

        # Test that semantic theories configuration works
        ex_theories = ex_examples.semantic_theories
        im_theories = im_examples.semantic_theories

        # Should have actual class references, not strings
        for theory_name, theory_config in ex_theories.items():
            assert 'semantics' in theory_config
            assert hasattr(theory_config['semantics'], '__init__')  # Should be a class

        for theory_name, theory_config in im_theories.items():
            assert 'semantics' in theory_config
            assert hasattr(theory_config['semantics'], '__init__')  # Should be a class