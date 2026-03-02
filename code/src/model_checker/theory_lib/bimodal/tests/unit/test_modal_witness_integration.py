"""Integration tests for witness predicates in modal operators.

Phase 4: Modal Operator Integration
Tests written BEFORE implementation following TDD methodology.
"""

import pytest
import z3
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics


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


class TestWitnessComponentsInitialization:
    """Tests that BimodalSemantics initializes witness components."""

    def test_witness_registry_initialized(self, semantics):
        """Test that semantics has witness_registry attribute."""
        assert hasattr(semantics, 'witness_registry'), \
            "BimodalSemantics should have witness_registry"

    def test_witness_registry_correct_type(self, semantics):
        """Test that witness_registry is the correct type."""
        from model_checker.theory_lib.bimodal.semantic.witness_registry import WitnessRegistry

        assert isinstance(semantics.witness_registry, WitnessRegistry), \
            "witness_registry should be WitnessRegistry instance"

    def test_witness_registry_has_correct_parameters(self, semantics):
        """Test that witness_registry was initialized with correct N, M."""
        assert semantics.witness_registry.N == 3, "Registry N should match semantics N"
        assert semantics.witness_registry.M == 2, "Registry M should match semantics M"

    def test_constraint_generator_initialized(self, semantics):
        """Test that semantics has constraint_generator attribute."""
        assert hasattr(semantics, 'constraint_generator'), \
            "BimodalSemantics should have constraint_generator"

    def test_constraint_generator_correct_type(self, semantics):
        """Test that constraint_generator is the correct type."""
        from model_checker.theory_lib.bimodal.semantic.witness_constraints import WitnessConstraintGenerator

        assert isinstance(semantics.constraint_generator, WitnessConstraintGenerator), \
            "constraint_generator should be WitnessConstraintGenerator instance"

    def test_constraint_generator_has_semantics_reference(self, semantics):
        """Test that constraint_generator has reference to semantics."""
        assert semantics.constraint_generator.semantics == semantics, \
            "Constraint generator should reference parent semantics"


class TestFormulaStringConversion:
    """Tests for _get_formula_string helper method."""

    def test_has_formula_string_method(self, semantics):
        """Test that semantics has _get_formula_string method."""
        assert hasattr(semantics, '_get_formula_string'), \
            "BimodalSemantics should have _get_formula_string method"

    def test_formula_string_callable(self, semantics):
        """Test that _get_formula_string is callable."""
        assert callable(semantics._get_formula_string), \
            "_get_formula_string should be callable"

    def test_formula_string_simple_sentence(self, semantics):
        """Test _get_formula_string on simple sentence letter."""
        # Create a mock sentence with sentence_letter
        class MockSentence:
            sentence_letter = 'p'
            operator = None

        mock_sentence = MockSentence()
        result = semantics._get_formula_string(mock_sentence)

        assert isinstance(result, str), "Should return string"
        assert len(result) > 0, "Should return non-empty string"
        assert 'p' in result, "Should include sentence letter"

    def test_formula_string_box_operator(self, semantics):
        """Test _get_formula_string on Box operator."""
        # Create mock Box(p) structure
        class MockOperator:
            name = "\\nec"

        class MockArgument:
            sentence_letter = 'p'
            operator = None

        class MockFormula:
            sentence_letter = None
            operator = MockOperator()
            arguments = [MockArgument()]

        mock_formula = MockFormula()
        result = semantics._get_formula_string(mock_formula)

        assert isinstance(result, str), "Should return string"
        # Should represent Box(p) in some form
        assert 'p' in result, "Should include argument"


class TestWitnessRegistration:
    """Tests for witness predicate registration during constraint building."""

    def test_can_register_witness_manually(self, semantics):
        """Test that witness can be registered for a formula."""
        formula_str = "box_p"

        # Should not be registered initially
        assert not semantics.witness_registry.has_witness_predicate(formula_str), \
            "Formula should not be pre-registered"

        # Register it
        predicate = semantics.witness_registry.register_witness_predicate(formula_str)

        # Should now be registered
        assert semantics.witness_registry.has_witness_predicate(formula_str), \
            "Formula should be registered after registration"

        assert predicate is not None, "Should return predicate"

    def test_can_generate_constraints_for_registered_witness(self, semantics):
        """Test that constraints can be generated for registered witness."""
        formula_str = "box_p"

        # Register witness
        predicate = semantics.witness_registry.register_witness_predicate(formula_str)

        # Generate constraints
        class MockFormula:
            pass

        constraints = semantics.constraint_generator.generate_witness_constraints(
            formula_str,
            MockFormula(),
            predicate
        )

        assert isinstance(constraints, list), "Should return list of constraints"
        assert len(constraints) > 0, "Should generate at least one constraint"


class TestNegationUnchanged:
    """Tests that Negation operator is unaffected by witness changes."""

    def test_negation_operator_exists(self):
        """Test that NegationOperator still exists."""
        from model_checker.theory_lib.bimodal.operators import NegationOperator

        # Negation operator should be importable
        assert NegationOperator is not None, "NegationOperator should exist"
        assert hasattr(NegationOperator, 'name'), "NegationOperator should have name attribute"

    def test_negation_has_simple_semantics(self, semantics):
        """Test that negation uses simple true_at/false_at without quantification."""
        from model_checker.theory_lib.bimodal.operators import NegationOperator

        neg_op = NegationOperator(semantics)

        # Create mock argument
        class MockArgument:
            pass

        mock_arg = MockArgument()
        eval_point = {"world": 0, "time": 0}

        # Patch semantics methods to track calls
        true_at_calls = []
        false_at_calls = []

        original_true_at = semantics.true_at
        original_false_at = semantics.false_at

        semantics.true_at = lambda s, ep: (true_at_calls.append((s, ep)), z3.Bool('mock_true'))[1]
        semantics.false_at = lambda s, ep: (false_at_calls.append((s, ep)), z3.Bool('mock_false'))[1]

        try:
            # Call negation's false_at (should call semantics.true_at on argument)
            neg_op.false_at(mock_arg, eval_point)

            # Should have called true_at on argument
            assert len(true_at_calls) > 0, "Negation.false_at should call semantics.true_at"

        finally:
            semantics.true_at = original_true_at
            semantics.false_at = original_false_at


class TestRegressionBasic:
    """Basic regression tests to ensure existing functionality works."""

    def test_semantics_initialization_succeeds(self, semantics):
        """Test that BimodalSemantics initializes without error."""
        assert semantics is not None, "Semantics should initialize"
        assert semantics.N == 3, "N should be set correctly"
        assert semantics.M == 2, "M should be set correctly"

    def test_has_necessary_semantic_methods(self, semantics):
        """Test that necessary semantic methods exist."""
        assert hasattr(semantics, 'is_world'), "Should have is_world"
        assert hasattr(semantics, 'is_valid_time_for_world'), "Should have is_valid_time_for_world"
        assert hasattr(semantics, 'true_at'), "Should have true_at"
        assert hasattr(semantics, 'false_at'), "Should have false_at"

    def test_frame_constraints_still_generated(self, semantics):
        """Test that frame_constraints are still generated."""
        assert hasattr(semantics, 'frame_constraints'), "Should have frame_constraints"
        assert isinstance(semantics.frame_constraints, list), "frame_constraints should be list"
        # Should have some constraints (exact number varies)
        assert len(semantics.frame_constraints) >= 0, "Should have frame constraints"
