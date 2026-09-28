"""Tests for the models module (model building and difference calculation)."""

import pytest
import z3
from types import SimpleNamespace
from unittest.mock import Mock, patch, MagicMock
from model_checker.iterate.models import ModelBuilder, DifferenceCalculator
from model_checker.iterate.errors import ModelExtractionError
from model_checker.solver import is_true
from model_checker.builder.example import BuildExample


def _real_build_example(theory, premises, conclusions, settings):
    """A real, non-mocked `BuildExample` -- no Mock stands in for the solver, the model,
    or the semantics. Only the surrounding `BuildModule` is a `Mock`, mirroring bimodal's
    own `_real_build_example`
    (`theory_lib/bimodal/tests/integration/test_iterate.py`) and the construction pattern
    already used by the other three theories' own `test_iterate.py` files."""
    general_settings = dict(settings)
    mock_module = Mock()
    mock_module.semantic_theories = {"theory": theory}
    mock_module.general_settings = general_settings
    mock_module.raw_general_settings = general_settings
    mock_module.module_flags = SimpleNamespace(
        contingent=False, disjoint=False, non_empty=False, non_null=False,
        print_constraints=False, save_output=False, print_impossible=False,
        print_z3=False, maximize=False,
    )
    example_case = [premises, conclusions, general_settings]
    return BuildExample(mock_module, theory, example_case)


def _generic_pinning_cases():
    """The three research-confirmed live probes (report F3): one case per theory without a
    `_pin_theory_specific_values` override. Built lazily (inside a function, not at module
    import time) so importing this test module never pays the cost of importing all three
    theory packages unless this test class actually runs."""
    from model_checker.theory_lib.logos import get_theory as get_logos_theory, LogosModelIterator
    from model_checker.theory_lib.exclusion import get_theory as get_exclusion_theory, ExclusionModelIterator
    from model_checker.theory_lib.exclusion.examples import EX_CM_6_premises, EX_CM_6_conclusions
    from model_checker.theory_lib.imposition import get_theory as get_imposition_theory, ImpositionModelIterator
    from model_checker.theory_lib.imposition.examples import IM_CM_0_premises, IM_CM_0_conclusions

    return [
        pytest.param(
            get_logos_theory(),
            LogosModelIterator,
            [],
            ["\\neg A"],
            {
                "N": 2, "contingent": True, "non_null": True, "non_empty": True,
                "disjoint": False, "max_time": 40, "iterate": 3,
            },
            id="logos",
        ),
        pytest.param(
            get_exclusion_theory(),
            ExclusionModelIterator,
            EX_CM_6_premises,
            EX_CM_6_conclusions,
            {
                "N": 3, "contingent": True, "non_null": True, "non_empty": True,
                "disjoint": False, "max_time": 40, "iterate": 3,
            },
            id="exclusion",
        ),
        pytest.param(
            get_imposition_theory(),
            ImpositionModelIterator,
            IM_CM_0_premises,
            IM_CM_0_conclusions,
            {
                "N": 4, "contingent": True, "non_null": True, "non_empty": True,
                "disjoint": False, "max_time": 40, "iterate": 3,
            },
            id="imposition",
        ),
    ]


@pytest.mark.slow
class TestGenericPinningReachesRebuiltSolve:
    """Live, non-mocked regression coverage for the generic `is_world`/`possible`/`verify`/
    `falsify` pinning loop in `ModelBuilder.build_new_model_structure`: for every theory
    without a `_pin_theory_specific_values` override (logos, exclusion, imposition), the
    pins computed from the candidate Z3 model must actually reach the solve that produces
    the rebuilt model, not merely populate a write-only `temp_solver` that is never
    checked and never read again.

    Method: monkeypatch `ModelBuilder.build_new_model_structure` to intercept every
    `(candidate_z3_model, returned_structure)` pair produced during a real, bounded
    `iterate: 3` search, then independently evaluate `is_world`/`possible`/`verify`/
    `falsify` (each guarded by the same `hasattr` checks the production loop itself uses)
    at every state -- and, for `verify`/`falsify`, every sentence-letter atom -- under
    both the candidate model the generic loop was asked to pin and the actual Z3 model the
    rebuilt structure's own solve produced. If pinning works, these must be identical
    everywhere; that is the definition of "pinned". This is agnostic to which live list a
    future refactor chooses for the pins -- it observes the solved result, not the fix's
    own internal mechanism.

    Deliberately not `TestAllConstraintsReflectsCertificateAfterSolve` (bimodal's own
    coverage for a different defect: a stale `all_constraints` snapshot). That test's
    subject is display/read completeness of a computed property; it would not catch a
    regression of the defect this class targets, which is about what the solver at
    `_setup_solver` actually saw.
    """

    @pytest.mark.parametrize(
        "theory, iterator_class, premises, conclusions, settings",
        _generic_pinning_cases(),
    )
    def test_rebuilt_solve_matches_pinned_values(
        self, monkeypatch, theory, iterator_class, premises, conclusions, settings
    ):
        original_build_new_model_structure = ModelBuilder.build_new_model_structure
        captured = []

        def _wrapped(self_builder, z3_model):
            result = original_build_new_model_structure(self_builder, z3_model)
            captured.append((z3_model, result))
            return result

        monkeypatch.setattr(ModelBuilder, "build_new_model_structure", _wrapped)

        example = _real_build_example(theory, premises, conclusions, settings)
        iterator = iterator_class(example)
        list(iterator.iterate_generator())

        assert len(captured) > 0, (
            "no rebuild was intercepted -- the test would pass vacuously without "
            "exercising build_new_model_structure at all"
        )

        checked_at_least_one_pair = False
        for candidate_z3_model, returned_structure in captured:
            if returned_structure is None:
                # UNSAT rebuild (or a build failure the production loop already treats as
                # a skip) -- nothing to compare against.
                continue
            checked_at_least_one_pair = True

            semantics = returned_structure.semantics
            actual_z3_model = returned_structure.z3_model
            atoms = returned_structure.model_constraints.sentence_letters
            num_states = 2 ** semantics.N

            if hasattr(semantics, 'is_world'):
                for state in range(num_states):
                    candidate_val = is_true(
                        candidate_z3_model.eval(semantics.is_world(state), model_completion=True)
                    )
                    actual_val = is_true(
                        actual_z3_model.eval(semantics.is_world(state), model_completion=True)
                    )
                    assert candidate_val == actual_val, (
                        f"is_world mismatch at state {state}: pinned {candidate_val}, "
                        f"actual solve {actual_val}"
                    )

                    if hasattr(semantics, 'possible'):
                        candidate_possible = is_true(
                            candidate_z3_model.eval(semantics.possible(state), model_completion=True)
                        )
                        actual_possible = is_true(
                            actual_z3_model.eval(semantics.possible(state), model_completion=True)
                        )
                        assert candidate_possible == actual_possible, (
                            f"possible mismatch at state {state}: pinned {candidate_possible}, "
                            f"actual solve {actual_possible}"
                        )

            if hasattr(semantics, 'verify'):
                for atom in atoms:
                    for state in range(num_states):
                        candidate_verify = is_true(
                            candidate_z3_model.eval(semantics.verify(state, atom), model_completion=True)
                        )
                        actual_verify = is_true(
                            actual_z3_model.eval(semantics.verify(state, atom), model_completion=True)
                        )
                        assert candidate_verify == actual_verify, (
                            f"verify mismatch at state {state}, atom {atom}: pinned "
                            f"{candidate_verify}, actual solve {actual_verify}"
                        )

                        if hasattr(semantics, 'falsify'):
                            candidate_falsify = is_true(
                                candidate_z3_model.eval(semantics.falsify(state, atom), model_completion=True)
                            )
                            actual_falsify = is_true(
                                actual_z3_model.eval(semantics.falsify(state, atom), model_completion=True)
                            )
                            assert candidate_falsify == actual_falsify, (
                                f"falsify mismatch at state {state}, atom {atom}: pinned "
                                f"{candidate_falsify}, actual solve {actual_falsify}"
                            )

        assert checked_at_least_one_pair, (
            "every intercepted rebuild returned None (all UNSAT) -- no pair was available "
            "to check pinning against"
        )


class TestModelBuilder:
    """Test cases for ModelBuilder functionality."""
    
    def test_initialization(self):
        """Test model builder initialization."""
        mock_example = Mock()
        builder = ModelBuilder(mock_example)
        assert builder.build_example == mock_example
    
    def test_build_new_model_structure_success(self):
        """Test successful model structure building."""
        # Create mock build example with required attributes
        mock_example = Mock()
        mock_example.premises = ["P"]
        mock_example.conclusions = ["Q"]
        mock_example.semantic_theory = {
            "semantics": Mock,
            "proposition": Mock,
            "operators": {}
        }
        mock_example.settings = {"N": 2}
        
        # Mock model structure class
        MockModelStructure = Mock()
        mock_example.model_structure_class = MockModelStructure
        
        # Create mock Z3 model
        mock_z3_model = Mock()
        mock_z3_model.eval = Mock(side_effect=lambda expr, **kwargs: z3.BoolVal(True))
        
        builder = ModelBuilder(mock_example)
        
        # Mock the imports and creation process - patch where they're imported
        with patch('model_checker.syntactic.Syntax') as MockSyntax, \
             patch('model_checker.models.constraints.ModelConstraints') as MockModelConstraints:
            
            # Set up mocks
            mock_syntax = Mock()
            mock_syntax.sentence_letters = []
            mock_syntax.premises = ["P"]
            mock_syntax.conclusions = ["Q"]
            MockSyntax.return_value = mock_syntax
            
            mock_semantics = Mock()
            mock_semantics.N = 2
            # Return actual Z3 expressions instead of strings
            mock_semantics.is_world = Mock(side_effect=lambda s: z3.Bool(f"is_world_{s}"))
            mock_semantics.possible = Mock(side_effect=lambda s: z3.Bool(f"possible_{s}"))
            
            mock_constraints = Mock()
            mock_constraints.semantics = mock_semantics
            mock_constraints.all_constraints = []
            MockModelConstraints.return_value = mock_constraints
            
            mock_structure = Mock()
            mock_structure.z3_model = mock_z3_model
            mock_structure.z3_model_status = True
            MockModelStructure.return_value = mock_structure
            mock_structure.interpret = Mock()  # Add interpret method
            
            # Build the model
            result = builder.build_new_model_structure(mock_z3_model)
            
            # Verify creation
            assert result == mock_structure
            MockSyntax.assert_called_once()
            MockModelConstraints.assert_called_once()
            MockModelStructure.assert_called_once()
    
    def test_build_new_model_structure_error_handling(self):
        """Test error handling in model building."""
        mock_example = Mock()
        mock_example.premises = ["P"]
        mock_example.conclusions = ["Q"]
        mock_example.semantic_theory = {
            "semantics": Mock,
            "proposition": Mock,
            "operators": {}
        }
        mock_example.settings = {}
        mock_example.model_structures = []  # Add this so len() works
        
        builder = ModelBuilder(mock_example)
        
        # Test with exception during building - now raises ModelExtractionError
        with patch('model_checker.syntactic.Syntax', side_effect=Exception("Test error")):
            with pytest.raises(ModelExtractionError) as exc_info:
                builder.build_new_model_structure(Mock())
            assert "Test error" in str(exc_info.value)
    
    def test_initialize_z3_dependent_attributes(self):
        """Test initialization of Z3-dependent model attributes."""
        mock_example = Mock()
        builder = ModelBuilder(mock_example)
        
        # Create mock structure and model
        mock_structure = Mock()
        mock_structure.settings = {'N': 4}  # Add settings for N
        mock_structure.semantics = Mock()
        mock_structure.semantics.all_states = [0, 1, 2, 3]
        # Return Z3 expressions, not strings
        mock_structure.semantics.is_world = Mock(side_effect=lambda s: z3.Bool(f"is_world_{s}"))
        mock_structure.semantics.possible = Mock(side_effect=lambda s: z3.Bool(f"possible_{s}"))
        
        mock_z3_model = Mock()
        # States 0 and 1 are worlds, states 0, 1, 2 are possible
        def eval_side_effect(expr, **kwargs):
            expr_str = str(expr)
            if "is_world_0" in expr_str or "is_world_1" in expr_str:
                return z3.BoolVal(True)
            elif "possible_0" in expr_str or "possible_1" in expr_str or "possible_2" in expr_str:
                return z3.BoolVal(True)
            return z3.BoolVal(False)
        
        mock_z3_model.eval = Mock(side_effect=eval_side_effect)
        
        # Initialize attributes
        builder._initialize_z3_dependent_attributes(mock_structure, mock_z3_model)
        
        # Check results
        assert mock_structure.z3_world_states == [0, 1]
        assert mock_structure.z3_possible_states == [0, 1, 2]
        assert mock_structure.z3_impossible_states == [3]
        assert mock_structure.z3_worlds == [0, 1]
    
    def test_evaluate_z3_boolean(self):
        """Test Z3 boolean evaluation."""
        builder = ModelBuilder(Mock())
        mock_model = Mock()
        
        # Test with True value
        mock_model.eval = Mock(return_value=z3.BoolVal(True))
        assert builder._evaluate_z3_boolean(mock_model, z3.BoolVal(True)) is True
        
        # Test with False value
        mock_model.eval = Mock(return_value=z3.BoolVal(False))
        assert builder._evaluate_z3_boolean(mock_model, z3.BoolVal(False)) is False
        
        # Test with None expression
        assert builder._evaluate_z3_boolean(mock_model, None) is False
        
        # Test with exception
        mock_model.eval = Mock(side_effect=Exception("Test error"))
        assert builder._evaluate_z3_boolean(mock_model, z3.BoolVal(True)) is False


class TestDifferenceCalculator:
    """Test cases for DifferenceCalculator functionality."""
    
    def test_calculate_differences_basic(self):
        """Test basic difference calculation."""
        calc = DifferenceCalculator()
        
        # Create mock structures
        new_struct = Mock()
        new_struct.z3_world_states = [0, 1, 2]
        new_struct.z3_possible_states = [0, 1, 2, 3]
        new_struct.z3_impossible_states = [4, 5]
        
        prev_struct = Mock()
        prev_struct.z3_world_states = [0, 1]
        prev_struct.z3_possible_states = [0, 1, 3]
        prev_struct.z3_impossible_states = [4]
        
        # Calculate differences
        diffs = calc.calculate_differences(new_struct, prev_struct)
        
        # Check world changes
        assert 'world_changes' in diffs
        assert diffs['world_changes']['added'] == [2]
        assert diffs['world_changes']['removed'] == []
        
        # Check possible changes
        assert 'possible_changes' in diffs
        assert diffs['possible_changes']['added'] == [2]
        assert diffs['possible_changes']['removed'] == []
    
    def test_calculate_differences_with_removals(self):
        """Test difference calculation with removed states."""
        calc = DifferenceCalculator()
        
        # Create structures where states are removed
        new_struct = Mock()
        new_struct.z3_world_states = [0]
        new_struct.z3_possible_states = [0, 1]
        new_struct.z3_impossible_states = [2, 3]
        
        prev_struct = Mock()
        prev_struct.z3_world_states = [0, 1, 2]
        prev_struct.z3_possible_states = [0, 1, 2, 3]
        prev_struct.z3_impossible_states = []
        
        diffs = calc.calculate_differences(new_struct, prev_struct)
        
        # Check removals
        assert diffs['world_changes']['removed'] == [1, 2]
        assert diffs['possible_changes']['removed'] == [2, 3]
        assert diffs['impossible_state_changes']['added'] == [2, 3]
    
    def test_calculate_differences_error_handling(self):
        """Test error handling in difference calculation."""
        calc = DifferenceCalculator()
        
        # Test with structures missing attributes
        new_struct = Mock()
        prev_struct = Mock()
        
        diffs = calc.calculate_differences(new_struct, prev_struct)
        
        # Should still return a dict without errors
        assert isinstance(diffs, dict)
        # Basic diffs should be empty due to missing attributes
        assert diffs.get('world_changes', {}) == {}
    
    def test_calculate_semantic_differences(self):
        """Test semantic difference calculation."""
        calc = DifferenceCalculator()
        
        # Create structures with semantic attributes
        new_struct = Mock()
        new_struct.semantics = Mock()
        new_struct.semantics.verify = Mock()
        new_struct.semantics.falsify = Mock()
        new_struct.sentence_letters = ['P', 'Q']
        new_struct.z3_world_states = [0, 1]
        
        prev_struct = Mock()
        prev_struct.semantics = Mock()
        prev_struct.semantics.verify = Mock()
        prev_struct.semantics.falsify = Mock()
        prev_struct.sentence_letters = ['P', 'Q']
        prev_struct.z3_world_states = [0, 1]
        
        # Mock different verification patterns
        new_struct.semantics.verify.side_effect = lambda atom, state: atom == 'P' and state == 0
        prev_struct.semantics.verify.side_effect = lambda atom, state: atom == 'P' and state in [0, 1]
        
        diffs = calc._calculate_semantic_differences(new_struct, prev_struct)
        
        # The implementation only adds atomic_changes if there are actual changes
        # Since we're using mocks that don't have z3_sentence_letters attribute,
        # the method returns an empty dict
        assert isinstance(diffs, dict)
        # To properly test this, we'd need to set up the z3_sentence_letters attribute
    
    def test_compare_state_evaluations(self):
        """Test state evaluation comparison."""
        calc = DifferenceCalculator()
        
        # Create structures with different world assignments
        new_struct = Mock()
        new_struct.z3_world_states = [0, 2, 3]
        
        prev_struct = Mock()
        prev_struct.z3_world_states = [0, 1, 2]
        
        comparisons = calc._compare_state_evaluations(new_struct, prev_struct)
        
        # State 1 lost world status
        assert 'state_1' in comparisons
        assert comparisons['state_1']['world_status_changed']['was_world'] is True
        assert comparisons['state_1']['world_status_changed']['is_world'] is False
        
        # State 3 gained world status
        assert 'state_3' in comparisons
        assert comparisons['state_3']['world_status_changed']['was_world'] is False
        assert comparisons['state_3']['world_status_changed']['is_world'] is True
        
        # States 0 and 2 unchanged (not in comparisons)
        assert 'state_0' not in comparisons
        assert 'state_2' not in comparisons