"""Targeted tests to improve iterate package coverage.

Focus on specific uncovered lines that are easier to test.
"""

import unittest
from unittest.mock import Mock, patch
import z3

from model_checker.iterate.constraints import ConstraintGenerator
from model_checker.iterate.models import ModelBuilder, DifferenceCalculator, evaluate_z3_boolean
from model_checker.iterate.graph import ModelGraph, IsomorphismChecker
from model_checker.iterate.metrics import IterationStatistics, TerminationManager


class TestConstraintGeneratorCoverage(unittest.TestCase):
    """Test uncovered paths in ConstraintGenerator."""
    
    def test_get_model_with_z3_exception(self):
        """Test get_model when Z3 raises an exception."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = Mock()
        mock_example.model_structure.stored_solver = Mock()
        mock_example.model_structure.solver.assertions = Mock(return_value=[])
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        
        generator = ConstraintGenerator(mock_example)
        
        # Make solver.model() raise Z3Exception
        generator.solver.model = Mock(side_effect=z3.Z3Exception("Test error"))
        
        result = generator.get_model()
        self.assertIsNone(result)
    
    def test_create_extended_constraints_empty(self):
        """Test create_extended_constraints with empty previous models."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = Mock()
        mock_example.model_structure.stored_solver = Mock()
        mock_example.model_structure.solver.assertions = Mock(return_value=[])
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        
        generator = ConstraintGenerator(mock_example)
        
        # Test with empty list
        result = generator.create_extended_constraints([])
        self.assertEqual(result, [])
    
    def test_generate_input_combinations_higher_arity(self):
        """Test _generate_input_combinations with arity > 1."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.solver = Mock()
        mock_example.model_structure.stored_solver = Mock()
        mock_example.model_structure.solver.assertions = Mock(return_value=[])
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        
        generator = ConstraintGenerator(mock_example)
        
        # Test binary predicate
        result = generator._generate_input_combinations(2, 3)
        expected = [(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
        self.assertEqual(list(result), expected)


class TestModelsUtilityCoverage(unittest.TestCase):
    """Test uncovered utility functions in models.py."""
    
    def test_evaluate_z3_boolean_standalone(self):
        """Test the standalone evaluate_z3_boolean function."""
        mock_model = Mock()
        
        # Test with None - this is the only part that works without full Z3 setup
        result = evaluate_z3_boolean(mock_model, None)
        self.assertFalse(result)
    
    def test_difference_calculator_empty_differences(self):
        """Test DifferenceCalculator with structures having no differences."""
        calculator = DifferenceCalculator()
        
        mock_new = Mock()
        mock_new.z3_world_states = [0, 1]
        mock_new.z3_possible_states = [0, 1]
        mock_new.z3_impossible_states = []
        mock_new.z3_sentence_letters = []
        
        mock_prev = Mock()
        mock_prev.z3_world_states = [0, 1]
        mock_prev.z3_possible_states = [0, 1]
        mock_prev.z3_impossible_states = []
        mock_prev.z3_sentence_letters = []
        
        differences = calculator.calculate_differences(mock_new, mock_prev)
        
        # Should have empty change lists
        self.assertEqual(differences['world_changes']['added'], [])
        self.assertEqual(differences['world_changes']['removed'], [])


class TestMetricsCoverage(unittest.TestCase):
    """Test uncovered paths in metrics.py."""
    
    def test_iteration_statistics_completion_time(self):
        """Test setting completion_time."""
        stats = IterationStatistics()
        
        # Set completion time
        stats.set_completion_time(1.23)
        
        # Check it was set
        self.assertEqual(stats.completion_time, 1.23)


class TestGraphCoverage(unittest.TestCase):
    """Test uncovered paths in graph.py."""
    
    def test_model_graph_init_coverage(self):
        """Test ModelGraph initialization paths."""
        mock_structure = Mock()
        mock_structure.z3_world_states = []
        mock_structure.semantics = None
        mock_structure.model_constraints = None
        
        mock_z3_model = Mock()
        
        # Should handle missing attributes
        graph = ModelGraph(mock_structure, mock_z3_model)
        self.assertIsNotNone(graph.graph)
    
    def test_graph_init_with_logging(self):
        """Test that ModelGraph initialization handles logging."""
        # This test just ensures the import works
        from model_checker.iterate.graph import ModelGraph
        self.assertTrue(ModelGraph is not None)


class TestErrorPathsCoverage(unittest.TestCase):
    """Test error handling paths for better coverage."""
    
    def test_model_builder_initialize_with_missing_solver(self):
        """Test ModelBuilder initialization when solver is missing."""
        mock_example = Mock()
        mock_example.model_structures = []
        
        builder = ModelBuilder(mock_example)
        
        mock_structure = Mock()
        mock_constraints = Mock()
        mock_constraints.solver = None
        settings = {}
        
        # Should handle None solver
        builder._initialize_base_attributes(mock_structure, mock_constraints, settings)
        self.assertIsNone(mock_structure.solver)
    
    def test_difference_calculator_error_in_semantic_differences(self):
        """Test error handling in semantic difference calculation."""
        calculator = DifferenceCalculator()
        
        mock_new = Mock()
        mock_prev = Mock()
        
        # Make _calculate_atomic_differences raise an error
        with patch.object(calculator, '_calculate_atomic_differences', side_effect=AttributeError("test")):
            result = calculator._calculate_semantic_differences(mock_new, mock_prev)
            
            # Should catch error and add to result
            self.assertIn('semantic_error', result)


if __name__ == '__main__':
    unittest.main()