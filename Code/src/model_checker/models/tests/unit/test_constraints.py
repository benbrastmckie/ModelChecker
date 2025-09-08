"""Tests for constraints.py module.

Tests for ModelConstraints class functionality after refactoring.
Following TDD approach - these tests are written BEFORE moving the class.
"""

import unittest
from unittest.mock import Mock, MagicMock, patch
from z3 import Bool, And, Or, Not, ExprRef

from model_checker.models.constraints import ModelConstraints


class TestModelConstraints(unittest.TestCase):
    """Test ModelConstraints class functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Mock settings
        self.settings = {'N': 3}
        
        # Mock syntax object
        self.syntax = Mock()
        self.syntax.premises = []
        self.syntax.conclusions = []
        self.syntax.sentence_letters = []
        self.syntax.operator_collection = {}
        
        # Mock semantics
        self.semantics = Mock()
        self.semantics.frame_constraints = []
        self.semantics.premise_behavior = Mock(return_value=Bool('premise_constraint'))
        self.semantics.conclusion_behavior = Mock(return_value=Bool('conclusion_constraint'))
        
        # Mock proposition class
        self.proposition_class = Mock()
        self.proposition_class.proposition_constraints = Mock(return_value=[Bool('prop_constraint')])
    
    def test_initialization(self):
        """Test that ModelConstraints initializes correctly."""
        constraints = ModelConstraints(
            self.settings,
            self.syntax,
            self.semantics,
            self.proposition_class
        )
        
        # Check attributes are set
        self.assertEqual(constraints.settings, self.settings)
        self.assertEqual(constraints.syntax, self.syntax)
        self.assertEqual(constraints.semantics, self.semantics)
        self.assertEqual(constraints.proposition_class, self.proposition_class)
        
        # Check derived attributes
        self.assertEqual(constraints.premises, self.syntax.premises)
        self.assertEqual(constraints.conclusions, self.syntax.conclusions)
        self.assertIsInstance(constraints.sentence_letters, list)
        self.assertIsInstance(constraints.operators, dict)
    
    def test_load_sentence_letters(self):
        """Test extraction of sentence letters from syntax."""
        # Create mock sentence letters
        letter1 = Mock()
        letter1.sentence_letter = Bool('A')
        letter2 = Mock()
        letter2.sentence_letter = Bool('B')
        
        self.syntax.sentence_letters = [letter1, letter2]
        
        constraints = ModelConstraints(
            self.settings,
            self.syntax,
            self.semantics,
            self.proposition_class
        )
        
        # Check sentence letters were extracted
        self.assertEqual(len(constraints.sentence_letters), 2)
        self.assertEqual(str(constraints.sentence_letters[0]), 'A')
        self.assertEqual(str(constraints.sentence_letters[1]), 'B')
    
    def test_invalid_sentence_letter_raises_error(self):
        """Test that non-ExprRef sentence letters raise TypeError."""
        # Create invalid sentence letter
        bad_letter = Mock()
        bad_letter.sentence_letter = "not_a_z3_expr"  # String instead of ExprRef
        
        self.syntax.sentence_letters = [bad_letter]
        
        with self.assertRaises(TypeError):
            ModelConstraints(
                self.settings,
                self.syntax,
                self.semantics,
                self.proposition_class
            )
    
    def test_operator_dictionary_copying(self):
        """Test that operators are properly instantiated with semantics."""
        # Create mock operator classes
        op1_class = Mock()
        op2_class = Mock()
        
        self.syntax.operator_collection = {
            'op1': op1_class,
            'op2': op2_class
        }
        
        constraints = ModelConstraints(
            self.settings,
            self.syntax,
            self.semantics,
            self.proposition_class
        )
        
        # Check operators were instantiated
        self.assertEqual(len(constraints.operators), 2)
        self.assertIn('op1', constraints.operators)
        self.assertIn('op2', constraints.operators)
        
        # Check each operator was called with semantics
        op1_class.assert_called_once_with(self.semantics)
        op2_class.assert_called_once_with(self.semantics)
    
    def test_constraint_generation(self):
        """Test generation of all constraint types."""
        # Set up frame constraints
        self.semantics.frame_constraints = [Bool('frame1'), Bool('frame2')]
        
        # Set up sentence letters
        letter1 = Mock()
        letter1.sentence_letter = Bool('A')
        self.syntax.sentence_letters = [letter1]
        
        # Set up premises and conclusions - they need arguments attribute for instantiate()
        premise1 = Mock()
        premise1.arguments = []  # Empty list for leaf nodes
        premise1.update_objects = Mock()
        
        conclusion1 = Mock()
        conclusion1.arguments = []  # Empty list for leaf nodes
        conclusion1.update_objects = Mock()
        
        self.syntax.premises = [premise1]
        self.syntax.conclusions = [conclusion1]
        
        constraints = ModelConstraints(
            self.settings,
            self.syntax,
            self.semantics,
            self.proposition_class
        )
        
        # Check all constraint types
        self.assertEqual(len(constraints.frame_constraints), 2)
        self.assertEqual(len(constraints.model_constraints), 1)  # 1 letter * 1 constraint
        self.assertEqual(len(constraints.premise_constraints), 1)
        self.assertEqual(len(constraints.conclusion_constraints), 1)
        
        # Check all_constraints combines everything
        self.assertEqual(len(constraints.all_constraints), 5)  # 2 + 1 + 1 + 1
    
    def test_instantiate_method(self):
        """Test the instantiate method updates sentence objects."""
        # Create mock sentences with arguments
        sent1 = Mock()
        sent1.arguments = []
        sent1.update_objects = Mock()
        
        sent2 = Mock()
        sent2.arguments = []
        sent2.update_objects = Mock()
        
        self.syntax.premises = [sent1]
        self.syntax.conclusions = [sent2]
        
        constraints = ModelConstraints(
            self.settings,
            self.syntax,
            self.semantics,
            self.proposition_class
        )
        
        # Check update_objects was called on each sentence
        sent1.update_objects.assert_called_once_with(constraints)
        sent2.update_objects.assert_called_once_with(constraints)
    
    def test_instantiate_recursive(self):
        """Test instantiate handles nested sentence structures."""
        # Create nested sentence structure
        nested_sent = Mock()
        nested_sent.arguments = []
        nested_sent.update_objects = Mock()
        
        main_sent = Mock()
        main_sent.arguments = [nested_sent]
        main_sent.update_objects = Mock()
        
        self.syntax.premises = [main_sent]
        self.syntax.conclusions = []
        
        constraints = ModelConstraints(
            self.settings,
            self.syntax,
            self.semantics,
            self.proposition_class
        )
        
        # Check both sentences were updated
        main_sent.update_objects.assert_called_once_with(constraints)
        nested_sent.update_objects.assert_called_once_with(constraints)
    
    def test_str_representation(self):
        """Test string representation of ModelConstraints."""
        # Mock premises and conclusions (they need arguments attribute for instantiate())
        premise_a = Mock()
        premise_a.arguments = []
        premise_a.update_objects = Mock()
        
        premise_b = Mock()
        premise_b.arguments = []
        premise_b.update_objects = Mock()
        
        conclusion_c = Mock()
        conclusion_c.arguments = []
        conclusion_c.update_objects = Mock()
        
        self.syntax.premises = [premise_a, premise_b]
        self.syntax.conclusions = [conclusion_c]
        
        constraints = ModelConstraints(
            self.settings,
            self.syntax,
            self.semantics,
            self.proposition_class
        )
        
        result = str(constraints)
        self.assertIn("ModelConstraints", result)
        self.assertIn("premises", result)
        self.assertIn("conclusions", result)
    
    def test_print_enumerate(self):
        """Test enumerated printing of premises and conclusions."""
        # Create mock output
        mock_output = Mock()
        
        # Set up premises and conclusions with proper mock structure
        premise_a = Mock()
        premise_a.arguments = []
        premise_a.update_objects = Mock()
        
        premise_b = Mock()
        premise_b.arguments = []  
        premise_b.update_objects = Mock()
        
        conclusion_c = Mock()
        conclusion_c.arguments = []
        conclusion_c.update_objects = Mock()
        
        conclusion_d = Mock()
        conclusion_d.arguments = []
        conclusion_d.update_objects = Mock()
        
        self.syntax.premises = [premise_a, premise_b]
        self.syntax.conclusions = [conclusion_c, conclusion_d]
        
        constraints = ModelConstraints(
            self.settings,
            self.syntax,
            self.semantics,
            self.proposition_class
        )
        
        # Since print() uses file.write internally, we'll use patch
        with patch('builtins.print') as mock_print:
            constraints.print_enumerate(output=mock_output)
            
            # Check that print was called (exact number depends on premises/conclusions)
            self.assertGreater(mock_print.call_count, 0)
            
            # Check that it was called with the mock output
            for call in mock_print.call_args_list:
                self.assertEqual(call.kwargs['file'], mock_output)
    
    def test_empty_premises_conclusions(self):
        """Test behavior with empty premises or conclusions."""
        # Empty case
        self.syntax.premises = []
        self.syntax.conclusions = []
        
        constraints = ModelConstraints(
            self.settings,
            self.syntax,
            self.semantics,
            self.proposition_class
        )
        
        # Should not raise errors
        self.assertEqual(constraints.premise_constraints, [])
        self.assertEqual(constraints.conclusion_constraints, [])


if __name__ == '__main__':
    unittest.main()