"""Test IteratorBuildExample functionality.

Following TDD approach - written BEFORE implementing IteratorBuildExample.
Tests verify factory function pattern and theory-agnostic implementation.
"""

import unittest
from unittest.mock import Mock, patch
import z3
from model_checker.builder.example import BuildExample


class TestIteratorBuildExample(unittest.TestCase):
    """Test IteratorBuildExample functionality."""
    
    def setUp(self):
        """Create mock BuildExample for testing."""
        self.mock_build = Mock(spec=BuildExample)
        self.mock_build.semantic_theory = {
            'semantics': Mock,
            'model': Mock,
            'proposition': Mock
        }
        self.mock_build.semantics = Mock
        self.mock_build.proposition = Mock
        # Create mock operator collection
        mock_operators = Mock()
        mock_operators.apply_operator = Mock(return_value=[Mock()])
        self.mock_build.operators = mock_operators
        # Mock model structure class to return proper model structure
        mock_model_structure = Mock()
        mock_model_structure.premises = []
        mock_model_structure.conclusions = []
        mock_model_structure.interpret = Mock()
        mock_model_structure.solver = Mock()
        self.mock_build.model_structure_class = Mock(return_value=mock_model_structure)
        self.mock_build.premises = []  # Empty to avoid syntax parsing
        self.mock_build.conclusions = []  # Empty to avoid syntax parsing
        self.mock_build.settings = {'N': 3}
        self.mock_build.settings_manager = Mock()
        self.mock_build.build_module = Mock()
        # Add missing model_constraints attribute
        self.mock_build.model_constraints = Mock()
        self.mock_build.model_constraints.semantics = Mock()
    
    @patch('model_checker.iterate.build_example.Syntax')
    @patch('model_checker.iterate.build_example.ModelConstraints')
    def test_create_with_z3_model(self, mock_constraints_class, mock_syntax_class):
        """Test factory function creates proper instance."""
        mock_z3_model = Mock()
        mock_syntax = Mock()
        mock_syntax_class.return_value = mock_syntax
        mock_constraints = Mock()
        mock_constraints_class.return_value = mock_constraints
        
        # Create instance
        from model_checker.iterate.build_example import create_with_z3_model
        iter_build = create_with_z3_model(
            self.mock_build, mock_z3_model
        )
        
        # Verify instance created
        from model_checker.iterate.build_example import IteratorBuildExample
        self.assertIsInstance(iter_build, IteratorBuildExample)
        
        # Verify model structure created
        self.assertIsNotNone(iter_build.model_structure)
        
        # Verify Z3 model stored
        self.assertEqual(iter_build.model_structure.z3_model, mock_z3_model)
    
    def test_theory_agnostic_implementation(self):
        """Verify no theory concepts in IteratorBuildExample."""
        import inspect
        
        # This test will fail until we implement the class
        try:
            from model_checker.iterate.build_example import IteratorBuildExample
            source = inspect.getsource(IteratorBuildExample)
            
            # Theory concepts that should NOT appear
            forbidden = [
                'is_world', 'possible', 'verify', 'falsify',
                'states', '2**', 'atom', 'sentence_letter'
            ]
            
            for concept in forbidden:
                self.assertNotIn(concept, source,
                    f"Theory concept '{concept}' found in IteratorBuildExample")
        except ImportError:
            # Module doesn't exist yet - this is expected in TDD
            pass
    
    @patch('model_checker.iterate.build_example.Syntax')
    @patch('model_checker.iterate.build_example.ModelConstraints')
    def test_injection_delegation(self, mock_constraints_class, mock_syntax_class):
        """Test that injection is delegated to ModelConstraints."""
        mock_z3_model = Mock()
        mock_constraints = Mock()
        mock_constraints_class.return_value = mock_constraints
        mock_syntax = Mock()
        mock_syntax_class.return_value = mock_syntax
        
        # Create instance
        from model_checker.iterate.build_example import create_with_z3_model
        iter_build = create_with_z3_model(
            self.mock_build, mock_z3_model
        )
        
        # Verify injection was called
        mock_constraints.inject_z3_values.assert_called_once_with(mock_z3_model, self.mock_build.model_constraints.semantics)
    
    @patch('model_checker.iterate.build_example.Syntax')
    @patch('model_checker.iterate.build_example.ModelConstraints')
    def test_attributes_copied_from_original(self, mock_constraints_class, mock_syntax_class):
        """Test that necessary attributes are copied from original BuildExample."""
        mock_z3_model = Mock()
        mock_syntax = Mock()
        mock_syntax_class.return_value = mock_syntax
        mock_constraints = Mock()
        mock_constraints_class.return_value = mock_constraints
        
        # Set specific attributes on mock
        self.mock_build.build_module = Mock()
        self.mock_build.semantic_theory = {'name': 'test'}
        self.mock_build.semantics = Mock()
        self.mock_build.proposition = Mock()
        # Create mock operator collection
        mock_operators = Mock()
        mock_operators.apply_operator = Mock(return_value=[Mock()])
        self.mock_build.operators = mock_operators
        # Mock model structure class to return proper model structure
        mock_model_structure = Mock()
        mock_model_structure.premises = []
        mock_model_structure.conclusions = []
        mock_model_structure.interpret = Mock()
        mock_model_structure.solver = Mock()
        self.mock_build.model_structure_class = Mock(return_value=mock_model_structure)
        self.mock_build.premises = ['P1', 'P2']
        self.mock_build.conclusions = ['C1']
        self.mock_build.settings = {'N': 5, 'other': 'value'}
        self.mock_build.settings_manager = Mock()
        
        from model_checker.iterate.build_example import create_with_z3_model
        iter_build = create_with_z3_model(self.mock_build, mock_z3_model)
        
        # Verify attributes copied
        self.assertEqual(iter_build.build_module, self.mock_build.build_module)
        self.assertEqual(iter_build.semantic_theory, self.mock_build.semantic_theory)
        self.assertEqual(iter_build.semantics, self.mock_build.semantics)
        self.assertEqual(iter_build.proposition, self.mock_build.proposition)
        self.assertEqual(iter_build.operators, self.mock_build.operators)
        self.assertEqual(iter_build.model_structure_class, self.mock_build.model_structure_class)
        self.assertEqual(iter_build.premises, self.mock_build.premises)
        self.assertEqual(iter_build.conclusions, self.mock_build.conclusions)
        # Settings should be a copy, not the same object
        self.assertEqual(iter_build.settings, self.mock_build.settings)
        self.assertIsNot(iter_build.settings, self.mock_build.settings)
    
    def test_no_class_methods_used(self):
        """Verify no class methods (per maintenance standards)."""
        import inspect
        
        try:
            from model_checker.iterate.build_example import IteratorBuildExample
            # Check for forbidden decorators
            for name, method in inspect.getmembers(IteratorBuildExample):
                if inspect.ismethod(method) or inspect.isfunction(method):
                    source = inspect.getsource(method)
                    self.assertNotIn('@classmethod', source,
                        f"@classmethod found in {name}")
                    self.assertNotIn('@staticmethod', source,
                        f"@staticmethod found in {name}")
        except ImportError:
            # Module doesn't exist yet - expected in TDD
            pass


if __name__ == '__main__':
    unittest.main()