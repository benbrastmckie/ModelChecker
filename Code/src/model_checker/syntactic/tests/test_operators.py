"""Tests for the Operator and DefinedOperator classes."""

import pytest
from unittest.mock import MagicMock, Mock

from model_checker.syntactic.operators import Operator, DefinedOperator


class TestOperatorBasics:
    """Test basic Operator functionality."""
    
    def test_operator_abstract_class(self):
        """Test that Operator cannot be instantiated directly."""
        mock_semantics = MagicMock()
        with pytest.raises(NotImplementedError):
            Operator(mock_semantics)
    
    def test_operator_missing_name(self):
        """Test that operator without name raises error."""
        class TestOp(Operator):
            arity = 2
            
        mock_semantics = MagicMock()
        with pytest.raises(NameError, match="missing a name"):
            TestOp(mock_semantics)
    
    def test_operator_missing_arity(self):
        """Test that operator without arity raises error."""
        class TestOp(Operator):
            name = "test"
            
        mock_semantics = MagicMock()
        with pytest.raises(NameError, match="missing.*arity"):
            TestOp(mock_semantics)
    
    def test_operator_creation(self):
        """Test successful operator creation."""
        class TestOp(Operator):
            name = "∧"
            arity = 2
            
        mock_semantics = MagicMock()
        op = TestOp(mock_semantics)
        
        assert op.name == "∧"
        assert op.arity == 2
        assert op.primitive is True
        assert op.semantics == mock_semantics
    
    def test_operator_str_repr(self):
        """Test string representation."""
        class TestOp(Operator):
            name = "∨"
            arity = 2
            
        op = TestOp(MagicMock())
        assert str(op) == "∨"
        assert repr(op) == "∨"
    
    def test_operator_equality(self):
        """Test operator equality."""
        class TestOp1(Operator):
            name = "∧"
            arity = 2
            
        class TestOp2(Operator):
            name = "∧"
            arity = 2
            
        class TestOp3(Operator):
            name = "∨"
            arity = 2
            
        op1 = TestOp1(MagicMock())
        op2 = TestOp2(MagicMock())
        op3 = TestOp3(MagicMock())
        
        assert op1 == op2
        assert op1 != op3
        assert op1 != "not an operator"
    
    def test_operator_hash(self):
        """Test operator hashing."""
        class TestOp(Operator):
            name = "¬"
            arity = 1
            
        op = TestOp(MagicMock())
        assert hash(op) == hash(("¬", 1))


class TestOperatorPrinting:
    """Test operator printing methods."""
    
    def test_general_print(self):
        """Test general_print method."""
        class TestOp(Operator):
            name = "∧"
            arity = 2
            
        # Create mocks
        mock_semantics = MagicMock()
        op = TestOp(mock_semantics)
        
        mock_sentence = MagicMock()
        mock_proposition = MagicMock()
        mock_structure = MagicMock()
        
        mock_sentence.proposition = mock_proposition
        mock_proposition.model_structure = mock_structure
        mock_sentence.original_arguments = None
        
        eval_point = {"world": 1}
        
        # Call method
        op.general_print(mock_sentence, eval_point, 0, True)
        
        # Verify calls
        mock_proposition.print_proposition.assert_called_once_with(eval_point, 0, True)
    
    def test_general_print_with_arguments(self):
        """Test general_print with subformulas."""
        class TestOp(Operator):
            name = "∧"
            arity = 2
            
        # Create mocks
        mock_semantics = MagicMock()
        op = TestOp(mock_semantics)
        
        mock_sentence = MagicMock()
        mock_proposition = MagicMock()
        mock_structure = MagicMock()
        mock_arg1 = MagicMock()
        mock_arg2 = MagicMock()
        
        mock_sentence.proposition = mock_proposition
        mock_proposition.model_structure = mock_structure
        mock_sentence.original_arguments = [mock_arg1, mock_arg2]
        
        eval_point = {"world": 1}
        
        # Call method
        op.general_print(mock_sentence, eval_point, 0, True)
        
        # Verify calls
        mock_proposition.print_proposition.assert_called_once_with(eval_point, 0, True)
        mock_structure.recursive_print.assert_any_call(mock_arg1, eval_point, 1, True)
        mock_structure.recursive_print.assert_any_call(mock_arg2, eval_point, 1, True)


class TestDefinedOperator:
    """Test DefinedOperator functionality."""
    
    def test_defined_operator_abstract(self):
        """Test that derived_definition must be implemented."""
        class TestDefined(DefinedOperator):
            name = "→"
            arity = 2
            
            # Override but don't implement to avoid arity mismatch
            def derived_definition(self, p, q):
                return super().derived_definition(p, q)
            
        mock_semantics = MagicMock()
        op = TestDefined(mock_semantics)
        
        with pytest.raises(NotImplementedError):
            op.derived_definition("p", "q")
    
    def test_defined_operator_primitive_false(self):
        """Test that defined operators have primitive=False."""
        class TestDefined(DefinedOperator):
            name = "→"
            arity = 2
            
            def derived_definition(self, p, q):
                return ["∨", ["¬", p], q]
        
        assert TestDefined.primitive is False
    
    def test_defined_operator_arity_validation(self):
        """Test arity validation for defined operators."""
        class TestDefined(DefinedOperator):
            name = "→"
            arity = 3  # Wrong - derived_definition takes 2 args
            
            def derived_definition(self, p, q):
                return ["∨", ["¬", p], q]
        
        mock_semantics = MagicMock()
        with pytest.raises(ValueError, match="arity of 3.*does not match.*2"):
            TestDefined(mock_semantics)
    
    def test_defined_operator_missing_arity(self):
        """Test that missing arity raises error."""
        class TestDefined(DefinedOperator):
            name = "→"
            # No arity defined - this should trigger error in parent constructor
            
            def derived_definition(self, p, q):
                return ["∨", ["¬", p], q]
        
        mock_semantics = MagicMock()
        # The error actually comes from the parent Operator class
        with pytest.raises(NameError, match="missing a name or an arity"):
            TestDefined(mock_semantics)
    
    def test_defined_operator_valid(self):
        """Test valid defined operator."""
        class Implication(DefinedOperator):
            name = "→"
            arity = 2
            
            def derived_definition(self, p, q):
                return ["∨", ["¬", p], q]
        
        mock_semantics = MagicMock()
        op = Implication(mock_semantics)
        
        assert op.name == "→"
        assert op.arity == 2
        assert op.primitive is False
        
        # Test that derived_definition works
        result = op.derived_definition("p", "q")
        assert result == ["∨", ["¬", "p"], "q"]