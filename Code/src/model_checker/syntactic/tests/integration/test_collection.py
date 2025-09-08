"""Tests for the OperatorCollection class."""

import pytest
from unittest.mock import MagicMock, Mock
from z3 import Const, ExprRef

from model_checker.syntactic.collection import OperatorCollection
from model_checker.syntactic.operators import Operator
from model_checker.syntactic.atoms import AtomSort


class TestOperatorCollection:
    """Test OperatorCollection functionality."""
    
    def test_empty_collection(self):
        """Test creating an empty collection."""
        collection = OperatorCollection()
        assert collection.operator_dictionary == {}
    
    def test_add_single_operator(self):
        """Test adding a single operator."""
        class TestOp(Operator):
            name = "∧"
            arity = 2
        
        collection = OperatorCollection()
        collection.add_operator(TestOp)
        
        assert "∧" in collection.operator_dictionary
        assert collection["∧"] == TestOp
    
    def test_add_multiple_operators(self):
        """Test adding multiple operators at once."""
        class AndOp(Operator):
            name = "∧"
            arity = 2
            
        class OrOp(Operator):
            name = "∨"
            arity = 2
        
        collection = OperatorCollection()
        collection.add_operator([AndOp, OrOp])
        
        assert "∧" in collection.operator_dictionary
        assert "∨" in collection.operator_dictionary
        assert collection["∧"] == AndOp
        assert collection["∨"] == OrOp
    
    def test_init_with_operators(self):
        """Test initializing collection with operators."""
        class NotOp(Operator):
            name = "¬"
            arity = 1
        
        collection = OperatorCollection(NotOp)
        assert "¬" in collection.operator_dictionary
    
    def test_add_duplicate_operator(self):
        """Test that duplicate operators are skipped."""
        class TestOp1(Operator):
            name = "∧"
            arity = 2
            
        class TestOp2(Operator):
            name = "∧"
            arity = 2
        
        collection = OperatorCollection(TestOp1)
        collection.add_operator(TestOp2)
        
        # Should still have TestOp1, not TestOp2
        assert collection["∧"] == TestOp1
    
    def test_add_operator_without_name(self):
        """Test adding operator without name raises error."""
        class BadOp(Operator):
            # No name attribute
            arity = 1
        
        collection = OperatorCollection()
        with pytest.raises(ValueError, match="no name defined"):
            collection.add_operator(BadOp)
    
    def test_add_invalid_type(self):
        """Test adding invalid type raises error."""
        collection = OperatorCollection()
        with pytest.raises(TypeError, match="Unexpected input type"):
            collection.add_operator("not a type")
    
    def test_merge_collections(self):
        """Test merging two collections."""
        class AndOp(Operator):
            name = "∧"
            arity = 2
            
        class OrOp(Operator):
            name = "∨"
            arity = 2
        
        collection1 = OperatorCollection(AndOp)
        collection2 = OperatorCollection(OrOp)
        
        collection1.add_operator(collection2)
        
        assert "∧" in collection1.operator_dictionary
        assert "∨" in collection1.operator_dictionary
    
    def test_iter_collection(self):
        """Test iterating over collection."""
        class AndOp(Operator):
            name = "∧"
            arity = 2
            
        class OrOp(Operator):
            name = "∨"
            arity = 2
        
        collection = OperatorCollection([AndOp, OrOp])
        names = list(collection)
        
        assert set(names) == {"∧", "∨"}
    
    def test_items_method(self):
        """Test items method."""
        class NotOp(Operator):
            name = "¬"
            arity = 1
        
        collection = OperatorCollection(NotOp)
        items = list(collection.items())
        
        assert len(items) == 1
        assert items[0] == ("¬", NotOp)


class TestApplyOperator:
    """Test apply_operator functionality."""
    
    def test_apply_atomic_sentence(self):
        """Test applying to atomic sentence."""
        collection = OperatorCollection()
        result = collection.apply_operator(["p"])
        
        assert len(result) == 1
        assert isinstance(result[0], ExprRef)  # Z3 expressions are ExprRef
        assert str(result[0]) == "p"
    
    def test_apply_extremal_operators(self):
        """Test applying to extremal operators."""
        class TopOp(Operator):
            name = "\\top"
            arity = 0
            
        class BotOp(Operator):
            name = "\\bot"
            arity = 0
        
        collection = OperatorCollection([TopOp, BotOp])
        
        result_top = collection.apply_operator(["\\top"])
        assert result_top == [TopOp]
        
        result_bot = collection.apply_operator(["\\bot"])
        assert result_bot == [BotOp]
    
    def test_apply_invalid_atom(self):
        """Test applying to invalid atom raises error."""
        collection = OperatorCollection()
        with pytest.raises(ValueError, match="invalid in apply_operator"):
            collection.apply_operator(["@#$"])
    
    def test_apply_unary_operator(self):
        """Test applying unary operator."""
        class NotOp(Operator):
            name = "¬"
            arity = 1
        
        collection = OperatorCollection(NotOp)
        result = collection.apply_operator(["¬", ["p"]])
        
        assert len(result) == 2
        assert result[0] == NotOp
        assert isinstance(result[1][0], ExprRef)
        assert str(result[1][0]) == "p"
    
    def test_apply_binary_operator(self):
        """Test applying binary operator."""
        class AndOp(Operator):
            name = "∧"
            arity = 2
        
        collection = OperatorCollection(AndOp)
        result = collection.apply_operator(["∧", ["p"], ["q"]])
        
        assert len(result) == 3
        assert result[0] == AndOp
        assert isinstance(result[1][0], ExprRef)
        assert isinstance(result[2][0], ExprRef)
        assert str(result[1][0]) == "p"
        assert str(result[2][0]) == "q"
    
    def test_apply_nested_operators(self):
        """Test applying nested operators."""
        class AndOp(Operator):
            name = "∧"
            arity = 2
            
        class NotOp(Operator):
            name = "¬"
            arity = 1
        
        collection = OperatorCollection([AndOp, NotOp])
        # (¬p ∧ q)
        result = collection.apply_operator(["∧", ["¬", ["p"]], ["q"]])
        
        assert result[0] == AndOp
        assert result[1][0] == NotOp
        assert isinstance(result[1][1][0], ExprRef)
        assert isinstance(result[2][0], ExprRef)
    
    def test_apply_non_string_operator(self):
        """Test that non-string operator raises error."""
        collection = OperatorCollection()
        with pytest.raises(TypeError, match="Expected operator name as a string"):
            collection.apply_operator([123, ["p"]])