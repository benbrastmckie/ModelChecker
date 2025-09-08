"""Tests for the Syntax class."""

import pytest
from unittest.mock import MagicMock, Mock

from model_checker.syntactic.syntax import Syntax
from model_checker.syntactic.collection import OperatorCollection
from model_checker.syntactic.operators import Operator, DefinedOperator


class TestSyntaxBasics:
    """Test basic Syntax functionality."""
    
    def test_empty_syntax(self):
        """Test creating syntax with no premises or conclusions."""
        collection = OperatorCollection()
        syntax = Syntax([], [], collection)
        
        assert syntax.infix_premises == []
        assert syntax.infix_conclusions == []
        assert syntax.premises == []
        assert syntax.conclusions == []
        assert syntax.all_sentences == {}
        assert syntax.sentence_letters == []
    
    def test_simple_premise(self):
        """Test syntax with simple atomic premise."""
        collection = OperatorCollection()
        syntax = Syntax(["p"], [], collection)
        
        assert len(syntax.premises) == 1
        assert syntax.premises[0].name == "p"
        assert "p" in syntax.all_sentences
        assert len(syntax.sentence_letters) == 1
        assert syntax.sentence_letters[0].name == "p"
    
    def test_simple_conclusion(self):
        """Test syntax with simple atomic conclusion."""
        collection = OperatorCollection()
        syntax = Syntax([], ["q"], collection)
        
        assert len(syntax.conclusions) == 1
        assert syntax.conclusions[0].name == "q"
        assert "q" in syntax.all_sentences
        assert len(syntax.sentence_letters) == 1
    
    def test_complex_sentence(self):
        """Test syntax with complex sentence."""
        class AndOp(Operator):
            name = "∧"
            arity = 2
        
        collection = OperatorCollection(AndOp)
        syntax = Syntax(["(p ∧ q)"], [], collection)
        
        assert len(syntax.premises) == 1
        assert syntax.premises[0].name == "(p ∧ q)"
        assert len(syntax.all_sentences) == 3  # (p ∧ q), p, q
        assert len(syntax.sentence_letters) == 2  # p, q
        
        # Check operator linkage
        premise = syntax.premises[0]
        assert premise.operator == AndOp
        assert premise.original_operator == AndOp
    
    def test_shared_subsentences(self):
        """Test that shared subsentences are reused."""
        class OrOp(Operator):
            name = "∨"
            arity = 2
        
        collection = OperatorCollection(OrOp)
        syntax = Syntax(["(p ∨ q)", "(q ∨ p)"], [], collection)
        
        # Should have 5 sentences: (p ∨ q), (q ∨ p), p, q
        assert len(syntax.all_sentences) == 4
        
        # p and q should be the same objects in both premises
        p1 = syntax.premises[0].arguments[0]
        q1 = syntax.premises[0].arguments[1]
        q2 = syntax.premises[1].arguments[0]
        p2 = syntax.premises[1].arguments[1]
        
        assert p1 is p2
        assert q1 is q2


class TestOperatorHandling:
    """Test operator handling in Syntax."""
    
    def test_defined_operator(self):
        """Test syntax with defined operator."""
        class NotOp(Operator):
            name = "¬"
            arity = 1
            
        class OrOp(Operator):
            name = "∨"
            arity = 2
            
        class ImpliesOp(DefinedOperator):
            name = "→"
            arity = 2
            
            def derived_definition(self, p, q):
                return [OrOp, [NotOp, p], q]
        
        collection = OperatorCollection([NotOp, OrOp, ImpliesOp])
        syntax = Syntax(["(p → q)"], [], collection)
        
        premise = syntax.premises[0]
        assert premise.original_operator == ImpliesOp
        assert premise.operator == OrOp  # Derived operator
        
        # Check derived arguments
        assert len(premise.arguments) == 2
        # premise.arguments are Sentence objects, not strings
        assert premise.arguments[0].name == "¬ p"
        assert premise.arguments[1].name == "q"
    
    def test_extremal_operators(self):
        """Test handling of \\top and \\bot."""
        class TopOp(Operator):
            name = "\\top"
            arity = 0
            
        class BotOp(Operator):
            name = "\\bot"
            arity = 0
        
        collection = OperatorCollection([TopOp, BotOp])
        syntax = Syntax(["\\top", "\\bot"], [], collection)
        
        assert len(syntax.premises) == 2
        assert syntax.premises[0].name == "\\top"
        assert syntax.premises[1].name == "\\bot"
        
        # These should not be in sentence_letters
        assert len(syntax.sentence_letters) == 0
        
        # But should have operators
        assert syntax.premises[0].operator == TopOp
        assert syntax.premises[1].operator == BotOp


class TestCircularityCheck:
    """Test circularity detection in operator definitions."""
    
    def test_no_circularity(self):
        """Test that non-circular definitions pass."""
        class NotOp(Operator):
            name = "¬"
            arity = 1
            
        class OrOp(Operator):
            name = "∨"
            arity = 2
            
        class ImpliesOp(DefinedOperator):
            name = "→"
            arity = 2
            
            def derived_definition(self, p, q):
                return [OrOp, [NotOp, p], q]
        
        collection = OperatorCollection([NotOp, OrOp, ImpliesOp])
        # Should not raise any exception
        syntax = Syntax([], [], collection)
    
    def test_direct_circularity(self):
        """Test detection of direct circular dependency."""
        class AOp(DefinedOperator):
            name = "A"
            arity = 1
            
            def derived_definition(self, p):
                return [AOp, p]  # A defined in terms of itself
        
        collection = OperatorCollection(AOp)
        with pytest.raises(RecursionError, match="Circular definition detected"):
            Syntax([], [], collection)
    
    def test_indirect_circularity(self):
        """Test detection of indirect circular dependency."""
        class AOp(DefinedOperator):
            name = "A"
            arity = 1
            
            def derived_definition(self, p):
                return [BOp, p]
                
        class BOp(DefinedOperator):
            name = "B"
            arity = 1
            
            def derived_definition(self, p):
                return [AOp, p]  # B depends on A, A depends on B
        
        collection = OperatorCollection([AOp, BOp])
        with pytest.raises(RecursionError, match="Circular definition detected"):
            Syntax([], [], collection)
    
    def test_missing_dependency(self):
        """Test detection of missing operator dependency."""
        # Create a reference to a non-existent operator
        class OrOp:
            name = "∨"
            
        class NotOp(Operator):
            name = "¬"
            arity = 1
            
        class ImpliesOp(DefinedOperator):
            name = "→"
            arity = 2
            
            def derived_definition(self, p, q):
                # References OrOp which is not in collection
                return [OrOp, [NotOp, p], q]
        
        collection = OperatorCollection([NotOp, ImpliesOp])
        # Should raise ValueError about missing operator
        with pytest.raises(ValueError, match="depends on undefined operators"):
            Syntax([], [], collection)