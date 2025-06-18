"""
Unit tests for operator implementations.

Tests validate individual operator implementations and their
semantic clauses work correctly.
"""

import pytest
import z3
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.theory_lib.logos.semantic import LogosSemantics
from model_checker import syntactic


class TestExtensionalOperators:
    """Test extensional operator implementations."""
    
    def test_extensional_operators_available(self, extensional_theory):
        """Test all extensional operators are available."""
        operators = extensional_theory['operators']
        
        # Check essential extensional operators
        assert "\\neg" in operators
        assert "\\wedge" in operators 
        assert "\\vee" in operators
        assert "\\rightarrow" in operators
        
    def test_operator_properties(self, extensional_theory):
        """Test operator arity, names, and basic properties."""
        operators = extensional_theory['operators']
        
        # Test negation properties
        neg_op = operators["\\neg"]
        assert neg_op.name == "\\neg"
        assert neg_op.arity == 1
        
        # Test conjunction properties
        conj_op = operators["\\wedge"]
        assert conj_op.name == "\\wedge"
        assert conj_op.arity == 2
        
    def test_negation_operator(self, extensional_theory):
        """Test negation operator implementation."""
        operators = extensional_theory['operators']
        neg_op = operators["\\neg"]
        
        # Test operator exists and has correct type
        assert neg_op is not None
        assert issubclass(neg_op, syntactic.Operator)
        assert hasattr(neg_op, 'true_at')
        assert hasattr(neg_op, 'false_at')
        
    def test_binary_operators(self, extensional_theory):
        """Test binary operator implementations."""
        operators = extensional_theory['operators']
        
        # Test conjunction
        conj_op = operators["\\wedge"]
        assert conj_op is not None
        assert conj_op.arity == 2
        assert hasattr(conj_op, 'true_at')
        assert hasattr(conj_op, 'false_at')
        
        # Test disjunction
        disj_op = operators["\\vee"]
        assert disj_op is not None
        assert disj_op.arity == 2
        assert hasattr(disj_op, 'true_at')
        assert hasattr(disj_op, 'false_at')


class TestModalOperators:
    """Test modal operator implementations."""
    
    def test_modal_operators_available(self, modal_theory):
        """Test modal operators are correctly loaded."""
        operators = modal_theory['operators']
        
        # Should have extensional operators
        assert "\\neg" in operators
        assert "\\wedge" in operators
        
        # Should have modal operators
        assert "\\Box" in operators
        assert "\\Diamond" in operators
        
    def test_necessity_operator(self, modal_theory):
        """Test necessity operator implementation."""
        operators = modal_theory['operators']
        necessity_op = operators["\\Box"]
        
        assert necessity_op is not None
        assert necessity_op.name == "\\Box"
        assert necessity_op.arity == 1
        assert issubclass(necessity_op, syntactic.Operator)
        assert hasattr(necessity_op, 'true_at')
        assert hasattr(necessity_op, 'false_at')
        
    def test_possibility_operator(self, modal_theory):
        """Test possibility operator implementation."""
        operators = modal_theory['operators']
        possibility_op = operators["\\Diamond"]
        
        assert possibility_op is not None
        assert possibility_op.name == "\\Diamond"
        assert possibility_op.arity == 1
        assert issubclass(possibility_op, syntactic.Operator)
        # PossibilityOperator is a DefinedOperator
        assert hasattr(possibility_op, 'derived_definition')


class TestOperatorSemanticClauses:
    """Test operator semantic clause implementations."""
    
    def test_semantic_clause_structure(self, logos_theory):
        """Test semantic clauses have proper structure."""
        operators = logos_theory['operators']
        
        # Test that operators have semantic methods
        for op_name, operator in operators.items():
            # DefinedOperators may not have true_at/false_at methods directly
            if issubclass(operator, syntactic.DefinedOperator):
                assert hasattr(operator, 'derived_definition'), f"DefinedOperator {op_name} missing derived_definition method"
            else:
                assert hasattr(operator, 'true_at'), f"Operator {op_name} missing true_at method"
                assert hasattr(operator, 'false_at'), f"Operator {op_name} missing false_at method"
            
    def test_semantic_clause_execution(self, logos_theory, basic_settings):
        """Test semantic clauses can be executed."""
        # Get an operator class
        operators = logos_theory['operators']
        neg_op_class = operators["\\neg"]
        
        # Set up basic test structures
        registry = LogosOperatorRegistry()
        semantics = LogosSemantics(basic_settings, registry)
        
        # Test that operator can be instantiated with semantics
        neg_op = neg_op_class(semantics)
        assert neg_op is not None
        assert neg_op.semantics is semantics
        
        # Test that the operator has the expected methods
        assert hasattr(neg_op, 'true_at')
        assert hasattr(neg_op, 'false_at')
        assert hasattr(neg_op, 'extended_verify')
        assert hasattr(neg_op, 'extended_falsify')