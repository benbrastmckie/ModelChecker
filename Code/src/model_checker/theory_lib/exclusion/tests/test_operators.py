"""
Unit tests for exclusion theory operator implementations.

Tests validate individual operator implementations and their
semantic clauses work correctly.
"""

import pytest
import z3
from model_checker.theory_lib.exclusion.operators import (
    UniNegationOperator,
    UniConjunctionOperator,
    UniDisjunctionOperator,
    UniIdentityOperator,
    witness_operators
)
from model_checker.theory_lib.exclusion.semantic import WitnessSemantics
from model_checker import syntactic


class TestExclusionOperators:
    """Test exclusion operator implementations."""
    
    def test_exclusion_operators_available(self, exclusion_theory):
        """Test all exclusion operators are available."""
        operators = exclusion_theory['operators']
        
        # Check essential exclusion operators
        assert "\\func_unineg" in operators
        assert "\\uniwedge" in operators 
        assert "\\univee" in operators
        assert "\\uniequiv" in operators
        
    def test_operator_properties(self, exclusion_theory):
        """Test operator arity, names, and basic properties."""
        operators = exclusion_theory['operators']
        
        # Test uninegation properties
        unineg_op = operators["\\func_unineg"]
        assert unineg_op.name == "\\func_unineg"
        assert unineg_op.arity == 1
        
        # Test conjunction properties
        conj_op = operators["\\uniwedge"]
        assert conj_op.name == "\\uniwedge"
        assert conj_op.arity == 2
        
        # Test disjunction properties
        disj_op = operators["\\univee"]
        assert disj_op.name == "\\univee"
        assert disj_op.arity == 2
        
        # Test identity properties
        id_op = operators["\\uniequiv"]
        assert id_op.name == "\\uniequiv"
        assert id_op.arity == 2
        
    def test_uninegation_operator(self, exclusion_theory):
        """Test uninegation operator implementation."""
        operators = exclusion_theory['operators']
        unineg_op = operators["\\func_unineg"]
        
        # Test operator exists and has correct type
        assert unineg_op is not None
        assert issubclass(unineg_op, syntactic.Operator)
        assert hasattr(unineg_op, 'true_at')
        assert hasattr(unineg_op, 'extended_verify')
        assert hasattr(unineg_op, 'compute_verifiers')
        
    def test_binary_operators(self, exclusion_theory):
        """Test binary operator implementations."""
        operators = exclusion_theory['operators']
        
        # Test conjunction
        conj_op = operators["\\uniwedge"]
        assert conj_op is not None
        assert conj_op.arity == 2
        assert hasattr(conj_op, 'true_at')
        assert hasattr(conj_op, 'extended_verify')
        
        # Test disjunction
        disj_op = operators["\\univee"]
        assert disj_op is not None
        assert disj_op.arity == 2
        assert hasattr(disj_op, 'true_at')
        assert hasattr(disj_op, 'extended_verify')
        
        # Test identity
        id_op = operators["\\uniequiv"]
        assert id_op is not None
        assert id_op.arity == 2
        assert hasattr(id_op, 'true_at')
        assert hasattr(id_op, 'extended_verify')


class TestOperatorSemanticClauses:
    """Test operator semantic clause implementations."""
    
    def test_semantic_clause_structure(self, exclusion_theory):
        """Test semantic clauses have proper structure."""
        operators = exclusion_theory['operators']
        
        # Test that operators have semantic methods
        for op_name, operator in operators.items():
            assert hasattr(operator, 'true_at'), f"Operator {op_name} missing true_at method"
            assert hasattr(operator, 'extended_verify'), f"Operator {op_name} missing extended_verify method"
            
    def test_semantic_clause_execution(self, exclusion_theory, basic_settings):
        """Test semantic clauses can be executed."""
        # Get an operator class
        operators = exclusion_theory['operators']
        unineg_op_class = operators["\\func_unineg"]
        
        # Set up basic test structures
        semantics = WitnessSemantics(basic_settings)
        
        # Test that operator can be instantiated with semantics
        unineg_op = unineg_op_class(semantics)
        assert unineg_op is not None
        assert unineg_op.semantics is semantics
        
        # Test that the operator has the expected methods
        assert hasattr(unineg_op, 'true_at')
        assert hasattr(unineg_op, 'extended_verify')
        assert hasattr(unineg_op, 'compute_verifiers')
        
    def test_witness_aware_features(self, exclusion_theory, basic_settings):
        """Test witness-aware features of operators."""
        operators = exclusion_theory['operators']
        unineg_op_class = operators["\\func_unineg"]
        
        # The uninegation operator should have witness-specific methods
        assert hasattr(unineg_op_class, '_verifies_uninegation_with_predicates')
        assert hasattr(unineg_op_class, '_check_minimality')
        assert hasattr(unineg_op_class, '_eval_is_part_of')
        assert hasattr(unineg_op_class, '_eval_excludes')