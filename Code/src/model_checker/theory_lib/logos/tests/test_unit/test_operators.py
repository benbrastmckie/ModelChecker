"""
Unit tests for operator implementations.

This test file validates individual operator implementations and their
semantic clauses work correctly.
"""

import pytest
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry


class TestExtensionalOperators:
    """Test extensional (truth-functional) operator implementations."""
    
    def test_extensional_operators_available(self, extensional_theory):
        """Test that all extensional operators are available."""
        operators = extensional_theory['operators']
        
        expected_operators = [
            "\\neg", "\\wedge", "\\vee", "\\top", "\\bot", 
            "\\rightarrow", "\\leftrightarrow"
        ]
        
        for op in expected_operators:
            assert op in operators.operator_dictionary, f"Missing operator: {op}"
    
    def test_negation_operator(self, extensional_theory):
        """Test negation operator properties."""
        operators = extensional_theory['operators']
        neg_op = operators.operator_dictionary["\\neg"]
        
        assert neg_op is not None
        assert hasattr(neg_op, 'arity')
        assert neg_op.arity == 1
        assert hasattr(neg_op, 'name')
        assert neg_op.name == "\\neg"
    
    def test_binary_operators(self, extensional_theory):
        """Test binary operator properties."""
        operators = extensional_theory['operators']
        
        binary_ops = ["\\wedge", "\\vee", "\\rightarrow", "\\leftrightarrow"]
        
        for op_name in binary_ops:
            op = operators.operator_dictionary[op_name]
            assert op.arity == 2, f"Operator {op_name} should have arity 2"
            assert op.name == op_name
    
    def test_nullary_operators(self, extensional_theory):
        """Test nullary operator properties."""
        operators = extensional_theory['operators']
        
        nullary_ops = ["\\top", "\\bot"]
        
        for op_name in nullary_ops:
            op = operators.operator_dictionary[op_name]
            assert op.arity == 0, f"Operator {op_name} should have arity 0"
            assert op.name == op_name


class TestModalOperators:
    """Test modal operator implementations."""
    
    def test_modal_operators_available(self, modal_theory):
        """Test that all modal operators are available."""
        operators = modal_theory['operators']
        
        # Should have extensional + modal operators
        expected_modal = ["\\Box", "\\Diamond", "\\CFBox", "\\CFDiamond"]
        expected_extensional = ["\\neg", "\\wedge", "\\vee", "\\top", "\\bot", 
                              "\\rightarrow", "\\leftrightarrow"]
        
        for op in expected_modal + expected_extensional:
            assert op in operators.operator_dictionary, f"Missing operator: {op}"
    
    def test_modal_operator_arities(self, modal_theory):
        """Test modal operator arities."""
        operators = modal_theory['operators']
        
        modal_ops = ["\\Box", "\\Diamond", "\\CFBox", "\\CFDiamond"]
        
        for op_name in modal_ops:
            op = operators.operator_dictionary[op_name]
            assert op.arity == 1, f"Modal operator {op_name} should have arity 1"
            assert op.name == op_name
    
    def test_modal_operator_types(self, modal_theory):
        """Test that modal operators have correct types."""
        operators = modal_theory['operators']
        
        box_op = operators.operator_dictionary["\\Box"]
        diamond_op = operators.operator_dictionary["\\Diamond"]
        
        # Test that they are proper operator instances
        assert hasattr(box_op, 'evaluate')
        assert hasattr(diamond_op, 'evaluate')


class TestConstitutiveOperators:
    """Test constitutive operator implementations."""
    
    def test_constitutive_operators_available(self, constitutive_theory):
        """Test that all constitutive operators are available."""
        operators = constitutive_theory['operators']
        
        expected_constitutive = ["\\equiv", "\\leq", "\\sqsubseteq", "\\preceq", "\\reduction"]
        
        for op in expected_constitutive:
            assert op in operators.operator_dictionary, f"Missing constitutive operator: {op}"
    
    def test_constitutive_operator_arities(self, constitutive_theory):
        """Test constitutive operator arities."""
        operators = constitutive_theory['operators']
        
        # Most constitutive operators are binary
        binary_ops = ["\\equiv", "\\leq", "\\sqsubseteq", "\\preceq"]
        
        for op_name in binary_ops:
            op = operators.operator_dictionary[op_name]
            assert op.arity == 2, f"Constitutive operator {op_name} should have arity 2"
    
    def test_reduction_operator(self, constitutive_theory):
        """Test reduction operator specifically."""
        operators = constitutive_theory['operators']
        reduction_op = operators.operator_dictionary["\\reduction"]
        
        assert reduction_op is not None
        assert hasattr(reduction_op, 'arity')
        assert hasattr(reduction_op, 'name')
        assert reduction_op.name == "\\reduction"


class TestCounterfactualOperators:
    """Test counterfactual operator implementations."""
    
    def test_counterfactual_operators_available(self, counterfactual_theory):
        """Test that all counterfactual operators are available."""
        operators = counterfactual_theory['operators']
        
        expected_counterfactual = ["\\boxright", "\\diamondright", "\\imposition", "\\could"]
        
        for op in expected_counterfactual:
            assert op in operators.operator_dictionary, f"Missing counterfactual operator: {op}"
    
    def test_counterfactual_operator_arities(self, counterfactual_theory):
        """Test counterfactual operator arities."""
        operators = counterfactual_theory['operators']
        
        # Counterfactual operators are typically binary
        binary_ops = ["\\boxright", "\\diamondright", "\\imposition"]
        
        for op_name in binary_ops:
            op = operators.operator_dictionary[op_name]
            assert op.arity == 2, f"Counterfactual operator {op_name} should have arity 2"
    
    def test_could_operator(self, counterfactual_theory):
        """Test 'could' operator specifically."""
        operators = counterfactual_theory['operators']
        could_op = operators.operator_dictionary["\\could"]
        
        assert could_op is not None
        assert hasattr(could_op, 'arity')
        # Could is typically unary
        assert could_op.arity == 1


class TestRelevanceOperators:
    """Test relevance operator implementations."""
    
    def test_relevance_theory_loading(self, relevance_theory):
        """Test that relevance theory loads with all dependencies."""
        operators = relevance_theory['operators']
        
        # Should have operators from extensional + modal + constitutive + relevance
        assert len(operators.operator_dictionary) > 15
    
    def test_relevance_operator_access(self, relevance_theory):
        """Test that relevance operators are accessible."""
        operators = relevance_theory['operators']
        
        # Test that we can access operators (exact names depend on implementation)
        assert len(operators.operator_dictionary) > 0
        
        # Verify that dependency operators are present
        assert "\\neg" in operators.operator_dictionary  # extensional
        assert "\\Box" in operators.operator_dictionary  # modal  
        assert "\\equiv" in operators.operator_dictionary  # constitutive


class TestOperatorIntegration:
    """Test integration between different operator types."""
    
    def test_operator_registry_loading(self):
        """Test operator registry loading mechanisms."""
        registry = LogosOperatorRegistry()
        
        # Test loading individual subtheories
        registry.load_subtheories(['extensional'])
        ext_count = len(registry.get_operators().operator_dictionary)
        
        # Test loading additional subtheories
        registry.load_subtheories(['extensional', 'modal'])
        modal_count = len(registry.get_operators().operator_dictionary)
        
        assert modal_count > ext_count, "Adding modal should increase operator count"
    
    def test_operator_dependencies(self):
        """Test that operator dependencies are resolved correctly."""
        registry = LogosOperatorRegistry()
        
        # Modal requires extensional
        registry.load_subtheories(['modal', 'extensional'])
        operators = registry.get_operators()
        
        # Should have both extensional and modal operators
        assert "\\neg" in operators.operator_dictionary  # extensional
        assert "\\Box" in operators.operator_dictionary  # modal
    
    def test_all_subtheories_together(self, logos_theory):
        """Test that all subtheories can be loaded together."""
        operators = logos_theory['operators']
        
        # Test that we have a reasonable number of operators
        assert len(operators.operator_dictionary) >= 15
        
        # Test that operators from each subtheory are present
        assert "\\neg" in operators.operator_dictionary  # extensional
        assert "\\Box" in operators.operator_dictionary  # modal
        assert "\\equiv" in operators.operator_dictionary  # constitutive
        assert "\\boxright" in operators.operator_dictionary  # counterfactual
    
    def test_operator_uniqueness(self, logos_theory):
        """Test that operator names are unique."""
        operators = logos_theory['operators']
        
        # Get all operator names
        names = list(operators.operator_dictionary.keys())
        
        # Check for duplicates
        assert len(names) == len(set(names)), "Operator names should be unique"
    
    def test_operator_evaluation_methods(self, logos_theory):
        """Test that operators have required evaluation methods."""
        operators = logos_theory['operators']
        
        # Test a few key operators
        test_operators = ["\\neg", "\\wedge", "\\Box"]
        
        for op_name in test_operators:
            if op_name in operators.operator_dictionary:
                op = operators.operator_dictionary[op_name]
                assert hasattr(op, 'evaluate'), f"Operator {op_name} should have evaluate method"