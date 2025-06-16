"""
Tests for individual logos subtheories.

This test suite validates each subtheory in isolation to ensure
proper operator implementation and semantic behavior.
"""

import pytest

from model_checker.theory_lib.logos.subtheories import (
    extensional,
    modal, 
    constitutive,
    counterfactual,
)


class TestExtensionalSubtheory:
    """Test the extensional subtheory operators."""
    
    def test_extensional_operators_available(self):
        """Test that all extensional operators are available."""
        operators = extensional.get_operators()
        expected_ops = ["\\neg", "\\wedge", "\\vee", "\\top", "\\bot", "\\rightarrow", "\\leftrightarrow"]
        
        assert len(operators) == 7
        for op in expected_ops:
            assert op in operators
            assert operators[op] is not None
    
    def test_operator_arities(self):
        """Test that operators have correct arities."""
        operators = extensional.get_operators()
        
        # Unary operators
        assert operators["\\neg"].arity == 1
        assert operators["\\top"].arity == 0
        assert operators["\\bot"].arity == 0
        
        # Binary operators
        assert operators["\\wedge"].arity == 2
        assert operators["\\vee"].arity == 2
        assert operators["\\rightarrow"].arity == 2
        assert operators["\\leftrightarrow"].arity == 2
    
    def test_operator_names(self):
        """Test that operators have correct names."""
        operators = extensional.get_operators()
        
        for op_name, op_class in operators.items():
            assert op_class.name == op_name


class TestModalSubtheory:
    """Test the modal subtheory operators."""
    
    def test_modal_operators_available(self):
        """Test that all modal operators are available."""
        operators = modal.get_operators()
        expected_ops = ["\\Box", "\\Diamond", "\\CFBox", "\\CFDiamond"]
        
        assert len(operators) == 4
        for op in expected_ops:
            assert op in operators
            assert operators[op] is not None
    
    def test_modal_operator_arities(self):
        """Test that modal operators have correct arities."""
        operators = modal.get_operators()
        
        # All modal operators are unary
        for op_class in operators.values():
            assert op_class.arity == 1
    
    def test_defined_operators(self):
        """Test that defined operators are properly configured."""
        operators = modal.get_operators()
        
        # PossibilityOperator is defined
        from model_checker.syntactic import DefinedOperator
        assert issubclass(operators["\\Diamond"], DefinedOperator)
        assert issubclass(operators["\\CFBox"], DefinedOperator)
        assert issubclass(operators["\\CFDiamond"], DefinedOperator)


class TestConstitutiveSubtheory:
    """Test the constitutive subtheory operators."""
    
    def test_constitutive_operators_available(self):
        """Test that all constitutive operators are available."""
        operators = constitutive.get_operators()
        expected_ops = ["\\equiv", "\\leq", "\\sqsubseteq", "\\preceq", "\\reduction"]
        
        assert len(operators) == 5
        for op in expected_ops:
            assert op in operators
            assert operators[op] is not None
    
    def test_constitutive_operator_arities(self):
        """Test that constitutive operators have correct arities."""
        operators = constitutive.get_operators()
        
        # All constitutive operators are binary
        for op_class in operators.values():
            assert op_class.arity == 2
    
    def test_reduction_operator_defined(self):
        """Test that reduction operator is properly defined."""
        operators = constitutive.get_operators()
        
        from model_checker.syntactic import DefinedOperator
        assert issubclass(operators["\\reduction"], DefinedOperator)


class TestCounterfactualSubtheory:
    """Test the counterfactual subtheory operators."""
    
    def test_counterfactual_operators_available(self):
        """Test that all counterfactual operators are available."""
        operators = counterfactual.get_operators()
        expected_ops = ["\\boxright", "\\diamondright", "\\imposition", "\\could"]
        
        assert len(operators) == 4
        for op in expected_ops:
            assert op in operators
            assert operators[op] is not None
    
    def test_counterfactual_operator_arities(self):
        """Test that counterfactual operators have correct arities."""
        operators = counterfactual.get_operators()
        
        # All counterfactual operators are binary
        for op_class in operators.values():
            assert op_class.arity == 2
    
    def test_defined_counterfactual_operators(self):
        """Test that defined counterfactual operators are properly configured."""
        operators = counterfactual.get_operators()
        
        from model_checker.syntactic import DefinedOperator
        assert issubclass(operators["\\diamondright"], DefinedOperator)
        assert issubclass(operators["\\could"], DefinedOperator)


class TestSubtheoryIsolation:
    """Test that subtheories can work in isolation."""
    
    def test_extensional_isolation(self):
        """Test extensional operators work without other subtheories."""
        operators = extensional.get_operators()
        
        # Should be able to get operators without dependencies
        assert len(operators) > 0
        
        # Each operator should have required methods
        for op_class in operators.values():
            assert hasattr(op_class, 'name')
            assert hasattr(op_class, 'arity')
    
    def test_modal_isolation(self):
        """Test modal operators work in isolation."""
        operators = modal.get_operators()
        
        # Should be able to get operators
        assert len(operators) > 0
        
        # Check basic operator structure
        for op_class in operators.values():
            assert hasattr(op_class, 'name')
            assert hasattr(op_class, 'arity')
    
    def test_constitutive_isolation(self):
        """Test constitutive operators work in isolation."""
        operators = constitutive.get_operators()
        
        # Should be able to get operators
        assert len(operators) > 0
        
        # Check basic operator structure  
        for op_class in operators.values():
            assert hasattr(op_class, 'name')
            assert hasattr(op_class, 'arity')
    
    def test_counterfactual_isolation(self):
        """Test counterfactual operators work in isolation."""
        operators = counterfactual.get_operators()
        
        # Should be able to get operators
        assert len(operators) > 0
        
        # Check basic operator structure
        for op_class in operators.values():
            assert hasattr(op_class, 'name')
            assert hasattr(op_class, 'arity')


if __name__ == "__main__":
    pytest.main([__file__])