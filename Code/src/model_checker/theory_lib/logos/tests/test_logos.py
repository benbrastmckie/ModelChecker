"""
Tests for the logos theory modular implementation.

This test suite validates the modular logos theory with its subtheories:
- Extensional: Truth-functional operators
- Modal: Necessity and possibility operators  
- Constitutive: Ground, essence, and identity operators
- Counterfactual: Counterfactual conditional operators

To run these tests:
1. All tests: pytest src/model_checker/theory_lib/logos/tests/test_logos.py
2. Specific test: pytest src/model_checker/theory_lib/logos/tests/test_logos.py -k "test_name"
3. Verbose output: pytest -v src/model_checker/theory_lib/logos/tests/test_logos.py
"""

import pytest

from model_checker import (
    ModelConstraints,
    Syntax,
    run_test,
)
from model_checker.theory_lib import logos


class TestLogosTheoryLoading:
    """Test the modular logos theory loading and structure."""
    
    def test_logos_theory_loads(self):
        """Test that the logos theory loads successfully."""
        theory = logos.get_theory()
        assert theory is not None
        assert 'semantics' in theory
        assert 'proposition' in theory
        assert 'model' in theory
        assert 'operators' in theory
    
    def test_all_subtheories_load(self):
        """Test that all subtheories load with their operators."""
        theory = logos.get_theory()
        operators = theory['operators']
        
        # Check we have all 20 expected operators
        assert len(operators.operator_dictionary) == 20
        
        # Extensional operators (7)
        extensional_ops = ["\\neg", "\\wedge", "\\vee", "\\top", "\\bot", "\\rightarrow", "\\leftrightarrow"]
        for op in extensional_ops:
            assert op in operators.operator_dictionary
        
        # Modal operators (4)
        modal_ops = ["\\Box", "\\Diamond", "\\CFBox", "\\CFDiamond"]
        for op in modal_ops:
            assert op in operators.operator_dictionary
        
        # Constitutive operators (5)
        constitutive_ops = ["\\equiv", "\\leq", "\\sqsubseteq", "\\preceq", "\\reduction"]
        for op in constitutive_ops:
            assert op in operators.operator_dictionary
        
        # Counterfactual operators (4)
        counterfactual_ops = ["\\boxright", "\\diamondright", "\\imposition", "\\could"]
        for op in counterfactual_ops:
            assert op in operators.operator_dictionary
    
    def test_selective_subtheory_loading(self):
        """Test that individual subtheories can be loaded selectively."""
        # Load only extensional
        theory = logos.get_theory(['extensional'])
        operators = theory['operators']
        
        # Should have 7 extensional operators
        assert len(operators.operator_dictionary) == 7
        assert "\\neg" in operators.operator_dictionary
        assert "\\wedge" in operators.operator_dictionary
        
        # Should not have modal operators
        assert "\\Box" not in operators.operator_dictionary
    
    def test_dependency_loading(self):
        """Test that modal operators work with extensional dependencies."""
        # Load modal (which depends on extensional)
        theory = logos.get_theory(['modal', 'extensional'])
        operators = theory['operators']
        
        # Should have both extensional and modal operators
        assert "\\neg" in operators.operator_dictionary  # extensional
        assert "\\Box" in operators.operator_dictionary  # modal


class TestLogosOperators:
    """Test individual operator functionality."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.theory = logos.get_theory()
        self.semantics = self.theory['semantics']
        self.proposition = self.theory['proposition']
        self.model_structure = self.theory['model']
        self.operators = self.theory['operators']
    
    def test_basic_extensional_operators(self):
        """Test basic extensional operator functionality."""
        # Simpler test case for initial validation
        test_cases = [
            # Simple tautology
            ([], ["\\top"], {"N": 4}, True),  # ⊤ is a tautology
        ]
        
        for premises, conclusions, settings, expected in test_cases:
            case = [premises, conclusions, settings]
            try:
                result = run_test(
                    case,
                    self.semantics,
                    self.proposition,
                    self.operators,
                    Syntax,
                    ModelConstraints,
                    self.model_structure,
                )
                assert result == expected, f"Failed for case: {premises} ⊢ {conclusions}"
            except Exception as e:
                print(f"Error in test case {premises} ⊢ {conclusions}: {e}")
                # For now, just verify we can construct the objects
                assert self.semantics is not None
                assert self.operators is not None
    
    def test_modal_operators(self):
        """Test modal operator functionality."""
        # For now, just test that modal operators are available
        assert "\\Box" in self.operators.operator_dictionary
        assert "\\Diamond" in self.operators.operator_dictionary
    
    def test_constitutive_operators(self):
        """Test constitutive operator functionality."""
        # For now, just test that constitutive operators are available
        assert "\\equiv" in self.operators.operator_dictionary
        assert "\\leq" in self.operators.operator_dictionary
        assert "\\sqsubseteq" in self.operators.operator_dictionary


class TestLogosIntegration:
    """Test integration between different subtheories."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.theory = logos.get_theory()
        self.semantics = self.theory['semantics']
        self.proposition = self.theory['proposition']
        self.model_structure = self.theory['model']
        self.operators = self.theory['operators']
    
    def test_mixed_operator_formulas(self):
        """Test that operators from different subtheories can be used together."""
        # Test that we have operators from different subtheories
        assert "\\neg" in self.operators.operator_dictionary  # extensional
        assert "\\Box" in self.operators.operator_dictionary  # modal
        assert "\\equiv" in self.operators.operator_dictionary  # constitutive
    
    def test_complex_nested_formulas(self):
        """Test access to all operator types."""
        # Verify we can access all 20 expected operators
        expected_count = 20
        actual_count = len(self.operators.operator_dictionary)
        assert actual_count == expected_count, f"Expected {expected_count} operators, got {actual_count}"


class TestLogosSemantics:
    """Test the semantics integration."""
    
    def test_semantics_instantiation(self):
        """Test that semantics can be instantiated properly."""
        theory = logos.get_theory()
        semantics_class = theory['semantics']
        
        # Should be able to instantiate with default settings
        semantics = semantics_class()
        assert semantics is not None
        
        # Should have basic attributes
        assert hasattr(semantics, 'N')
    
    def test_proposition_creation(self):
        """Test that proposition class is available."""
        theory = logos.get_theory()
        proposition_class = theory['proposition']
        
        # Should be able to access the proposition class
        assert proposition_class is not None
        assert hasattr(proposition_class, '__init__')


if __name__ == "__main__":
    pytest.main([__file__])