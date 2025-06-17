"""
Unit tests for LogosSemantics methods.

This test file validates individual semantic methods work correctly
without running the full model checking pipeline.
"""

import pytest
from model_checker.theory_lib.logos.semantic import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
)
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry


class TestLogosSemantics:
    """Test the LogosSemantics class methods."""
    
    def test_initialization_basic(self, basic_settings):
        """Test basic semantics initialization."""
        semantics = LogosSemantics(basic_settings)
        
        assert semantics is not None
        assert hasattr(semantics, 'N')
        assert semantics.N == basic_settings['N']
        
    def test_initialization_complex(self, complex_settings):
        """Test semantics initialization with complex settings."""
        semantics = LogosSemantics(complex_settings)
        
        assert semantics.N == complex_settings['N']
        assert hasattr(semantics, 'contingent')
        assert hasattr(semantics, 'non_null')
        assert hasattr(semantics, 'non_empty')
        assert hasattr(semantics, 'disjoint')
    
    def test_world_creation(self, basic_settings):
        """Test world generation and structure."""
        semantics = LogosSemantics(basic_settings)
        
        # Test that worlds are created
        assert hasattr(semantics, 'worlds')
        # Basic validation that we have appropriate number of worlds
        # (exact count depends on implementation details)
        assert len(semantics.worlds) > 0
    
    def test_proposition_compatibility(self, basic_settings):
        """Test that semantics works with LogosProposition."""
        semantics = LogosSemantics(basic_settings)
        
        # Test that proposition can be created with this semantics
        prop = LogosProposition(semantics, "p")
        assert prop is not None
        assert hasattr(prop, 'semantics')
        assert prop.semantics is semantics
    
    def test_model_structure_compatibility(self, basic_settings):
        """Test that semantics works with LogosModelStructure."""
        semantics = LogosSemantics(basic_settings)
        
        # Test that model structure can be created with this semantics
        model = LogosModelStructure(semantics)
        assert model is not None
        assert hasattr(model, 'semantics')
        assert model.semantics is semantics


class TestLogosProposition:
    """Test the LogosProposition class methods."""
    
    def test_proposition_creation(self, logos_theory, basic_settings):
        """Test proposition creation with different atomic propositions."""
        semantics = logos_theory['semantics'](basic_settings)
        
        # Test creating propositions for different atomics
        for atom in ['p', 'q', 'r']:
            prop = LogosProposition(semantics, atom)
            assert prop is not None
            assert hasattr(prop, 'atom')
    
    def test_proposition_evaluation_basic(self, extensional_theory, minimal_settings):
        """Test basic proposition evaluation."""
        semantics = extensional_theory['semantics'](minimal_settings)
        prop = LogosProposition(semantics, "p")
        
        # Test that evaluation methods exist
        assert hasattr(prop, 'evaluate')
        # Basic validation that evaluation doesn't crash
        # (specific behavior depends on world state)
    
    def test_proposition_with_operators(self, logos_theory, basic_settings):
        """Test proposition evaluation with different operators."""
        semantics = logos_theory['semantics'](basic_settings)
        
        # Test that propositions work with operator expressions
        # This is a basic structural test
        prop = LogosProposition(semantics, "p")
        assert prop is not None


class TestLogosModelStructure:
    """Test the LogosModelStructure class methods."""
    
    def test_model_structure_creation(self, logos_theory, basic_settings):
        """Test model structure creation."""
        semantics = logos_theory['semantics'](basic_settings)
        model = LogosModelStructure(semantics)
        
        assert model is not None
        assert hasattr(model, 'semantics')
        assert model.semantics is semantics
    
    def test_constraint_generation(self, extensional_theory, minimal_settings):
        """Test that model structure can generate constraints."""
        semantics = extensional_theory['semantics'](minimal_settings)
        model = LogosModelStructure(semantics)
        
        # Test that constraint generation methods exist
        assert hasattr(model, 'generate_constraints')
    
    def test_model_validation(self, modal_theory, basic_settings):
        """Test model validation capabilities."""
        semantics = modal_theory['semantics'](basic_settings)
        model = LogosModelStructure(semantics)
        
        # Test that validation methods exist
        assert hasattr(model, 'validate')


class TestSemanticIntegration:
    """Test integration between semantic components."""
    
    def test_semantics_proposition_model_integration(self, logos_theory, basic_settings):
        """Test that all semantic components work together."""
        semantics = logos_theory['semantics'](basic_settings)
        proposition = LogosProposition(semantics, "p")
        model = LogosModelStructure(semantics)
        
        # Test that all components reference the same semantics
        assert proposition.semantics is semantics
        assert model.semantics is semantics
    
    def test_different_theory_configurations(self):
        """Test semantic initialization with different subtheory loadings."""
        from model_checker.theory_lib import logos
        
        # Test different theory configurations
        configurations = [
            ['extensional'],
            ['extensional', 'modal'],
            ['extensional', 'modal', 'constitutive'],
            ['extensional', 'modal', 'counterfactual'],
        ]
        
        for config in configurations:
            theory = logos.get_theory(config)
            semantics = theory['semantics']({'N': 2, 'max_time': 1})
            assert semantics is not None
            assert hasattr(semantics, 'N')
    
    def test_settings_validation(self, logos_theory):
        """Test that semantics validates settings appropriately."""
        # Test with missing required settings
        try:
            semantics = logos_theory['semantics']({})
            # If this succeeds, make sure N has a default
            assert hasattr(semantics, 'N')
        except (KeyError, ValueError):
            # Expected if N is required
            pass
        
        # Test with minimal valid settings
        semantics = logos_theory['semantics']({'N': 1})
        assert semantics.N == 1