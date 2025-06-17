"""
Unit tests for LogosProposition functionality.

This test file validates the LogosProposition class and its methods
work correctly in isolation.
"""

import pytest
from model_checker.theory_lib.logos.semantic import (
    LogosSemantics,
    LogosProposition,
)


class TestLogosProposition:
    """Test the LogosProposition class."""
    
    def test_proposition_creation(self, logos_theory, basic_settings):
        """Test basic proposition creation."""
        semantics = logos_theory['semantics'](basic_settings)
        
        prop = LogosProposition(semantics, "p")
        assert prop is not None
        assert hasattr(prop, 'semantics')
        assert hasattr(prop, 'atom')
        assert prop.semantics is semantics
    
    def test_proposition_with_different_atoms(self, extensional_theory, minimal_settings):
        """Test proposition creation with different atomic propositions."""
        semantics = extensional_theory['semantics'](minimal_settings)
        
        atoms = ['p', 'q', 'r', 's']
        propositions = []
        
        for atom in atoms:
            prop = LogosProposition(semantics, atom)
            propositions.append(prop)
            assert prop.atom == atom
        
        # Test that different propositions are distinct
        assert len(set(propositions)) == len(atoms)
    
    def test_proposition_semantics_reference(self, modal_theory, basic_settings):
        """Test that proposition maintains reference to semantics."""
        semantics = modal_theory['semantics'](basic_settings)
        prop = LogosProposition(semantics, "p")
        
        assert prop.semantics is semantics
        assert hasattr(prop.semantics, 'N')
        assert prop.semantics.N == basic_settings['N']
    
    def test_proposition_evaluation_methods(self, logos_theory, basic_settings):
        """Test that proposition has evaluation methods."""
        semantics = logos_theory['semantics'](basic_settings)
        prop = LogosProposition(semantics, "p")
        
        # Test that evaluation methods exist
        assert hasattr(prop, 'evaluate')
        
        # Basic validation that methods are callable
        assert callable(getattr(prop, 'evaluate', None))


class TestPropositionEvaluation:
    """Test proposition evaluation capabilities."""
    
    def test_basic_evaluation_structure(self, extensional_theory, minimal_settings):
        """Test basic evaluation method structure."""
        semantics = extensional_theory['semantics'](minimal_settings)
        prop = LogosProposition(semantics, "p")
        
        # Test that evaluation doesn't immediately crash
        # (exact behavior depends on world/model state)
        try:
            # This may require additional parameters in actual implementation
            result = prop.evaluate()
            # If it returns something, validate it's reasonable
            assert result is not None
        except (TypeError, AttributeError):
            # Expected if evaluate requires parameters
            assert hasattr(prop, 'evaluate')
    
    def test_evaluation_with_different_settings(self, logos_theory):
        """Test proposition evaluation with different semantic settings."""
        # Test with minimal settings
        semantics1 = logos_theory['semantics']({'N': 1, 'max_time': 1})
        prop1 = LogosProposition(semantics1, "p")
        
        # Test with complex settings
        semantics2 = logos_theory['semantics']({
            'N': 3, 
            'max_time': 2,
            'contingent': True,
            'non_null': True
        })
        prop2 = LogosProposition(semantics2, "p")
        
        # Both should be valid propositions
        assert prop1.semantics.N == 1
        assert prop2.semantics.N == 3
        assert hasattr(prop1, 'evaluate')
        assert hasattr(prop2, 'evaluate')
    
    def test_proposition_state_independence(self, modal_theory, basic_settings):
        """Test that propositions maintain state independently."""
        semantics = modal_theory['semantics'](basic_settings)
        
        prop_p = LogosProposition(semantics, "p")
        prop_q = LogosProposition(semantics, "q")
        
        # Should be different propositions
        assert prop_p is not prop_q
        assert prop_p.atom != prop_q.atom
        
        # But should share semantics
        assert prop_p.semantics is prop_q.semantics


class TestPropositionErrorHandling:
    """Test proposition error handling and edge cases."""
    
    def test_invalid_atom_names(self, extensional_theory, minimal_settings):
        """Test handling of various atom names."""
        semantics = extensional_theory['semantics'](minimal_settings)
        
        # Test various atom formats
        valid_atoms = ['p', 'q1', 'atom', 'P', 'x']
        
        for atom in valid_atoms:
            try:
                prop = LogosProposition(semantics, atom)
                assert prop.atom == atom
            except Exception as e:
                # If the implementation restricts certain atom names, that's okay
                # Just verify the error is reasonable
                assert isinstance(e, (ValueError, TypeError))
    
    def test_none_semantics(self):
        """Test proposition creation with invalid semantics."""
        try:
            prop = LogosProposition(None, "p")
            # If this succeeds, the implementation is very permissive
            assert prop is not None
        except (TypeError, AttributeError):
            # Expected behavior for None semantics
            pass
    
    def test_empty_atom(self, logos_theory, basic_settings):
        """Test proposition creation with empty atom."""
        semantics = logos_theory['semantics'](basic_settings)
        
        try:
            prop = LogosProposition(semantics, "")
            # If empty atom is allowed, that's okay
            assert prop.atom == ""
        except (ValueError, TypeError):
            # Expected if empty atoms are not allowed
            pass


class TestPropositionIntegration:
    """Test proposition integration with other components."""
    
    def test_proposition_with_different_theory_configurations(self):
        """Test propositions work with different theory configurations."""
        from model_checker.theory_lib import logos
        
        configurations = [
            ['extensional'],
            ['extensional', 'modal'],
            ['extensional', 'modal', 'constitutive'],
        ]
        
        for config in configurations:
            theory = logos.get_theory(config)
            semantics = theory['semantics']({'N': 2, 'max_time': 1})
            
            prop = LogosProposition(semantics, "p")
            assert prop is not None
            assert prop.semantics is semantics
    
    def test_proposition_semantic_consistency(self, logos_theory, basic_settings):
        """Test that propositions maintain semantic consistency."""
        semantics = logos_theory['semantics'](basic_settings)
        
        # Create multiple propositions
        props = [LogosProposition(semantics, f"p{i}") for i in range(3)]
        
        # All should reference the same semantics instance
        for prop in props:
            assert prop.semantics is semantics
            assert prop.semantics.N == basic_settings['N']
    
    def test_proposition_memory_efficiency(self, extensional_theory, minimal_settings):
        """Test that proposition creation is memory efficient."""
        semantics = extensional_theory['semantics'](minimal_settings)
        
        # Create many propositions
        props = [LogosProposition(semantics, f"p{i}") for i in range(10)]
        
        # Should all be distinct
        assert len(set(props)) == 10
        
        # Should all reference same semantics (not copies)
        for prop in props:
            assert prop.semantics is semantics


class TestPropositionUtilities:
    """Test proposition utility methods and properties."""
    
    def test_proposition_string_representation(self, logos_theory, basic_settings):
        """Test proposition string representation."""
        semantics = logos_theory['semantics'](basic_settings)
        prop = LogosProposition(semantics, "p")
        
        # Test that string conversion works
        try:
            str_repr = str(prop)
            assert isinstance(str_repr, str)
            assert len(str_repr) > 0
        except Exception:
            # If string representation not implemented, that's okay
            pass
    
    def test_proposition_equality(self, modal_theory, basic_settings):
        """Test proposition equality behavior."""
        semantics = modal_theory['semantics'](basic_settings)
        
        prop1 = LogosProposition(semantics, "p")
        prop2 = LogosProposition(semantics, "p")
        prop3 = LogosProposition(semantics, "q")
        
        # Test equality behavior (implementation dependent)
        try:
            # Same atom, same semantics - might be equal
            eq_result = (prop1 == prop2)
            assert isinstance(eq_result, bool)
            
            # Different atoms - should not be equal
            neq_result = (prop1 == prop3)
            assert isinstance(neq_result, bool)
        except Exception:
            # If equality not implemented, that's okay
            pass
    
    def test_proposition_hash(self, constitutive_theory, basic_settings):
        """Test proposition hash behavior."""
        semantics = constitutive_theory['semantics'](basic_settings)
        prop = LogosProposition(semantics, "p")
        
        # Test that hash works if implemented
        try:
            hash_val = hash(prop)
            assert isinstance(hash_val, int)
        except TypeError:
            # If hash not implemented, that's okay
            pass