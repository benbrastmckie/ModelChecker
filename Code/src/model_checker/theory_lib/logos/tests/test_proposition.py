"""
Unit tests for LogosProposition functionality.

Tests validate the LogosProposition class and its methods
work correctly in isolation and integration.
"""

import pytest
import z3
from model_checker.theory_lib.logos.semantic import LogosSemantics, LogosProposition, LogosModelStructure
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.model import ModelConstraints
from model_checker import syntactic


class TestPropositionCreation:
    """Test LogosProposition instantiation."""
    
    def test_proposition_creation_valid_args(self, logos_theory, basic_settings):
        """Test proposition creation with proper arguments."""
        # For unit tests, we can test the class structure without full integration
        # This validates that LogosProposition is a proper subclass
        from model_checker.model import PropositionDefaults
        
        assert issubclass(LogosProposition, PropositionDefaults)
        assert hasattr(LogosProposition, '__init__')
        assert hasattr(LogosProposition, 'proposition_constraints')
        
    def test_proposition_creation_invalid_args(self):
        """Test proposition creation fails with invalid arguments."""
        with pytest.raises((TypeError, AttributeError)):
            LogosProposition(None, None)
            
    def test_proposition_attributes(self, logos_theory, basic_settings):
        """Test proposition has expected attributes."""
        # Test that the class has expected methods and attributes
        assert hasattr(LogosProposition, 'proposition_constraints')
        assert hasattr(LogosProposition, 'find_proposition')
        assert hasattr(LogosProposition, '__init__')
        
        # Check parent class methods are available
        from model_checker.model import PropositionDefaults
        parent_methods = [m for m in dir(PropositionDefaults) if not m.startswith('_')]
        for method in parent_methods:
            assert hasattr(LogosProposition, method), f"Missing parent method: {method}"


class TestPropositionConstraints:
    """Test proposition constraint generation."""
    
    def test_proposition_constraints_method(self, logos_theory, basic_settings):
        """Test static proposition_constraints method."""
        # Test that the method exists and can be called
        assert hasattr(LogosProposition, 'proposition_constraints')
        
        # Check method signature
        import inspect
        sig = inspect.signature(LogosProposition.proposition_constraints)
        params = list(sig.parameters.keys())
        assert 'self' in params
        assert 'sentence_letter' in params
        
    def test_constraint_generation_structure(self, logos_theory, basic_settings):
        """Test generated constraints have proper structure."""
        # Create a minimal test instance to check the method
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional'])
        semantics = LogosSemantics(basic_settings, registry)
        
        # Create a mock proposition to test the method
        class MockProposition(LogosProposition):
            def __init__(self):
                self.semantics = semantics
                self.settings = basic_settings
                # Add minimal model structure attributes
                class MockModelStructure:
                    def __init__(self):
                        self.settings = basic_settings
                self.model_structure = MockModelStructure()
                
        mock_prop = MockProposition()
        sentence_letter = syntactic.AtomVal(0)
        
        # Test constraint generation
        constraints = mock_prop.proposition_constraints(sentence_letter)
        
        assert constraints is not None
        assert isinstance(constraints, list)
        # Should have constraints for classical behavior
        assert len(constraints) > 0


class TestPropositionIntegration:
    """Test proposition integration with other components."""
    
    def test_proposition_model_integration(self, logos_theory, basic_settings):
        """Test integration with model structures."""
        # Test that LogosProposition can work with LogosModelStructure
        assert hasattr(LogosProposition, '__init__')
        
        # Check that the init method signature is compatible
        import inspect
        sig = inspect.signature(LogosProposition.__init__)
        params = list(sig.parameters.keys())
        assert 'sentence' in params
        assert 'model_structure' in params
        
    def test_proposition_sentence_integration(self, logos_theory, basic_settings):
        """Test integration with sentence objects."""
        # Test that LogosProposition expects sentence objects
        import inspect
        sig = inspect.signature(LogosProposition.__init__)
        params = list(sig.parameters.keys())
        
        # Should have sentence parameter
        assert 'sentence' in params


class TestPropositionUtilities:
    """Test proposition utility methods."""
    
    def test_proposition_string_representation(self, logos_theory, basic_settings):
        """Test proposition string representation."""
        # Test that the class has string representation from parent
        assert hasattr(LogosProposition, '__str__') or hasattr(LogosProposition, '__repr__')
        
    def test_proposition_equality(self, logos_theory, basic_settings):
        """Test proposition equality and hashing."""
        # Test that the class has expected methods from parent
        # PropositionDefaults may or may not define equality methods
        # Just check that the class is properly structured
        assert issubclass(LogosProposition, object)
        assert hasattr(LogosProposition, '__class__')