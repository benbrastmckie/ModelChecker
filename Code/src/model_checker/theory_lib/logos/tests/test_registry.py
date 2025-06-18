"""
Unit tests for LogosOperatorRegistry functionality.

Tests validate the operator registry system works correctly
for loading and managing operators from different subtheories.
"""

import pytest
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.syntactic import OperatorCollection


class TestRegistryBasics:
    """Test basic registry functionality."""
    
    def test_registry_creation(self):
        """Test empty registry instantiation."""
        registry = LogosOperatorRegistry()
        
        assert registry is not None
        assert isinstance(registry.loaded_subtheories, dict)
        assert isinstance(registry.operator_collection, OperatorCollection)
        assert len(registry.loaded_subtheories) == 0
        
    def test_registry_initial_state(self):
        """Test registry initial state is correct."""
        registry = LogosOperatorRegistry()
        
        assert registry.dependencies is not None
        assert isinstance(registry.dependencies, dict)
        assert 'extensional' in registry.dependencies
        assert 'modal' in registry.dependencies
        assert 'constitutive' in registry.dependencies
        assert 'counterfactual' in registry.dependencies
        assert 'relevance' in registry.dependencies


class TestSubtheoryLoading:
    """Test subtheory loading functionality."""
    
    def test_load_single_subtheory(self):
        """Test loading individual subtheories."""
        registry = LogosOperatorRegistry()
        
        # Load extensional subtheory
        result = registry.load_subtheory('extensional')
        
        assert result is not None
        assert 'extensional' in registry.loaded_subtheories
        
        # Check operators were loaded
        operators = registry.get_operators()
        op_dict = dict(operators.items())
        assert len(op_dict) > 0
        assert "\\neg" in op_dict
        assert "\\wedge" in op_dict
        
    def test_load_multiple_subtheories(self):
        """Test loading multiple subtheories."""
        registry = LogosOperatorRegistry()
        
        # Load multiple subtheories
        registry.load_subtheories(['extensional', 'modal'])
        
        assert 'extensional' in registry.loaded_subtheories
        assert 'modal' in registry.loaded_subtheories
        
        # Check operators from both were loaded
        operators = registry.get_operators()
        op_dict = dict(operators.items())
        assert "\\neg" in op_dict  # from extensional
        assert "\\Box" in op_dict  # from modal
        
    def test_incremental_loading(self):
        """Test loading subtheories incrementally."""
        registry = LogosOperatorRegistry()
        
        # Load first subtheory
        registry.load_subtheory('extensional')
        initial_count = len(dict(registry.get_operators().items()))
        
        # Load another subtheory
        registry.load_subtheory('modal')
        final_count = len(dict(registry.get_operators().items()))
        
        assert final_count > initial_count
        assert 'extensional' in registry.loaded_subtheories
        assert 'modal' in registry.loaded_subtheories


class TestDependencyResolution:
    """Test dependency resolution functionality."""
    
    def test_automatic_dependency_resolution(self):
        """Test dependencies are automatically resolved."""
        registry = LogosOperatorRegistry()
        
        # Load modal, which depends on extensional
        registry.load_subtheory('modal')
        
        # Both should be loaded
        assert 'modal' in registry.loaded_subtheories
        assert 'extensional' in registry.loaded_subtheories
        
        # Extensional operators should be available
        operators = registry.get_operators()
        op_dict = dict(operators.items())
        assert "\\neg" in op_dict  # from extensional dependency
        
    def test_dependency_chain_resolution(self):
        """Test complex dependency chains are resolved."""
        registry = LogosOperatorRegistry()
        
        # Load relevance, which depends on constitutive
        registry.load_subtheory('relevance')
        
        # Both should be loaded
        assert 'relevance' in registry.loaded_subtheories
        assert 'constitutive' in registry.loaded_subtheories


class TestOperatorAccess:
    """Test operator access functionality."""
    
    def test_operator_retrieval(self):
        """Test accessing loaded operators."""
        registry = LogosOperatorRegistry()
        registry.load_subtheory('extensional')
        
        operators = registry.get_operators()
        
        assert operators is not None
        assert isinstance(operators, OperatorCollection)
        op_dict = dict(operators.items())
        assert len(op_dict) > 0
        
    def test_operator_collection_structure(self):
        """Test operator collection has expected structure."""
        registry = LogosOperatorRegistry()
        registry.load_subtheory('extensional')
        
        operators = registry.get_operators()
        op_dict = dict(operators.items())
        
        # Check specific operators
        assert "\\neg" in op_dict
        assert "\\wedge" in op_dict
        assert "\\vee" in op_dict
        
        # Check that values are operator classes
        from model_checker.syntactic import Operator
        for op_name, op_class in operators.items():
            assert issubclass(op_class, Operator), f"{op_name} is not an Operator subclass"


class TestErrorHandling:
    """Test registry error handling."""
    
    def test_invalid_subtheory_handling(self):
        """Test graceful handling of invalid subtheory names."""
        registry = LogosOperatorRegistry()
        
        with pytest.raises((ImportError, ModuleNotFoundError, ValueError)):
            registry.load_subtheory('nonexistent_subtheory')
            
    def test_empty_subtheory_list(self):
        """Test handling of empty subtheory lists."""
        registry = LogosOperatorRegistry()
        
        # Loading empty list should work without error
        result = registry.load_subtheories([])
        
        # Registry should remain empty
        assert len(registry.loaded_subtheories) == 0
        assert len(dict(registry.get_operators().items())) == 0