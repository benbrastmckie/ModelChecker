"""
Unit tests for LogosOperatorRegistry functionality.

This test file validates the operator registry system works correctly
for loading and managing operators from different subtheories.
"""

import pytest
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry


class TestLogosOperatorRegistry:
    """Test the LogosOperatorRegistry class."""
    
    def test_registry_creation(self):
        """Test basic registry creation."""
        registry = LogosOperatorRegistry()
        assert registry is not None
        assert hasattr(registry, 'operator_collections')
        assert hasattr(registry, 'loaded_subtheories')
    
    def test_empty_registry(self):
        """Test empty registry state."""
        registry = LogosOperatorRegistry()
        operators = registry.get_operators()
        
        # Should have empty or minimal operator set initially
        assert hasattr(operators, 'operator_dictionary')
    
    def test_load_single_subtheory(self):
        """Test loading a single subtheory."""
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional'])
        
        assert 'extensional' in registry.loaded_subtheories
        operators = registry.get_operators()
        
        # Should have extensional operators
        assert "\\neg" in operators.operator_dictionary
        assert "\\wedge" in operators.operator_dictionary
        assert "\\vee" in operators.operator_dictionary
    
    def test_load_multiple_subtheories(self):
        """Test loading multiple subtheories."""
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional', 'modal'])
        
        assert 'extensional' in registry.loaded_subtheories
        assert 'modal' in registry.loaded_subtheories
        
        operators = registry.get_operators()
        
        # Should have both extensional and modal operators
        assert "\\neg" in operators.operator_dictionary  # extensional
        assert "\\Box" in operators.operator_dictionary  # modal
    
    def test_incremental_loading(self):
        """Test loading subtheories incrementally."""
        registry = LogosOperatorRegistry()
        
        # Load extensional first
        registry.load_subtheories(['extensional'])
        first_count = len(registry.get_operators().operator_dictionary)
        
        # Add modal
        registry.load_subtheories(['extensional', 'modal'])
        second_count = len(registry.get_operators().operator_dictionary)
        
        assert second_count > first_count, "Adding modal should increase operator count"
    
    def test_all_subtheories_loading(self):
        """Test loading all available subtheories."""
        registry = LogosOperatorRegistry()
        all_subtheories = ['extensional', 'modal', 'constitutive', 'counterfactual', 'relevance']
        
        registry.load_subtheories(all_subtheories)
        
        for subtheory in all_subtheories:
            assert subtheory in registry.loaded_subtheories
        
        operators = registry.get_operators()
        
        # Should have substantial number of operators
        assert len(operators.operator_dictionary) >= 15


class TestSubtheoryDependencies:
    """Test subtheory dependency resolution."""
    
    def test_modal_requires_extensional(self):
        """Test that modal subtheory includes extensional operators."""
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional', 'modal'])
        
        operators = registry.get_operators()
        
        # Should have extensional operators (modal depends on them)
        assert "\\neg" in operators.operator_dictionary
        assert "\\wedge" in operators.operator_dictionary
        
        # Should have modal operators
        assert "\\Box" in operators.operator_dictionary
        assert "\\Diamond" in operators.operator_dictionary
    
    def test_constitutive_dependencies(self):
        """Test constitutive subtheory dependencies."""
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional', 'modal', 'constitutive'])
        
        operators = registry.get_operators()
        
        # Should have extensional, modal, and constitutive operators
        assert "\\neg" in operators.operator_dictionary  # extensional
        assert "\\Box" in operators.operator_dictionary  # modal
        assert "\\equiv" in operators.operator_dictionary  # constitutive
    
    def test_counterfactual_dependencies(self):
        """Test counterfactual subtheory dependencies."""
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional', 'modal', 'counterfactual'])
        
        operators = registry.get_operators()
        
        # Should have extensional, modal, and counterfactual operators
        assert "\\neg" in operators.operator_dictionary  # extensional
        assert "\\Box" in operators.operator_dictionary  # modal
        assert "\\boxright" in operators.operator_dictionary  # counterfactual
    
    def test_relevance_dependencies(self):
        """Test relevance subtheory dependencies."""
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional', 'modal', 'constitutive', 'relevance'])
        
        operators = registry.get_operators()
        
        # Should have all dependency operators
        assert "\\neg" in operators.operator_dictionary  # extensional
        assert "\\Box" in operators.operator_dictionary  # modal
        assert "\\equiv" in operators.operator_dictionary  # constitutive


class TestOperatorCounting:
    """Test operator counting and validation."""
    
    def test_extensional_operator_count(self):
        """Test expected number of extensional operators."""
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional'])
        
        operators = registry.get_operators()
        
        # Extensional should have 7 operators
        extensional_ops = ["\\neg", "\\wedge", "\\vee", "\\top", "\\bot", 
                          "\\rightarrow", "\\leftrightarrow"]
        
        for op in extensional_ops:
            assert op in operators.operator_dictionary, f"Missing extensional operator: {op}"
    
    def test_modal_addition_count(self):
        """Test that modal adds expected number of operators."""
        registry = LogosOperatorRegistry()
        
        # Count extensional only
        registry.load_subtheories(['extensional'])
        ext_count = len(registry.get_operators().operator_dictionary)
        
        # Add modal
        registry = LogosOperatorRegistry()  # Fresh registry
        registry.load_subtheories(['extensional', 'modal'])
        modal_count = len(registry.get_operators().operator_dictionary)
        
        # Modal should add at least 4 operators
        assert modal_count >= ext_count + 4, "Modal should add at least 4 operators"
    
    def test_total_operator_bounds(self):
        """Test reasonable bounds on total operator count."""
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional', 'modal', 'constitutive', 'counterfactual', 'relevance'])
        
        operators = registry.get_operators()
        total_count = len(operators.operator_dictionary)
        
        # Should have substantial number but not excessive
        assert total_count >= 15, "Should have at least 15 operators total"
        assert total_count <= 50, "Should not have excessive number of operators"


class TestRegistryErrorHandling:
    """Test registry error handling and edge cases."""
    
    def test_invalid_subtheory(self):
        """Test handling of invalid subtheory names."""
        registry = LogosOperatorRegistry()
        
        # This should either raise an error or silently ignore
        try:
            registry.load_subtheories(['nonexistent_subtheory'])
            # If it doesn't raise an error, make sure it doesn't break the registry
            operators = registry.get_operators()
            assert operators is not None
        except (KeyError, ValueError, ImportError):
            # Expected behavior for invalid subtheory
            pass
    
    def test_empty_subtheory_list(self):
        """Test loading empty subtheory list."""
        registry = LogosOperatorRegistry()
        registry.load_subtheories([])
        
        # Should not crash
        operators = registry.get_operators()
        assert operators is not None
    
    def test_duplicate_loading(self):
        """Test loading the same subtheory multiple times."""
        registry = LogosOperatorRegistry()
        
        # Load extensional twice
        registry.load_subtheories(['extensional'])
        first_count = len(registry.get_operators().operator_dictionary)
        
        registry.load_subtheories(['extensional'])
        second_count = len(registry.get_operators().operator_dictionary)
        
        # Count should be the same (no duplicates)
        assert first_count == second_count


class TestRegistryStateManagement:
    """Test registry state management."""
    
    def test_registry_isolation(self):
        """Test that different registries are isolated."""
        registry1 = LogosOperatorRegistry()
        registry2 = LogosOperatorRegistry()
        
        registry1.load_subtheories(['extensional'])
        registry2.load_subtheories(['extensional', 'modal'])
        
        ops1 = registry1.get_operators()
        ops2 = registry2.get_operators()
        
        # Should have different numbers of operators
        assert len(ops1.operator_dictionary) != len(ops2.operator_dictionary)
    
    def test_registry_reuse(self):
        """Test that registry can be reused with different configurations."""
        registry = LogosOperatorRegistry()
        
        # First configuration
        registry.load_subtheories(['extensional'])
        first_ops = set(registry.get_operators().operator_dictionary.keys())
        
        # Second configuration (should replace first)
        registry.load_subtheories(['extensional', 'modal'])
        second_ops = set(registry.get_operators().operator_dictionary.keys())
        
        # Second should be superset of first
        assert first_ops.issubset(second_ops)
        assert len(second_ops) > len(first_ops)
    
    def test_get_operators_consistency(self):
        """Test that get_operators returns consistent results."""
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional', 'modal'])
        
        ops1 = registry.get_operators()
        ops2 = registry.get_operators()
        
        # Should get same operators
        assert set(ops1.operator_dictionary.keys()) == set(ops2.operator_dictionary.keys())