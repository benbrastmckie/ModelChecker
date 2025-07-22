"""Edge case tests for model iteration."""

import pytest
import z3
from unittest.mock import Mock, patch
from model_checker import get_theory


class TestIteratorEdgeCases:
    """Test edge cases and error conditions for iterators."""
    
    def test_zero_iterations_requested(self):
        """Test behavior when 0 iterations are requested."""
        theory = get_theory('logos')
        module = create_test_module()
        module.semantic_theories = {'logos': {}}
        module.example_range = {'test': object()}
        
        build_module = Mock()
        build_module.module = module
        build_module.name = 'test_module'
        
        example = BuildExample(build_module, 'logos', 'test')
        example.check_formula("A", settings={'iterate': 0})
        
        # Should have no iterator created
        assert not hasattr(example, '_iterator')
    
    def test_negative_iterations_rejected(self):
        """Test that negative iteration counts are rejected."""
        theory = get_theory('logos')
        module = create_test_module()
        module.semantic_theories = {'logos': {}}
        module.example_range = {'test': object()}
        
        build_module = Mock()
        build_module.module = module
        build_module.name = 'test_module'
        
        example = BuildExample(build_module, 'logos', 'test')
        with pytest.raises(ValueError):
            example.check_formula("A", settings={'iterate': -1})
    
    def test_very_large_iteration_count(self):
        """Test behavior with unreasonably large iteration request."""
        theory = get_theory('logos')
        module = create_test_module()
        module.semantic_theories = {'logos': {}}
        module.example_range = {'test': object()}
        
        build_module = Mock()
        build_module.module = module
        build_module.name = 'test_module'
        
        example = BuildExample(build_module, 'logos', 'test')
        # Should handle gracefully even if requested iterations are huge
        example.check_formula("A \\func_fusion B", settings={'N': 2, 'iterate': 1000000})
        
        # Iterator should exist but find limited models
        assert hasattr(example, '_iterator')
        # Should find fewer models than requested
        assert len(example._iterator.model_structures) < 1000000
    
    def test_empty_formula_iteration(self):
        """Test iteration with empty formula."""
        theory = get_theory('logos')
        module = create_test_module()
        module.semantic_theories = {'logos': {}}
        module.example_range = {'test': object()}
        
        build_module = Mock()
        build_module.module = module
        build_module.name = 'test_module'
        
        example = BuildExample(build_module, 'logos', 'test')
        example.check_formula("", settings={'iterate': 2})
        
        # Should handle empty formula gracefully
        assert hasattr(example, '_iterator')
    
    def test_iteration_with_unsatisfiable_formula(self):
        """Test iteration with contradiction."""
        theory = get_theory('logos')
        module = create_test_module()
        module.semantic_theories = {'logos': {}}
        module.example_range = {'test': object()}
        
        build_module = Mock()
        build_module.module = module
        build_module.name = 'test_module'
        
        example = BuildExample(build_module, 'logos', 'test')
        example.check_formula("A \\func_intersection \\neg A", settings={'iterate': 5})
        
        # Should find only 1 model or none
        assert hasattr(example, '_iterator')
        assert len(example._iterator.model_structures) <= 1
    
    def test_iteration_with_missing_settings(self):
        """Test iteration when some settings are missing."""
        theory = get_theory('logos')
        module = create_test_module()
        module.semantic_theories = {'logos': {}}
        module.example_range = {'test': object()}
        
        build_module = Mock()
        build_module.module = module
        build_module.name = 'test_module'
        
        example = BuildExample(build_module, 'logos', 'test')
        # Missing 'N' setting
        example.check_formula("A", settings={'iterate': 2})
        
        # Should use defaults and work
        assert hasattr(example, '_iterator')
    
    def test_concurrent_iteration_safety(self):
        """Test that multiple iterators don't interfere."""
        theory = get_theory('logos')
        
        # Create two examples
        examples = []
        for i in range(2):
            module = create_test_module()
            module.semantic_theories = {'logos': {}}
            module.example_range = {'test': object()}
            
            build_module = Mock()
            build_module.module = module
            build_module.name = f'test_module_{i}'
            
            example = BuildExample(build_module, 'logos', 'test')
            examples.append(example)
        
        # Run iterations on both
        examples[0].check_formula("A", settings={'iterate': 2})
        examples[1].check_formula("B", settings={'iterate': 3})
        
        # Each should have independent results
        assert len(examples[0]._iterator.model_structures) <= 2
        assert len(examples[1]._iterator.model_structures) <= 3


def create_test_module():
    """Create a mock module for testing."""
    from types import ModuleType
    module = ModuleType('test_module')
    return module