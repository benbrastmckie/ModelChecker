"""Tests that define the ideal architecture for ModelChecker.

These tests define how we want the system to work after refactoring.
They serve as the specification for the clean architecture.
"""

import ast
import os
import pytest
from pathlib import Path


class TestArchitecturalConstraints:
    """Tests that verify architectural constraints are maintained."""
    
    def test_builder_has_no_theory_imports(self):
        """Builder module should not import any theories."""
        builder_path = Path(__file__).parent.parent / 'src' / 'model_checker' / 'builder'
        
        for filepath in builder_path.rglob('*.py'):
            # Skip test files
            if 'test' in filepath.name:
                continue
                
            with open(filepath) as f:
                content = f.read()
                tree = ast.parse(content)
            
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    for alias in node.names:
                        assert 'theory_lib' not in alias.name, \
                            f"{filepath.name} imports from theory_lib: {alias.name}"
                elif isinstance(node, ast.ImportFrom):
                    if node.module:
                        assert 'theory_lib' not in node.module, \
                            f"{filepath.name} imports from theory_lib: {node.module}"
    
    def test_no_circular_imports(self):
        """Verify no circular import between builder and iterate."""
        # Check that iterate doesn't import from builder.example
        iterate_path = Path(__file__).parent.parent / 'src' / 'model_checker' / 'iterate' / 'core.py'
        
        with open(iterate_path) as f:
            content = f.read()
            tree = ast.parse(content)
            
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom):
                if node.module and 'builder.example' in node.module:
                    # Should be commented out or removed
                    assert False, "iterate/core.py should not import from builder.example"


class TestCoreInterfaces:
    """Tests for the core interface definitions."""
    
    def test_theory_interface_exists(self):
        """Core theory interface should exist."""
        from model_checker.core.interfaces import TheoryInterface
        
        # Check required methods
        assert hasattr(TheoryInterface, 'get_semantics')
        assert hasattr(TheoryInterface, 'get_proposition_class')
        assert hasattr(TheoryInterface, 'get_model_class')
        assert hasattr(TheoryInterface, 'get_operators')
    
    def test_example_interface_exists(self):
        """Core example interface should exist."""
        from model_checker.core.interfaces import ExampleInterface
        
        # Check required methods
        assert hasattr(ExampleInterface, 'build')


class TestTheoryRegistry:
    """Tests for the theory registration system."""
    
    def test_theory_registry_exists(self):
        """Theory registry should exist and work properly."""
        from model_checker.theory_lib.registry import TheoryRegistry, get_theory
        
        registry = TheoryRegistry()
        
        # Should be able to register theories
        assert hasattr(registry, 'register')
        assert hasattr(registry, 'get')
        assert hasattr(registry, 'list_theories')
    
    def test_all_theories_implement_interface(self):
        """All theories must implement the core interface."""
        from model_checker.core.interfaces import TheoryInterface
        from model_checker.theory_lib import get_all_theories
        
        for theory_name, theory_class in get_all_theories().items():
            # Create instance
            theory = theory_class()
            
            # Check it has all required methods
            assert hasattr(theory, 'get_semantics')
            assert hasattr(theory, 'get_proposition_class')
            assert hasattr(theory, 'get_model_class')
            assert hasattr(theory, 'get_operators')
            
            # Check methods are callable
            assert callable(theory.get_semantics)
            assert callable(theory.get_proposition_class)
            assert callable(theory.get_model_class)
            assert callable(theory.get_operators)


class TestExampleBuilder:
    """Tests for the refactored example builder."""
    
    def test_example_builder_with_any_theory(self):
        """Example builder should work with any theory via interface."""
        from model_checker.builder import Example
        from model_checker.theory_lib import get_theory
        
        # Test with different theories
        for theory_name in ['logos', 'bimodal', 'exclusion', 'imposition']:
            theory = get_theory(theory_name)
            example = Example(theory=theory)
            
            # Should be able to build with any valid theory
            result = example.build(
                premises=['A'],
                conclusions=['B'],
                settings={'N': 3}
            )
            assert result is not None
    
    def test_example_accepts_theory_interface(self):
        """Example should accept any object implementing TheoryInterface."""
        from model_checker.builder import Example
        from model_checker.core.interfaces import TheoryInterface
        
        # Create a mock theory that implements the interface
        class MockTheory(TheoryInterface):
            def get_semantics(self):
                from model_checker.theory_lib.logos import LogosSemantics
                return LogosSemantics
            
            def get_proposition_class(self):
                from model_checker.theory_lib.logos import LogosProposition
                return LogosProposition
            
            def get_model_class(self):
                from model_checker.theory_lib.logos import LogosModelStructure
                return LogosModelStructure
            
            def get_operators(self):
                from model_checker.theory_lib.logos import get_theory
                return get_theory()['operators']
        
        # Should work with mock theory
        mock_theory = MockTheory()
        example = Example(theory=mock_theory)
        assert example is not None


class TestPublicAPI:
    """Tests for the clean public API."""
    
    def test_simple_api_works(self):
        """The simplified API should work as expected."""
        from model_checker import check_example
        
        result = check_example(
            theory_name='logos',
            premises=['A'],
            conclusions=['B'],
            settings={'N': 3}
        )
        
        assert result is not None
    
    def test_public_api_exports(self):
        """Public API should export the right components."""
        import model_checker
        
        # Core interfaces
        assert hasattr(model_checker, 'TheoryInterface')
        assert hasattr(model_checker, 'ExampleInterface')
        
        # Builders
        assert hasattr(model_checker, 'Example')
        assert hasattr(model_checker, 'Module')
        
        # Theory management
        assert hasattr(model_checker, 'get_theory')
        assert hasattr(model_checker, 'list_theories')
        
        # Convenience
        assert hasattr(model_checker, 'check_example')


class TestIteratorIntegration:
    """Tests for iterator working with new architecture."""
    
    def test_iterator_uses_interface(self):
        """Iterator should work through the interface."""
        from model_checker.builder import Example
        from model_checker.theory_lib import get_theory
        
        # Get theory through interface
        theory = get_theory('logos')
        
        # Build example
        example = Example(theory=theory)
        result = example.build(
            premises=[],
            conclusions=['A'],
            settings={'N': 3, 'iterate': 2}
        )
        
        # Should have found models
        assert hasattr(result, 'models')
        assert len(result.models) <= 2  # At most 2 models as requested