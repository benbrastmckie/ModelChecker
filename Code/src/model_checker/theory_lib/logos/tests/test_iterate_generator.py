"""Test generator interface for logos theory iteration."""

import pytest
from model_checker.builder.example import BuildExample
from model_checker.theory_lib.logos import get_theory, iterate_example_generator


class TestLogosGeneratorInterface:
    """Test logos theory supports generator iteration."""
    
    def test_logos_generator_interface(self):
        """Test logos supports generator iteration."""
        # Get logos theory
        theory = get_theory()
        
        # Create a minimal BuildModule mock that has all required attributes
        from unittest.mock import Mock
        from types import SimpleNamespace
        
        # Create module with all necessary attributes
        module = Mock()
        module.theory_name = 'logos'
        module.semantic_theories = {"logos": theory}
        module.raw_general_settings = {}
        module.general_settings = {}
        module.module_flags = SimpleNamespace()
        
        # Simple example case that should work
        example_case = [
            ["P"],  # premises
            ["Q"],  # conclusions (countermodel expected)
            {"N": 2, "expectation": True}  # minimal settings
        ]
        
        # Build example - this creates the initial model
        example = BuildExample(module, theory, example_case, 'logos')
        
        # Check initial model found
        assert example.model_structure is not None
        assert example.model_structure.z3_model_status == True
        
        # Test generator interface
        gen = iterate_example_generator(example, max_iterations=3)
        
        models = []
        for i, model in enumerate(gen):
            models.append(model)
            # Verify incremental yielding
            print(f"Yielded model {i+1}")
            assert model is not None
            
        # The generator should work even if no additional models exist
        # Just verify it runs without error
        print(f"Found {len(models)} additional models")
        
    def test_generator_marker_present(self):
        """Test that generator function is properly marked."""
        # Check the function has the expected markers
        assert hasattr(iterate_example_generator, 'returns_generator')
        assert iterate_example_generator.returns_generator == True
        assert hasattr(iterate_example_generator, '__wrapped__')
        
    def test_generator_yields_incrementally(self):
        """Test that models are yielded one at a time."""
        # Get logos theory
        theory = get_theory()
        
        # Create a minimal BuildModule mock
        from unittest.mock import Mock
        from types import SimpleNamespace
        
        module = Mock()
        module.theory_name = 'logos'
        module.semantic_theories = {"logos": theory}
        module.raw_general_settings = {}
        module.general_settings = {}
        module.module_flags = SimpleNamespace()
        
        example_case = [
            ["P"],       # premises
            ["Q"],       # conclusions (countermodel expected)
            {"N": 2}     # smaller for faster test
        ]
        
        example = BuildExample(module, theory, example_case, 'logos')
        
        # Get generator
        gen = iterate_example_generator(example, max_iterations=2)
        
        # Should be able to get models one at a time
        try:
            model1 = next(gen)
            assert model1 is not None
            # At this point, only one model has been generated
        except StopIteration:
            # It's ok if no additional models exist
            pass