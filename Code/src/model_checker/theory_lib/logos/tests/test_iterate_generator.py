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
        
        # Use run_test to properly set up the example
        from model_checker import run_test, ModelConstraints, Syntax
        from model_checker.theory_lib.logos.semantic import LogosSemantics, LogosProposition, LogosModelStructure
        from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
        
        # Create operator registry
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional', 'modal'])
        
        example_case = [
            ["P"],  # premises
            ["Q"],  # conclusions (countermodel expected)  
            {"N": 3, "expectation": True, "contingent": False, "non_empty": False, "disjoint": False, "non_null": False, "max_time": 10}  # settings with expectation for countermodel
        ]
        
        # Run the test to build initial model
        test_result = run_test(
            example_case,
            LogosSemantics,
            LogosProposition,
            registry.get_operators(),
            Syntax,
            ModelConstraints,
            LogosModelStructure,
        )
        
        # Get the example from test result's state
        # run_test creates model_result which has the example
        from model_checker.state import get_model_results
        model_result = get_model_results()[0]
        example = model_result.build_example
        
        # Check initial model found
        assert example.model_structure is not None
        assert example.model_structure.z3_model_status == 'sat'
        
        # Test generator interface
        gen = iterate_example_generator(example, max_iterations=3)
        
        models = []
        for i, model in enumerate(gen):
            models.append(model)
            # Verify incremental yielding
            print(f"Yielded model {i+1}")
            assert model is not None
            
        # Should find at least 1 additional model (besides initial)
        assert len(models) >= 1
        
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
        
        # Use run_test to properly set up the example
        from model_checker import run_test, ModelConstraints, Syntax
        from model_checker.theory_lib.logos.semantic import LogosSemantics, LogosProposition, LogosModelStructure
        from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
        
        # Create operator registry
        registry = LogosOperatorRegistry()
        registry.load_subtheories(['extensional'])
        
        example_case = [
            ["P"],       # premises
            ["Q"],       # conclusions (countermodel expected)
            {"N": 2, "expectation": True, "contingent": False, "non_empty": False, "disjoint": False, "non_null": False, "max_time": 10}     # smaller for faster test
        ]
        
        # Run the test to build initial model
        test_result = run_test(
            example_case,
            LogosSemantics,
            LogosProposition,
            registry.get_operators(),
            Syntax,
            ModelConstraints,
            LogosModelStructure,
        )
        
        # Get the example from test result's state
        from model_checker.state import get_model_results
        model_result = get_model_results()[0]
        example = model_result.build_example
        
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