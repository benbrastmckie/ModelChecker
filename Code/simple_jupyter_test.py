#!/usr/bin/env python3
"""
A minimal script to test the model-checker with a single formula check.
"""

import os
import sys

# Set up paths
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'src'))

try:
    # Import the model-checker
    import model_checker
    print(f"Successfully imported model_checker from {model_checker.__file__}")
    print(f"Version: {model_checker.__version__}")
    
    # Import theory_lib and get the semantic theories
    from model_checker.theory_lib import get_semantic_theories
    
    # Get all available semantic theories for 'default'
    semantic_theories = get_semantic_theories('default')
    
    # Get the default theory
    theory_name = next(iter(semantic_theories.keys()))
    theory = semantic_theories[theory_name]
    print(f"Using theory: {theory_name}")
    
    # Define the basic settings for the model
    example_settings = {
        'N': 3,
        'contingent': False,
        'disjoint': False,
        'non_empty': False,
        'non_null': False,
        'max_time': 5,
        'model': True
    }
    
    general_settings = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "maximize": False,
    }
    
    # Use a simple valid formula with proper syntax
    formula = "(A \\equiv A)"  # Identity operator
    
    # Create a properly structured example
    premises = []
    conclusions = [formula]
    example = [premises, conclusions, example_settings]
    
    # Create a properly structured BuildModule with required attributes
    class ModuleFlags:
        def __init__(self):
            self.file_path = __file__
            
    module_flags = ModuleFlags()
    
    class MockModule:
        def __init__(self):
            self.general_settings = general_settings
            self.semantic_theories = semantic_theories
            self.example_range = {"test_example": example}
    
    build_module = type('BuildModule', (), {
        'module': MockModule(),
        'module_flags': module_flags,
        'general_settings': general_settings
    })
    
    # Build and check the model
    from model_checker import BuildExample
    model = BuildExample(build_module, theory, example)
    
    # Print the result
    print(f"\nFormula: {formula}")
    print(f"Valid: {model.check_result()}")
    
    # Print model details
    print("\nModel details:")
    model.model_structure.print_all(model.example_settings, "formula_check", "default")
    
    print("\nTest completed successfully!")
    
    # Try to import the jupyter module to see if it's available
    print("\nTesting Jupyter integration:")
    try:
        from model_checker.jupyter import check_formula
        print("Successfully imported check_formula from model_checker.jupyter")
    except ImportError as e:
        print(f"Could not import from model_checker.jupyter: {e}")
    
except Exception as e:
    import traceback
    print(f"Error: {e}")
    traceback.print_exc()
    sys.exit(1)