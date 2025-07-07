"""
Debug the actual implementation to see why NEG_TO_SENT has no countermodel.
"""

import sys
from pathlib import Path

# Add paths
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))
sys.path.insert(0, str(Path(__file__).parent.parent))

# Import the example directly
from examples import (
    NEG_TO_SENT_example,
    exclusion_theory,
    general_settings
)

# Import model checker components
from model_checker.builder import BuildExample

def debug_implementation():
    """Debug why the implementation doesn't find a countermodel."""
    
    print("=== DEBUGGING NEG_TO_SENT IMPLEMENTATION ===")
    
    # Extract example components
    premises, conclusions, settings = NEG_TO_SENT_example
    
    print(f"Premises: {premises}")
    print(f"Conclusions: {conclusions}")
    print(f"Settings: {settings}")
    print()
    
    # Create a BuildExample instance with verbose settings
    debug_settings = settings.copy()
    debug_settings.update({
        'print_constraints': True,  # Show Z3 constraints
        'print_z3': True,          # Show Z3 model details
    })
    
    # Merge with general settings
    debug_settings.update(general_settings)
    
    print("Creating BuildExample instance...")
    example = BuildExample(
        premises,
        conclusions,
        debug_settings,
        exclusion_theory
    )
    
    print("\nRunning model check...")
    example.run()
    
    print("\n=== ANALYSIS ===")
    
    # Check if we got a model
    if hasattr(example, 'model') and example.model:
        model = example.model
        
        print(f"Model found: {model.z3_model_status}")
        print(f"Timeout: {model.z3_model_timeout}")
        
        if model.z3_model is not None:
            print("\nZ3 Model details:")
            print(model.z3_model)
        else:
            print("No Z3 model available")
            
        # Check the constraint generation
        if hasattr(model, 'incremental_solver'):
            print("\nIncremental solver assertions:")
            assertions = model.incremental_solver.solver.assertions()
            print(f"Total assertions: {len(assertions)}")
            
            # Look for exclusion-related constraints
            print("\nSearching for exclusion constraints...")
            for i, assertion in enumerate(assertions[:10]):  # First 10
                print(f"\nAssertion {i}: {assertion}")
    else:
        print("No model was created!")

if __name__ == "__main__":
    debug_implementation()