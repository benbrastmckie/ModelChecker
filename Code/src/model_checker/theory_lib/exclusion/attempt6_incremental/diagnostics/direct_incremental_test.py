"""
Direct test using the actual IncrementalModelStructure.
"""

import sys
from pathlib import Path

# Add paths
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))
sys.path.insert(0, str(Path(__file__).parent.parent))

# Import model checker components
from model_checker import syntactic
from model_checker.model import ModelConstraints
from semantic import ExclusionSemantics, UnilateralProposition
from operators import exclusion_operators
from incremental_model import IncrementalModelStructure

def direct_test():
    """Test NEG_TO_SENT directly with IncrementalModelStructure."""
    
    print("=== Direct Test of NEG_TO_SENT ===")
    
    # Create syntax
    syntax = syntactic.Syntax(
        ["\\exclude A"],  # premises
        ["A"],           # conclusions
        exclusion_operators
    )
    
    # Settings
    settings = {
        'N': 3,
        'possible': False,
        'contingent': True,
        'non_empty': True,
        'non_null': True,
        'disjoint': False,
        'fusion_closure': False,
        'max_time': 5,
        'expectation': False,
    }
    
    # Create semantics
    semantics = ExclusionSemantics(settings)
    
    # Create model constraints
    model_constraints = ModelConstraints(
        syntax,
        settings,
        semantics,
        UnilateralProposition
    )
    
    print("\nCreating IncrementalModelStructure...")
    
    try:
        # This is where the solving happens
        model = IncrementalModelStructure(model_constraints, settings)
        
        print(f"\nModel status: {model.z3_model_status}")
        print(f"Timeout: {model.z3_model_timeout}")
        
        if model.z3_model is not None:
            print("Model found!")
            main_world = model.z3_model.eval(model.main_world).as_long()
            print(f"main_world = {bin(main_world)}")
        else:
            print("No model found!")
            
            # Check solver assertions
            if hasattr(model, 'incremental_solver'):
                print(f"\nNumber of constraints: {len(model.incremental_solver.constraint_stack)}")
                
                # Show last few constraints
                print("\nLast few constraints added:")
                for constraint, label in model.incremental_solver.constraint_stack[-5:]:
                    print(f"  {label}")
                    
    except Exception as e:
        print(f"\nError during model creation: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    direct_test()