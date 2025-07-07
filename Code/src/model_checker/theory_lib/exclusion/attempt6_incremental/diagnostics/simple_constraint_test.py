"""
Simple test to identify the problematic constraint.
"""

import z3
import sys
from pathlib import Path

# Add paths
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))
sys.path.insert(0, str(Path(__file__).parent.parent))

from semantic import ExclusionSemantics

def simple_test():
    """Simplified test of frame constraints."""
    
    print("=== Simple Frame Constraint Test ===")
    
    # Minimal settings
    settings = {'N': 2}  # Use N=2 for simplicity
    
    sem = ExclusionSemantics(settings)
    
    # Get frame constraints
    constraints = sem._get_frame_constraints()
    
    print(f"\nNumber of frame constraints: {len(constraints)}")
    
    # Test each constraint individually
    for i, constraint in enumerate(constraints):
        solver = z3.Solver()
        solver.add(constraint)
        result = solver.check()
        
        print(f"\nConstraint {i}: {result}")
        
        if result == z3.unsat:
            print("This constraint is individually UNSAT!")
            
            # Try to understand it better
            print("\nConstraint details:")
            # Get string representation
            constraint_str = str(constraint)
            if len(constraint_str) > 500:
                print(f"Very long constraint ({len(constraint_str)} chars)")
                print("First 200 chars:", constraint_str[:200])
                print("...")
                print("Last 200 chars:", constraint_str[-200:])
            else:
                print(constraint_str)
    
    # Test all together
    print("\n\nTesting all constraints together:")
    solver_all = z3.Solver()
    for constraint in constraints:
        solver_all.add(constraint)
    
    result_all = solver_all.check()
    print(f"All constraints together: {result_all}")
    
    if result_all == z3.sat:
        model = solver_all.model()
        print("\nModel found!")
        # Print main_world value
        for decl in model.decls():
            if 'main_world' in decl.name():
                print(f"{decl.name()} = {model[decl]}")

if __name__ == "__main__":
    simple_test()