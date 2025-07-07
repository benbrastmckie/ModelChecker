"""
Trace the exact constraint that makes the system UNSAT.
"""

import z3
import sys
from pathlib import Path

# Add paths
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))
sys.path.insert(0, str(Path(__file__).parent.parent))

# Import the actual semantic class
from semantic import ExclusionSemantics

def trace_constraints():
    """Add constraints one by one to find which makes it UNSAT."""
    
    print("=== Tracing Constraint Addition ===")
    
    # Create semantics instance
    settings = {
        'N': 3,
        'contingent': True,
        'non_empty': True,
        'non_null': True,
        'possible': False,
        'disjoint': False,
        'fusion_closure': False,
    }
    
    sem = ExclusionSemantics(settings)
    
    # Get frame constraints
    frame_constraints = sem._get_frame_constraints()
    
    print(f"\nTotal frame constraints: {len(frame_constraints)}")
    
    # Create solver
    solver = z3.Solver()
    
    # Add constraints one by one
    for i, constraint in enumerate(frame_constraints):
        print(f"\n--- Adding constraint {i} ---")
        
        # Show constraint info
        print(f"Constraint: {constraint}")
        
        # Create checkpoint
        solver.push()
        
        # Add constraint
        solver.add(constraint)
        
        # Check satisfiability
        result = solver.check()
        print(f"Satisfiable after constraint {i}? {result}")
        
        if result == z3.unsat:
            print(f"\nConstraint {i} makes the system UNSAT!")
            print("This is the problematic constraint.")
            
            # Try to understand why
            solver.pop()  # Remove the problematic constraint
            
            # Check what we had before
            if solver.check() == z3.sat:
                print("\nThe system was SAT before this constraint.")
                model = solver.model()
                
                # Try to understand the constraint better
                print(f"\nProblematic constraint details:")
                print(f"Type: {type(constraint)}")
                print(f"String representation: {str(constraint)[:200]}...")
            break
    
    if result == z3.sat:
        print("\nAll frame constraints are satisfiable together!")
        
        # Now add atomic constraints
        print("\n\n=== Adding Atomic Constraints ===")
        
        # Get atomic constraints for A
        from model_checker import syntactic
        letter_A = syntactic.AtomVal(0)
        
        atom_constraints = sem.atom_constraints(letter_A, [letter_A], settings)
        
        for label, constraint in atom_constraints:
            print(f"\nAdding atomic constraint: {label}")
            solver.add(constraint)
            result = solver.check()
            print(f"Satisfiable? {result}")
            
            if result == z3.unsat:
                print(f"\nAtomic constraint '{label}' makes it UNSAT!")
                break

if __name__ == "__main__":
    trace_constraints()