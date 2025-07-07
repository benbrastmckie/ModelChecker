"""
Extract and analyze the exact constraints that exist before the premise constraint is added.
"""

import z3
import sys
from pathlib import Path

# Add paths
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))
sys.path.insert(0, str(Path(__file__).parent.parent))

from semantic import ExclusionSemantics
from model_checker import syntactic

def extract_constraints():
    """Build up constraints exactly as the incremental solver does."""
    
    print("=== Extracting Constraints Before Premise ===")
    
    # Settings from NEG_TO_SENT
    settings = {
        'N': 3,
        'possible': False,
        'contingent': True,
        'non_empty': True,
        'non_null': True,
        'disjoint': False,
        'fusion_closure': False,
    }
    
    # Create semantics
    sem = ExclusionSemantics(settings)
    
    # Create solver
    solver = z3.Solver()
    
    print("\n1. FRAME CONSTRAINTS")
    print("-" * 50)
    
    # Get frame constraints
    frame_constraints = sem._get_frame_constraints()
    
    print(f"Number of frame constraints: {len(frame_constraints)}")
    
    # Add frame constraints
    for i, constraint in enumerate(frame_constraints):
        solver.add(constraint)
        print(f"  Added frame_{i}")
    
    # Check after frame constraints
    result = solver.check()
    print(f"\nSAT after frame constraints? {result}")
    
    if result == z3.sat:
        model = solver.model()
        # Get main_world value
        main_world = sem.main_world
        main_world_val = model.eval(main_world).as_long()
        print(f"main_world = {bin(main_world_val)}")
    
    print("\n2. ATOMIC CONSTRAINTS FOR A")
    print("-" * 50)
    
    # Create atomic proposition A
    letter_A = syntactic.AtomVal(0)
    
    # Get atomic constraints
    atom_constraints = sem.atom_constraints(letter_A, [letter_A], settings)
    
    print(f"Number of atomic constraints: {len(atom_constraints)}")
    
    # Add atomic constraints
    for label, constraint in atom_constraints:
        solver.add(constraint)
        print(f"  Added: {label}")
    
    # Check after atomic constraints
    result = solver.check()
    print(f"\nSAT after atomic constraints? {result}")
    
    if result == z3.sat:
        model = solver.model()
        main_world_val = model.eval(main_world).as_long()
        print(f"main_world = {bin(main_world_val)}")
        
        # Check which states verify A
        print("\nStates that verify A:")
        verify = sem.verify
        for i in range(2**settings['N']):
            try:
                verifies = model.eval(verify(i, letter_A))
                if z3.is_true(verifies):
                    print(f"  {bin(i)} verifies A")
            except:
                pass
    
    print("\n3. ANALYZING PREMISE CONSTRAINT")
    print("-" * 50)
    
    # Now we'll manually build the three-condition constraint for \exclude A
    # This is what gets added as premise_0
    
    # Create eval_point
    eval_point = {'world': main_world}
    
    # Skolem functions
    h_sk = z3.Function('h_sk', z3.BitVecSort(settings['N']), z3.BitVecSort(settings['N']))
    y_sk = z3.Function('y_sk', z3.BitVecSort(settings['N']), z3.BitVecSort(settings['N']))
    
    print("\nBuilding three-condition constraint for \\exclude A...")
    
    # We need to understand what the constraint looks like
    # Let's check if we can add a simple version first
    
    solver2 = solver.translate(z3.Context())  # Copy solver state
    
    # Try adding a simplified constraint
    print("\nTest 1: Can we require main_world to have no 'a' bit?")
    solver2.push()
    solver2.add((main_world & 0b001) == 0)
    result = solver2.check()
    print(f"Result: {result}")
    
    if result == z3.sat:
        model2 = solver2.model()
        world_val = model2.eval(main_world).as_long()
        print(f"Possible main_world without 'a' bit: {bin(world_val)}")
    solver2.pop()
    
    print("\nTest 2: What if we require specific verifier patterns?")
    
    # Let's see what constraints are preventing the three-condition from working
    print("\nExtracting key information from current model:")
    
    if solver.check() == z3.sat:
        model = solver.model()
        
        # What are the current constraints on exclusion relation?
        print("\nChecking exclusion relation constraints...")
        excludes = sem.excludes
        
        # Check if anything excludes itself
        for i in range(1, 2**settings['N']):  # Skip 0
            try:
                self_excludes = model.eval(excludes(i, i))
                if z3.is_true(self_excludes):
                    print(f"  {bin(i)} excludes itself!")
            except:
                pass
        
        # Check coherence
        print("\nChecking which states are possible (cohere with themselves):")
        for i in range(2**settings['N']):
            try:
                is_possible = model.eval(sem.possible(i))
                if z3.is_true(is_possible):
                    print(f"  {bin(i)} is possible")
            except:
                pass

if __name__ == "__main__":
    extract_constraints()