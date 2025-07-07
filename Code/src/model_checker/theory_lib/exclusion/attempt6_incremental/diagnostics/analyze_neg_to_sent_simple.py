"""
Simple diagnostic to understand why NEG_TO_SENT has no countermodel.

We'll manually build the constraints and check what's happening.
"""

import z3
import sys
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))

def analyze_constraints():
    """Manually analyze the three-condition exclusion semantics."""
    
    print("=== MANUAL ANALYSIS OF NEG_TO_SENT ===")
    print("Looking for a model where:")
    print("  - \\exclude A is true")
    print("  - A is false")
    print()
    
    # Create solver
    solver = z3.Solver()
    
    # Variables
    N = 3  # Number of atoms
    world = z3.BitVec('world', N)
    
    # Define verifiers of A: states with 'a' bit (bit 0)
    print("Step 1: Verifiers of A are states with bit 0 set:")
    a_verifiers = []
    for i in range(2**N):
        if i & 0b001:
            a_verifiers.append(i)
            print(f"  {bin(i)} = {i}")
    print()
    
    # Create Skolem functions
    h_sk = z3.Function('h_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    y_sk = z3.Function('y_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    
    print("Step 2: Adding three-condition constraints for \\exclude A")
    
    # Helper functions
    def is_part_of(x, y):
        return (x | y) == y
    
    def excludes(x, y):
        return (x & y) == 0
    
    # Condition 1: For all x in Ver(A), y_sk(x) ⊑ x and h_sk(x) excludes y_sk(x)
    print("\nCondition 1: For each verifier x of A:")
    print("  - y_sk(x) must be part of x")
    print("  - h_sk(x) must exclude y_sk(x)")
    
    for v in a_verifiers:
        v_bv = z3.BitVecVal(v, N)
        # y_sk(v) is part of v
        solver.add(is_part_of(y_sk(v_bv), v_bv))
        # h_sk(v) excludes y_sk(v)
        solver.add(excludes(h_sk(v_bv), y_sk(v_bv)))
    
    # Condition 2: For all x in Ver(A), h_sk(x) is part of world
    print("\nCondition 2: For each verifier x of A:")
    print("  - h_sk(x) must be part of the evaluation world")
    
    for v in a_verifiers:
        v_bv = z3.BitVecVal(v, N)
        solver.add(is_part_of(h_sk(v_bv), world))
    
    # Condition 3: world is minimal (exactly the fusion of h_sk values)
    print("\nCondition 3: The evaluation world must be minimal")
    print("  - world = fusion of all h_sk(x) for x in Ver(A)")
    
    # The world must be exactly the fusion (bitwise OR) of all h_sk values
    fusion = z3.BitVecVal(0, N)
    for v in a_verifiers:
        v_bv = z3.BitVecVal(v, N)
        fusion = fusion | h_sk(v_bv)
    
    solver.add(world == fusion)
    
    # Add constraint that A is false at world
    print("\nAdding constraint: A is false at world")
    print("  - world & 0b001 == 0")
    solver.add((world & 0b001) == 0)
    
    print("\n=== CHECKING SATISFIABILITY ===")
    result = solver.check()
    print(f"Result: {result}")
    
    if result == z3.sat:
        model = solver.model()
        world_val = model.eval(world).as_long()
        print(f"\nFound model with world = {bin(world_val)}")
        
        print("\nSkolem function values:")
        for v in a_verifiers:
            v_bv = z3.BitVecVal(v, N)
            h_val = model.eval(h_sk(v_bv)).as_long()
            y_val = model.eval(y_sk(v_bv)).as_long()
            print(f"  h_sk({bin(v)}) = {bin(h_val)}")
            print(f"  y_sk({bin(v)}) = {bin(y_val)}")
    else:
        print("\nNo model found!")
        print("\nLet's check why...")
        
        # Check if the issue is with condition 3
        print("\nTesting without the A-false constraint:")
        solver2 = z3.Solver()
        
        # Add conditions 1 and 2
        for v in a_verifiers:
            v_bv = z3.BitVecVal(v, N)
            solver2.add(is_part_of(y_sk(v_bv), v_bv))
            solver2.add(excludes(h_sk(v_bv), y_sk(v_bv)))
            solver2.add(is_part_of(h_sk(v_bv), world))
        
        # Add condition 3
        fusion = z3.BitVecVal(0, N)
        for v in a_verifiers:
            v_bv = z3.BitVecVal(v, N)
            fusion = fusion | h_sk(v_bv)
        solver2.add(world == fusion)
        
        result2 = solver2.check()
        print(f"Can \\exclude A be true at any world? {result2}")
        
        if result2 == z3.sat:
            model2 = solver2.model()
            world_val2 = model2.eval(world).as_long()
            print(f"Yes, at world = {bin(world_val2)}")
            print(f"Does this world have the 'a' bit? {bool(world_val2 & 0b001)}")
            
            print("\nThe problem is that condition 3 (minimality) forces")
            print("the world to be the fusion of h_sk values.")
            print("If any h_sk(x) has the 'a' bit, then the world must too!")
            
            print("\nLet's check the h_sk values:")
            for v in a_verifiers:
                v_bv = z3.BitVecVal(v, N)
                h_val = model2.eval(h_sk(v_bv)).as_long()
                print(f"  h_sk({bin(v)}) = {bin(h_val)} - has 'a' bit: {bool(h_val & 0b001)}")

if __name__ == "__main__":
    analyze_constraints()