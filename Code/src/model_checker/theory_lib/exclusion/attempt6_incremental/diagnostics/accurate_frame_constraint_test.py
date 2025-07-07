"""
Test the actual frame constraints as implemented.
"""

import z3
import sys
from pathlib import Path

# Add project root
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))

from model_checker.utils import ForAll, Exists

def test_actual_frame_constraints():
    """Test the frame constraints as they're actually implemented."""
    
    print("=== Testing Actual Frame Constraints ===")
    
    N = 3
    solver = z3.Solver()
    
    # Main world
    main_world = z3.BitVec("main_world", N)
    
    # Exclusion relation
    excludes = z3.Function("excludes", z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())
    
    # Helper functions matching semantic.py
    def is_part_of(x, y):
        return (x | y) == y
    
    def is_proper_part_of(x, y):
        return z3.And(is_part_of(x, y), x != y)
    
    def conflicts(bit_e1, bit_e2):
        f1, f2 = z3.BitVecs("f1 f2", N)
        return Exists(
            [f1, f2],
            z3.And(
                is_part_of(f1, bit_e1),
                is_part_of(f2, bit_e2),
                excludes(f1, f2),
            ),
        )
    
    def coheres(bit_e1, bit_e2):
        return z3.Not(conflicts(bit_e1, bit_e2))
    
    def possible(bit_e):
        return coheres(bit_e, bit_e)
    
    def is_world(bit_s):
        m = z3.BitVec("m", N)
        return z3.And(
            possible(bit_s),
            z3.Not(
                Exists(
                    m,
                    z3.And(
                        is_proper_part_of(bit_s, m),
                        possible(m)
                    )
                )
            )
        )
    
    # The actual frame constraints
    x = z3.BitVec("frame_x", N)
    y = z3.BitVec("frame_y", N)
    
    possibility_downward_closure = ForAll(
        [x, y],
        z3.Implies(
            z3.And(is_world(x), is_part_of(y, x)),
            possible(y),
        ),
    )
    
    is_main_world = is_world(main_world)
    
    print("Adding frame constraints:")
    print("1. Possibility downward closure")
    print("2. main_world is a world")
    
    solver.add(possibility_downward_closure)
    solver.add(is_main_world)
    
    # Add basic exclusion properties
    print("\nAdding basic exclusion properties:")
    
    # Exclusion is symmetric
    solver.add(ForAll([x, y], excludes(x, y) == excludes(y, x)))
    
    # Nothing excludes the empty state (this is often assumed)
    solver.add(ForAll([x], z3.Not(excludes(x, 0))))
    
    print("- Exclusion is symmetric")
    print("- Nothing excludes the empty state")
    
    result = solver.check()
    print(f"\nSatisfiability: {result}")
    
    if result == z3.sat:
        model = solver.model()
        world_val = model.eval(main_world).as_long()
        print(f"main_world = {bin(world_val)}")
        
        # Check which states are possible
        print("\nPossible states:")
        for i in range(2**N):
            try:
                if z3.is_true(model.eval(possible(i))):
                    print(f"  {bin(i)} is possible")
            except:
                pass
    else:
        print("\nThe frame constraints are UNSAT!")
        
        # Try without possibility downward closure
        print("\nTesting without possibility downward closure:")
        solver2 = z3.Solver()
        
        # Just require main_world to be a world
        solver2.add(is_world(main_world))
        
        # Basic exclusion properties
        solver2.add(ForAll([x, y], excludes(x, y) == excludes(y, x)))
        solver2.add(ForAll([x], z3.Not(excludes(x, 0))))
        
        result2 = solver2.check()
        print(f"Result: {result2}")
        
        if result2 == z3.sat:
            print("The issue is with possibility downward closure!")

if __name__ == "__main__":
    test_actual_frame_constraints()