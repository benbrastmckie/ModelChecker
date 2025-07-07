"""
Debug why frame constraints make the system UNSAT.
"""

import z3
import sys
from pathlib import Path

# Add project root
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))

from model_checker.utils import ForAll

def debug_frame_constraints():
    """Test frame constraints one by one."""
    
    print("=== Debugging Frame Constraints ===")
    
    N = 3
    
    # Test each constraint individually
    print("\nTest 1: Just main_world != 0")
    solver1 = z3.Solver()
    main_world = z3.BitVec("main_world", N)
    solver1.add(main_world != 0)
    result1 = solver1.check()
    print(f"Result: {result1}")
    if result1 == z3.sat:
        print(f"Example: main_world = {bin(solver1.model().eval(main_world).as_long())}")
    
    print("\nTest 2: Possibility downward closure")
    solver2 = z3.Solver()
    main_world = z3.BitVec("main_world", N)
    x = z3.BitVec("frame_x", N)
    y = z3.BitVec("frame_y", N)
    
    # Original constraint from simulation
    downward_closure = ForAll([x, y], 
        z3.Implies(
            z3.And((x | main_world) == main_world, (y | x) == x),
            y != 0
        )
    )
    solver2.add(downward_closure)
    solver2.add(main_world != 0)
    
    result2 = solver2.check()
    print(f"Result with downward closure: {result2}")
    
    if result2 == z3.unsat:
        print("\nThe downward closure constraint is problematic!")
        print("Let's analyze what it says:")
        print("For all x, y: if (x is part of main_world) AND (y is part of x)")
        print("              then y != 0")
        print("\nThis means: no part of main_world can have 0 as a part")
        print("But 0 is part of everything! This creates a contradiction.")
        
        print("\nTest 3: Corrected downward closure")
        solver3 = z3.Solver()
        main_world = z3.BitVec("main_world", N)
        
        # A more reasonable constraint: if x is possible and y is part of x, then y is possible
        # But let's define "possible" properly
        def is_possible(state):
            # For now, all non-zero states are possible
            return state != 0
        
        # Only add main_world constraint
        solver3.add(main_world != 0)
        
        result3 = solver3.check()
        print(f"\nWithout problematic downward closure: {result3}")
        
        if result3 == z3.sat:
            print(f"main_world can be: {bin(solver3.model().eval(main_world).as_long())}")

if __name__ == "__main__":
    debug_frame_constraints()