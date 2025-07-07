"""
Final diagnosis of the NEG_TO_SENT issue.
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

def final_diagnosis():
    """Final diagnosis with minimal test case."""
    
    print("=== Final Diagnosis of NEG_TO_SENT ===")
    
    # Minimal test with just atomic and premise constraints
    print("\nTest 1: Just atomic constraints + premise (no frame constraints)")
    
    solver = z3.Solver()
    N = 3
    
    # Functions
    verify = z3.Function('verify', z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())
    excludes = z3.Function('excludes', z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())
    
    letter_A = syntactic.AtomVal(0)
    main_world = z3.BitVec('main_world', N)
    
    # Minimal atomic constraints
    v = z3.BitVec('v', N)
    
    # Some state verifies A
    solver.add(z3.Exists([v], verify(v, letter_A)))
    # State 0 doesn't verify A
    solver.add(z3.Not(verify(0, letter_A)))
    
    # Basic exclusion properties
    x = z3.BitVec('x', N)
    y = z3.BitVec('y', N)
    solver.add(z3.ForAll([x, y], excludes(x, y) == excludes(y, x)))  # Symmetric
    solver.add(z3.ForAll([x], z3.Not(excludes(x, 0))))  # Nothing excludes 0
    
    # Three-condition constraint for \\exclude A
    h_sk = z3.Function('h_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    y_sk = z3.Function('y_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    
    # Simplified three conditions
    solver.add(z3.ForAll([x],
        z3.Implies(
            verify(x, letter_A),
            z3.And(
                (y_sk(x) | x) == x,
                excludes(h_sk(x), y_sk(x))
            )
        )
    ))
    
    solver.add(z3.ForAll([x],
        z3.Implies(
            verify(x, letter_A),
            (h_sk(x) | main_world) == main_world
        )
    ))
    
    # Just require world != 0 for simplicity
    solver.add(main_world != 0)
    
    # A is false at main_world
    w = z3.BitVec('w', N)
    solver.add(z3.Not(z3.Exists([w], z3.And(
        verify(w, letter_A),
        (w | main_world) == main_world
    ))))
    
    print("Checking...")
    result = solver.check()
    print(f"Result: {result}")
    
    if result == z3.sat:
        model = solver.model()
        world_val = model.eval(main_world).as_long()
        print(f"main_world = {bin(world_val)}")
        
        # Check verifiers
        print("\nVerifiers of A:")
        for i in range(8):
            try:
                if z3.is_true(model.eval(verify(i, letter_A))):
                    print(f"  {bin(i)}")
            except:
                pass
    
    print("\n\nTest 2: What if we specify verifier pattern explicitly?")
    
    solver2 = z3.Solver()
    
    # Same setup
    verify2 = z3.Function('verify2', z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())
    excludes2 = z3.Function('excludes2', z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())
    main_world2 = z3.BitVec('main_world2', N)
    
    # Force standard pattern: only states with 'a' bit verify A
    for i in range(8):
        if i & 0b001:
            solver2.add(verify2(i, letter_A))
        else:
            solver2.add(z3.Not(verify2(i, letter_A)))
    
    # Basic exclusion
    solver2.add(z3.ForAll([x, y], excludes2(x, y) == excludes2(y, x)))
    solver2.add(z3.ForAll([x], z3.Not(excludes2(x, 0))))
    
    # Three conditions with explicit verifiers
    h_sk2 = z3.Function('h_sk2', z3.BitVecSort(N), z3.BitVecSort(N))
    y_sk2 = z3.Function('y_sk2', z3.BitVecSort(N), z3.BitVecSort(N))
    
    for v in [1, 3, 5, 7]:  # The explicit verifiers
        v_bv = z3.BitVecVal(v, N)
        solver2.add((y_sk2(v_bv) | v) == v)
        solver2.add(excludes2(h_sk2(v_bv), y_sk2(v_bv)))
        solver2.add((h_sk2(v_bv) | main_world2) == main_world2)
    
    # World is fusion of h_sk values
    fusion = h_sk2(1) | h_sk2(3) | h_sk2(5) | h_sk2(7)
    solver2.add(main_world2 == fusion)
    
    # A is false (no verifier is part of world)
    solver2.add((main_world2 & 0b001) == 0)
    
    print("\nWith explicit standard pattern...")
    result2 = solver2.check()
    print(f"Result: {result2}")
    
    if result2 == z3.sat:
        model2 = solver2.model()
        world_val2 = model2.eval(main_world2).as_long()
        print(f"main_world = {bin(world_val2)}")
        print("\n✓ SUCCESS with explicit pattern!")

if __name__ == "__main__":
    final_diagnosis()