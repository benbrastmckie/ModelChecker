"""
Compare nested quantifier approach vs direct constraint generation.
"""

import z3
import sys
from pathlib import Path

# Add project root
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))

from model_checker.utils import ForAll, Exists

def test_quantifier_approaches():
    """Compare different ways of expressing the constraints."""
    
    print("=== Comparing Quantifier Approaches ===")
    
    N = 3
    
    print("\nApproach 1: Nested quantifiers (like actual implementation)")
    solver1 = z3.Solver()
    
    world = z3.BitVec('world', N)
    h_sk = z3.Function('h_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    y_sk = z3.Function('y_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    
    # Helper to check if state verifies A
    def extended_verify_A(state):
        return (state & 0b001) != 0
    
    # Variables for quantification
    x = z3.BitVec('x', N)
    
    # Condition 1 with nested quantifiers
    condition1 = ForAll([x],
        z3.Implies(
            extended_verify_A(x),
            z3.And(
                (y_sk(x) | x) == x,
                (h_sk(x) & y_sk(x)) == 0
            )
        )
    )
    
    # Condition 2
    condition2 = ForAll([x],
        z3.Implies(
            extended_verify_A(x),
            (h_sk(x) | world) == world
        )
    )
    
    # Condition 3 - simplified to direct fusion
    # (The complex minimality might be part of the issue)
    fusion = z3.BitVecVal(0, N)
    for v in [0b001, 0b011, 0b101, 0b111]:
        fusion = fusion | h_sk(v)
    condition3 = (world == fusion)
    
    solver1.add(condition1)
    solver1.add(condition2)
    solver1.add(condition3)
    solver1.add(world != 0)  # non_empty
    solver1.add((world & 0b001) == 0)  # A is false
    
    print("Checking with nested quantifiers...")
    result1 = solver1.check()
    print(f"Result: {result1}")
    
    if result1 == z3.sat:
        model1 = solver1.model()
        world_val = model1.eval(world).as_long()
        print(f"Found world: {bin(world_val)}")
    
    print("\n\nApproach 2: Direct constraints (unrolled)")
    solver2 = z3.Solver()
    
    world2 = z3.BitVec('world2', N)
    h_sk2 = z3.Function('h_sk2', z3.BitVecSort(N), z3.BitVecSort(N))
    y_sk2 = z3.Function('y_sk2', z3.BitVecSort(N), z3.BitVecSort(N))
    
    # Directly add constraints for each verifier
    verifiers = [0b001, 0b011, 0b101, 0b111]
    for v in verifiers:
        v_bv = z3.BitVecVal(v, N)
        # Condition 1
        solver2.add((y_sk2(v_bv) | v) == v)
        solver2.add((h_sk2(v_bv) & y_sk2(v_bv)) == 0)
        # Condition 2
        solver2.add((h_sk2(v_bv) | world2) == world2)
    
    # Condition 3
    fusion2 = z3.BitVecVal(0, N)
    for v in verifiers:
        v_bv = z3.BitVecVal(v, N)
        fusion2 = fusion2 | h_sk2(v_bv)
    solver2.add(world2 == fusion2)
    
    solver2.add(world2 != 0)  # non_empty
    solver2.add((world2 & 0b001) == 0)  # A is false
    
    print("Checking with direct constraints...")
    result2 = solver2.check()
    print(f"Result: {result2}")
    
    if result2 == z3.sat:
        model2 = solver2.model()
        world_val2 = model2.eval(world2).as_long()
        print(f"Found world: {bin(world_val2)}")
    
    print("\n=== Analysis ===")
    if result1 != result2:
        print("Different results! The quantifier formulation matters.")
    else:
        print("Same results. The issue is likely elsewhere.")

if __name__ == "__main__":
    test_quantifier_approaches()