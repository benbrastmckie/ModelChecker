"""
Test if the non_empty constraint is preventing the countermodel.
"""

import z3

def test_with_non_empty():
    """Test the constraints with non_empty requirement."""
    
    print("=== Testing NEG_TO_SENT with non_empty constraint ===")
    
    solver = z3.Solver()
    N = 3
    world = z3.BitVec('world', N)
    
    # Add non_empty constraint: world != 0
    print("Adding non_empty constraint: world != 0")
    solver.add(world != 0)
    
    # Add constraint that A is false at world
    print("Adding constraint: A is false (bit 0 not set)")
    solver.add((world & 0b001) == 0)
    
    # Define h_sk and y_sk functions
    h_sk = z3.Function('h_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    y_sk = z3.Function('y_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    
    # Verifiers of A
    a_verifiers = [0b001, 0b011, 0b101, 0b111]
    
    # Add three conditions
    for v in a_verifiers:
        v_bv = z3.BitVecVal(v, N)
        # Condition 1: y_sk(v) ⊑ v and h_sk(v) excludes y_sk(v)
        solver.add((y_sk(v_bv) | v_bv) == v_bv)
        solver.add((h_sk(v_bv) & y_sk(v_bv)) == 0)
        # Condition 2: h_sk(v) ⊑ world
        solver.add((h_sk(v_bv) | world) == world)
    
    # Condition 3: world is fusion of h_sk values
    fusion = z3.BitVecVal(0, N)
    for v in a_verifiers:
        v_bv = z3.BitVecVal(v, N)
        fusion = fusion | h_sk(v_bv)
    solver.add(world == fusion)
    
    print("\nChecking satisfiability WITH non_empty constraint...")
    result = solver.check()
    print(f"Result: {result}")
    
    if result == z3.sat:
        model = solver.model()
        world_val = model.eval(world).as_long()
        print(f"\nFound model with world = {bin(world_val)}")
        print(f"World has 'a' bit: {bool(world_val & 0b001)}")
        
        print("\nSkolem functions:")
        for v in a_verifiers:
            v_bv = z3.BitVecVal(v, N)
            h_val = model.eval(h_sk(v_bv)).as_long()
            print(f"  h_sk({bin(v)}) = {bin(h_val)}")
    else:
        print("\nNo model found with non_empty constraint!")
        
        # Test without non_empty
        print("\n=== Testing WITHOUT non_empty constraint ===")
        solver2 = z3.Solver()
        
        # Same constraints but without world != 0
        solver2.add((world & 0b001) == 0)
        
        for v in a_verifiers:
            v_bv = z3.BitVecVal(v, N)
            solver2.add((y_sk(v_bv) | v_bv) == v_bv)
            solver2.add((h_sk(v_bv) & y_sk(v_bv)) == 0)
            solver2.add((h_sk(v_bv) | world) == world)
        
        fusion = z3.BitVecVal(0, N)
        for v in a_verifiers:
            v_bv = z3.BitVecVal(v, N)
            fusion = fusion | h_sk(v_bv)
        solver2.add(world == fusion)
        
        result2 = solver2.check()
        print(f"Result: {result2}")
        
        if result2 == z3.sat:
            model2 = solver2.model()
            world_val2 = model2.eval(world).as_long()
            print(f"\nFound model with world = {bin(world_val2)}")
            print("This confirms the non_empty constraint is blocking the countermodel!")

if __name__ == "__main__":
    test_with_non_empty()