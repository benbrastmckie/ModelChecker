"""
Test the minimality constraint to see if it allows world to be larger than the fusion.
"""

import z3

def test_minimality_constraint():
    """Test if the current minimality constraint allows incorrect models."""
    
    print("=== Testing Minimality Constraint ===")
    
    N = 3
    world = z3.BitVec('world', N)
    h_sk = z3.Function('h_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    
    # Verifiers of A
    a_verifiers = [0b001, 0b011, 0b101, 0b111]
    
    print("\nTest 1: Current minimality constraint")
    solver1 = z3.Solver()
    
    # Force all h_sk to map to 0b000
    for v in a_verifiers:
        v_bv = z3.BitVecVal(v, N)
        solver1.add(h_sk(v_bv) == 0b000)
    
    # Add the current minimality constraint
    s = z3.BitVec('s', N)
    x = z3.BitVec('x', N)
    
    # condition3_minimal from the code
    condition3_minimal = z3.ForAll([s],
        z3.Implies(
            z3.And(
                z3.ForAll([x], z3.Implies(
                    z3.Or([x == v for v in a_verifiers]),  # x is a verifier of A
                    (h_sk(x) | s) == s  # h_sk(x) is part of s
                )),
                s != world
            ),
            z3.Not((s | world) == world)  # s is not part of world
        )
    )
    
    solver1.add(condition3_minimal)
    
    # Force world to be non-empty
    solver1.add(world == 0b100)  # Has 'c' bit but not 'a' bit
    
    # Check if this is allowed
    result1 = solver1.check()
    print(f"Can world be 0b100 when all h_sk map to 0b000? {result1}")
    
    if result1 == z3.sat:
        print("YES - The current constraint allows world to be larger than the fusion!")
        
    print("\nTest 2: Proper fusion constraint")
    solver2 = z3.Solver()
    
    # Force all h_sk to map to 0b000
    for v in a_verifiers:
        v_bv = z3.BitVecVal(v, N)
        solver2.add(h_sk(v_bv) == 0b000)
    
    # Add proper fusion constraint: world equals the OR of all h_sk values
    fusion = z3.BitVecVal(0, N)
    for v in a_verifiers:
        v_bv = z3.BitVecVal(v, N)
        fusion = fusion | h_sk(v_bv)
    
    solver2.add(world == fusion)
    
    # Check what world must be
    result2 = solver2.check()
    if result2 == z3.sat:
        model2 = solver2.model()
        world_val = model2.eval(world).as_long()
        print(f"With proper fusion constraint, world must be: {bin(world_val)}")
    
    print("\n=== CONCLUSION ===")
    print("The current minimality constraint doesn't enforce world = fusion(h_sk values)")
    print("It only ensures no proper substate of world contains all h_sk values")
    print("This allows world to have extra bits beyond what's needed!")

if __name__ == "__main__":
    test_minimality_constraint()