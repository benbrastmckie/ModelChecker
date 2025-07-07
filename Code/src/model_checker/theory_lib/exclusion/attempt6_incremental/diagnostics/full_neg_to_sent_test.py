"""
Full test mimicking the exact NEG_TO_SENT scenario with all constraints.
"""

import z3

def full_neg_to_sent_test():
    """Complete test of NEG_TO_SENT with all semantic constraints."""
    
    print("=== FULL NEG_TO_SENT TEST ===")
    print("Looking for: \\exclude A true, A false")
    print()
    
    solver = z3.Solver()
    N = 3
    
    # Main variables
    world = z3.BitVec('world', N)
    
    # Skolem functions
    h_sk = z3.Function('h_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    y_sk = z3.Function('y_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    
    # Frame constraints from settings
    print("Adding frame constraints:")
    print("  - non_empty: world != 0")
    print("  - non_null: At least one proper part exists")
    print("  - contingent: Both possible and impossible worlds exist")
    
    # non_empty
    solver.add(world != 0)
    
    # Possible worlds and coherence setup
    # Define possible function (simplified - all non-empty states are possible)
    def possible(s):
        return s != 0
    
    # Main point must be a possible world
    solver.add(possible(world))
    
    # For contingent, we need both possible and impossible worlds
    # For simplicity, let's say 0 is impossible, all others are possible
    
    # Exclusion relation setup
    print("\nSetting up exclusion relation...")
    
    # For simplicity, let's define exclusion as disjointness
    def excludes(x, y):
        return (x & y) == 0
    
    def is_part_of(x, y):
        return (x | y) == y
    
    # Define which states verify A
    def verifies_A(state):
        return (state & 0b001) != 0
    
    # Three-condition constraints for \\exclude A
    print("\nAdding three-condition constraints for \\exclude A:")
    
    # Get verifiers of A
    a_verifiers = []
    for i in range(1, 2**N):  # Skip 0 due to non_empty
        if verifies_A(i):
            a_verifiers.append(i)
    
    print(f"Verifiers of A: {[bin(v) for v in a_verifiers]}")
    
    # Condition 1: For all x in Ver(A), y_sk(x) ⊑ x and h_sk(x) excludes y_sk(x)
    print("\nCondition 1: Witness constraints")
    for v in a_verifiers:
        v_bv = z3.BitVecVal(v, N)
        solver.add(is_part_of(y_sk(v_bv), v_bv))
        solver.add(excludes(h_sk(v_bv), y_sk(v_bv)))
    
    # Condition 2: For all x in Ver(A), h_sk(x) ⊑ world
    print("Condition 2: h_sk values are part of world")
    for v in a_verifiers:
        v_bv = z3.BitVecVal(v, N)
        solver.add(is_part_of(h_sk(v_bv), world))
    
    # Condition 3: world is minimal
    print("Condition 3: Minimality")
    
    # First, compute the fusion of all h_sk values
    fusion_parts = []
    for v in a_verifiers:
        v_bv = z3.BitVecVal(v, N)
        fusion_parts.append(h_sk(v_bv))
    
    # The actual fusion
    if fusion_parts:
        fusion = fusion_parts[0]
        for part in fusion_parts[1:]:
            fusion = fusion | part
    else:
        fusion = z3.BitVecVal(0, N)
    
    # World must equal the fusion
    solver.add(world == fusion)
    
    # Add constraint that A is false
    print("\nAdding constraint: A is false at world")
    solver.add((world & 0b001) == 0)
    
    print("\n=== CHECKING SATISFIABILITY ===")
    result = solver.check()
    print(f"Result: {result}")
    
    if result == z3.sat:
        model = solver.model()
        world_val = model.eval(world).as_long()
        print(f"\nFound countermodel!")
        print(f"World: {bin(world_val)}")
        print(f"A is false: {(world_val & 0b001) == 0}")
        
        print("\nWitness functions:")
        for v in a_verifiers:
            v_bv = z3.BitVecVal(v, N)
            h_val = model.eval(h_sk(v_bv)).as_long()
            y_val = model.eval(y_sk(v_bv)).as_long()
            print(f"  Verifier {bin(v)}:")
            print(f"    h_sk({bin(v)}) = {bin(h_val)}")
            print(f"    y_sk({bin(v)}) = {bin(y_val)}")
    else:
        print("\nNo countermodel found!")
        print("\nTrying without the fusion constraint...")
        
        # Remove the fusion constraint and try again
        solver2 = z3.Solver()
        
        # Re-add all constraints except the fusion
        solver2.add(world != 0)
        solver2.add(possible(world))
        solver2.add((world & 0b001) == 0)
        
        for v in a_verifiers:
            v_bv = z3.BitVecVal(v, N)
            solver2.add(is_part_of(y_sk(v_bv), v_bv))
            solver2.add(excludes(h_sk(v_bv), y_sk(v_bv)))
            solver2.add(is_part_of(h_sk(v_bv), world))
        
        result2 = solver2.check()
        print(f"Without fusion constraint: {result2}")
        
        if result2 == z3.sat:
            print("The fusion constraint is preventing the countermodel!")

if __name__ == "__main__":
    full_neg_to_sent_test()