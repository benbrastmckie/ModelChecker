"""
Check if the three-condition semantics forces A to be true when \exclude A is true.
"""

import z3

def check_forced_truth():
    """Test if \exclude A being true forces A to be true."""
    
    print("=== Checking if \\exclude A forces A to be true ===")
    
    N = 3
    
    # Try different possible worlds
    test_worlds = [
        (0b001, "0b001 (only 'a')"),
        (0b010, "0b010 (only 'b')"), 
        (0b100, "0b100 (only 'c')"),
        (0b110, "0b110 ('b' and 'c', no 'a')"),
        (0b111, "0b111 (all bits)")
    ]
    
    for world_val, world_desc in test_worlds:
        print(f"\n--- Testing world = {world_desc} ---")
        
        solver = z3.Solver()
        world = z3.BitVecVal(world_val, N)
        
        # Skolem functions
        h_sk = z3.Function('h_sk', z3.BitVecSort(N), z3.BitVecSort(N))
        y_sk = z3.Function('y_sk', z3.BitVecSort(N), z3.BitVecSort(N))
        
        # Verifiers of A
        a_verifiers = [0b001, 0b011, 0b101, 0b111]
        
        # Add three conditions
        for v in a_verifiers:
            v_bv = z3.BitVecVal(v, N)
            # Condition 1
            solver.add((y_sk(v_bv) | v_bv) == v_bv)  # y_sk(v) ⊑ v
            solver.add((h_sk(v_bv) & y_sk(v_bv)) == 0)  # h_sk(v) excludes y_sk(v)
            # Condition 2
            solver.add((h_sk(v_bv) | world) == world)  # h_sk(v) ⊑ world
        
        # Condition 3: world is fusion
        fusion = z3.BitVecVal(0, N)
        for v in a_verifiers:
            v_bv = z3.BitVecVal(v, N)
            fusion = fusion | h_sk(v_bv)
        solver.add(world == fusion)
        
        # Check satisfiability
        result = solver.check()
        print(f"Can \\exclude A be true? {result}")
        
        if result == z3.sat:
            model = solver.model()
            print(f"A is {'TRUE' if (world_val & 0b001) else 'FALSE'} at this world")
            
            # Show one h_sk value as example
            h_example = model.eval(h_sk(0b111)).as_long()
            print(f"Example: h_sk(0b111) = {bin(h_example)}")
    
    print("\n=== Analysis ===")
    print("If \\exclude A can only be true at worlds where A is true,")
    print("then there would be no countermodel for NEG_TO_SENT.")
    print("\nBut our tests show \\exclude A CAN be true at world 0b100")
    print("where A is false. So the issue must be elsewhere.")

if __name__ == "__main__":
    check_forced_truth()