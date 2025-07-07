"""
Simulate the exact solving process for NEG_TO_SENT to find where it fails.
"""

import z3
import sys
from pathlib import Path

# Add project root
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))

from model_checker.utils import ForAll, Exists
from model_checker import syntactic

def simulate_solving():
    """Simulate the incremental solving process step by step."""
    
    print("=== Simulating NEG_TO_SENT Solving Process ===")
    
    N = 3
    solver = z3.Solver()
    
    # Main world variable
    main_world = z3.BitVec("main_world", N)
    
    # Functions
    verify = z3.Function("verify", z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())
    excludes = z3.Function("excludes", z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())
    
    # Atomic proposition A
    letter_A = syntactic.AtomVal(0)
    
    print("\nPhase 1: Frame Constraints")
    print("-" * 50)
    
    # Basic frame constraints
    x = z3.BitVec("frame_x", N)
    y = z3.BitVec("frame_y", N)
    
    # Possibility downward closure (simplified)
    print("Adding: Possibility downward closure")
    solver.add(ForAll([x, y], 
        z3.Implies(
            z3.And((x | main_world) == main_world, (y | x) == x),
            y != 0  # Simplified: non-zero states are possible
        )
    ))
    
    # Main world is non-empty
    print("Adding: main_world != 0")
    solver.add(main_world != 0)
    
    # Exclusion is symmetric
    print("Adding: Exclusion is symmetric")
    solver.add(ForAll([x, y], excludes(x, y) == excludes(y, x)))
    
    print(f"Satisfiable after frame constraints? {solver.check()}")
    
    print("\nPhase 2: Atomic Constraints for A")
    print("-" * 50)
    
    # NEG_TO_SENT settings
    v = z3.BitVec("atom_v", N)
    
    # Contingent
    print("Adding: A is contingent")
    solver.add(Exists([v], verify(v, letter_A)))
    solver.add(Exists([v], z3.Not(verify(v, letter_A))))
    
    # Non-null
    print("Adding: A is non-null (0 doesn't verify A)")
    solver.add(z3.Not(verify(0, letter_A)))
    
    print(f"Satisfiable after atomic constraints? {solver.check()}")
    
    print("\nPhase 3: Premise Constraint (\\exclude A must be true)")
    print("-" * 50)
    
    # The three-condition constraint for \exclude A
    h_sk = z3.Function('h_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    y_sk = z3.Function('y_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    
    print("Adding: Three-condition constraints for \\exclude A")
    
    # For quantification
    x_var = z3.BitVec('x_ex', N)
    s_var = z3.BitVec('s_ex', N)
    
    # Condition 1
    condition1 = ForAll([x_var],
        z3.Implies(
            verify(x_var, letter_A),  # x verifies A
            z3.And(
                (y_sk(x_var) | x_var) == x_var,  # y_sk(x) ⊑ x
                (h_sk(x_var) & y_sk(x_var)) == 0  # h_sk(x) excludes y_sk(x)
            )
        )
    )
    solver.add(condition1)
    print("Added: Condition 1 (witness properties)")
    
    # Condition 2
    condition2 = ForAll([x_var],
        z3.Implies(
            verify(x_var, letter_A),
            (h_sk(x_var) | main_world) == main_world
        )
    )
    solver.add(condition2)
    print("Added: Condition 2 (h_sk values part of world)")
    
    # Condition 3 - the complex minimality
    # First part: h_sk values are part of world (already in condition 2)
    # Second part: world is minimal
    condition3_minimal = ForAll([s_var],
        z3.Implies(
            z3.And(
                ForAll([x_var], z3.Implies(
                    verify(x_var, letter_A),
                    (h_sk(x_var) | s_var) == s_var
                )),
                s_var != main_world
            ),
            z3.Not((s_var | main_world) == main_world)
        )
    )
    solver.add(condition3_minimal)
    print("Added: Condition 3 (minimality)")
    
    print(f"Satisfiable after premise constraint? {solver.check()}")
    
    print("\nPhase 4: Conclusion Constraint (A must be false)")
    print("-" * 50)
    
    # A is false at main_world
    w = z3.BitVec("w_conclusion", N)
    conclusion_constraint = z3.Not(Exists([w], z3.And(
        verify(w, letter_A),
        (w | main_world) == main_world
    )))
    
    print("Adding: A is false at main_world")
    solver.add(conclusion_constraint)
    
    print(f"\nFinal satisfiability check: {solver.check()}")
    
    if solver.check() == z3.sat:
        model = solver.model()
        world_val = model.eval(main_world).as_long()
        print(f"\nFound countermodel!")
        print(f"main_world = {bin(world_val)}")
    else:
        print("\nNo countermodel found!")
        
        # Try to identify which constraint is problematic
        print("\n\nDebugging: Testing without conclusion constraint")
        solver.pop()  # Remove conclusion constraint
        if solver.check() == z3.sat:
            model = solver.model()
            world_val = model.eval(main_world).as_long()
            print(f"Without conclusion constraint, main_world = {bin(world_val)}")
            
            # Check if A is true at this world
            print("\nChecking if A is true at this world...")
            # We need to check if any verifier of A is part of world
            for i in range(1, 2**N):  # Skip 0
                if model.eval(verify(i, letter_A)):
                    if (i | world_val) == world_val:
                        print(f"State {bin(i)} verifies A and is part of world")
                        print("This explains why adding 'A is false' makes it UNSAT")

if __name__ == "__main__":
    simulate_solving()