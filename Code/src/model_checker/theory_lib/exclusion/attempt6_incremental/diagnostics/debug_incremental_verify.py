"""
Debug what happens when premise constraint is evaluated incrementally.
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
from model_checker.utils import ForAll

def debug_incremental():
    """Debug the incremental evaluation issue."""
    
    print("=== Debugging Incremental Verify Issue ===")
    
    settings = {'N': 3}
    sem = ExclusionSemantics(settings)
    
    # Build constraints exactly as incremental solver does
    solver = z3.Solver()
    
    # 1. Add frame constraints
    print("\n1. Adding frame constraints...")
    frame_constraints = sem._get_frame_constraints()
    for constraint in frame_constraints:
        solver.add(constraint)
    
    # 2. Add atomic constraints
    print("\n2. Adding atomic constraints...")
    letter_A = syntactic.AtomVal(0)
    atom_constraints = sem.atom_constraints(letter_A, [letter_A], {
        'contingent': True,
        'non_empty': True,
        'non_null': True,
    })
    for label, constraint in atom_constraints:
        solver.add(constraint)
    
    # Get partial model after frame + atomic
    if solver.check() == z3.sat:
        model = solver.model()
        
        print("\n3. Checking verifier pattern in partial model:")
        verify_func = sem.verify
        
        # The issue: Z3 might not have fully determined verify values yet
        for i in range(8):
            try:
                val = model.eval(verify_func(i, letter_A), model_completion=True)
                print(f"  verify({i}, A) = {val}")
            except:
                print(f"  verify({i}, A) = UNKNOWN")
        
        # When model_completion=True, Z3 fills in arbitrary values
        # This might create the "all except 0" pattern
        
        print("\n4. The problem:")
        print("When the incremental solver checks satisfiability after adding")
        print("the premise constraint, Z3 uses the CURRENT partial model to")
        print("evaluate verify(i, A) in the quantified formulas.")
        print("")
        print("If the partial model has verify(i, A) = True for i=1..7,")
        print("then the three-condition constraint requires:")
        print("- h_sk must be defined for 7 states")
        print("- The fusion of 7 h_sk values must equal main_world")
        print("- This is much more restrictive than necessary!")
        
        # Test: Can we satisfy three-condition with this specific pattern?
        print("\n5. Testing three-condition with the partial model's pattern...")
        
        # Extract the pattern from model
        verifiers = []
        for i in range(8):
            if z3.is_true(model.eval(verify_func(i, letter_A), model_completion=True)):
                verifiers.append(i)
        
        print(f"\nVerifiers in partial model: {[bin(v) for v in verifiers]}")
        
        # Now test if three-condition can be satisfied with this pattern
        solver2 = z3.Solver()
        
        # Copy all existing constraints
        solver2.add(solver.assertions())
        
        # Build three-condition constraint
        main_world = sem.main_world
        h_sk = z3.Function('h_sk', z3.BitVecSort(3), z3.BitVecSort(3))
        y_sk = z3.Function('y_sk', z3.BitVecSort(3), z3.BitVecSort(3))
        
        # The actual constraint that gets generated
        x = z3.BitVec('x', 3)
        
        # Here's the key: the constraint uses verify(x, A) which gets evaluated
        # using the PARTIAL model's interpretation
        condition1 = ForAll([x],
            z3.Implies(
                verify_func(x, letter_A),  # This uses partial model!
                z3.And(
                    (y_sk(x) | x) == x,
                    sem.excludes(h_sk(x), y_sk(x))
                )
            )
        )
        
        solver2.add(condition1)
        
        # Similar for other conditions...
        # (simplified for clarity)
        
        result = solver2.check()
        print(f"\nCan three-condition be satisfied? {result}")
        
        if result == z3.unsat:
            print("\nTHE BUG:")
            print("The incremental solver evaluates verify(x, A) using the")
            print("partial model, which locks in a specific verifier pattern")
            print("that makes the three-condition constraint unsatisfiable!")

if __name__ == "__main__":
    debug_incremental()