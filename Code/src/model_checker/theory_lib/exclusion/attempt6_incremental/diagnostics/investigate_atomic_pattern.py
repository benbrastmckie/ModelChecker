"""
Investigate why atomic constraints produce the 'all except 0' verifier pattern.
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
from model_checker.utils import ForAll, Exists

def investigate_atomic():
    """Figure out why A has all states except 0 as verifiers."""
    
    print("=== Investigating Atomic Constraint Pattern ===")
    
    settings = {
        'N': 3,
        'contingent': True,
        'non_empty': True,
        'non_null': True,
    }
    
    # Just atomic constraints, no frame constraints
    solver = z3.Solver()
    
    # Create verify function
    verify = z3.Function('verify', z3.BitVecSort(3), syntactic.AtomSort, z3.BoolSort())
    letter_A = syntactic.AtomVal(0)
    
    # Variable for constraints
    v = z3.BitVec('v', 3)
    
    print("Adding atomic constraints manually:")
    
    # 1. Contingent positive: some state verifies A
    print("1. Some state verifies A")
    solver.add(Exists([v], verify(v, letter_A)))
    
    # 2. Contingent negative: some state doesn't verify A  
    print("2. Some state doesn't verify A")
    solver.add(Exists([v], z3.Not(verify(v, letter_A))))
    
    # 3. Non-empty: at least one state verifies A (redundant with contingent positive)
    print("3. At least one state verifies A (non_empty)")
    solver.add(Exists([v], verify(v, letter_A)))
    
    # 4. Non-null: state 0 doesn't verify A
    print("4. State 0 doesn't verify A (non_null)")
    solver.add(z3.Not(verify(0, letter_A)))
    
    print("\nFinding minimal solutions...")
    
    # These constraints only require:
    # - At least one state verifies A
    # - At least one state doesn't verify A
    # - State 0 doesn't verify A
    
    # Count solutions with different numbers of verifiers
    for num_verifiers in range(1, 8):
        solver.push()
        
        # Add constraint that exactly num_verifiers states verify A
        count = z3.Sum([z3.If(verify(i, letter_A), 1, 0) for i in range(8)])
        solver.add(count == num_verifiers)
        
        if solver.check() == z3.sat:
            print(f"\nSolution with {num_verifiers} verifiers exists")
            model = solver.model()
            verifiers = []
            for i in range(8):
                if z3.is_true(model.eval(verify(i, letter_A))):
                    verifiers.append(i)
            print(f"  Verifiers: {[bin(v) for v in verifiers]}")
        
        solver.pop()
    
    print("\n\nKEY INSIGHT:")
    print("The atomic constraints allow many different verifier patterns!")
    print("The 'all except 0' pattern must come from interaction with frame constraints.")
    
    # Now add frame constraints and see what happens
    print("\n\n=== Adding Frame Constraints ===")
    
    sem = ExclusionSemantics({'N': 3})
    solver2 = z3.Solver()
    
    # Add frame constraints
    frame_constraints = sem._get_frame_constraints()
    for constraint in frame_constraints:
        solver2.add(constraint)
    
    # Now add atomic constraints
    atom_constraints = sem.atom_constraints(letter_A, [letter_A], settings)
    for label, constraint in atom_constraints:
        solver2.add(constraint)
    
    # Try to force the standard pattern (states with 'a' bit)
    print("\nTesting if standard pattern is possible with frame constraints...")
    solver2.push()
    
    # Standard pattern: 1, 3, 5, 7 verify A (states with bit 0 set)
    # Non-verifiers: 0, 2, 4, 6
    for i in range(8):
        if i & 0b001:  # Has 'a' bit
            solver2.add(sem.verify(i, letter_A))
        else:
            solver2.add(z3.Not(sem.verify(i, letter_A)))
    
    result = solver2.check()
    print(f"Can we have standard pattern? {result}")
    
    if result == z3.unsat:
        print("\nThe frame constraints PREVENT the standard pattern!")
        print("This is why we get the 'all except 0' pattern.")
        
        # Let's find out which frame constraint causes this
        solver3 = z3.Solver()
        
        # Add atomic constraints first
        for label, constraint in atom_constraints:
            solver3.add(constraint)
        
        # Add frame constraints one by one
        print("\nAdding frame constraints one by one...")
        for i, constraint in enumerate(frame_constraints):
            solver3.push()
            solver3.add(constraint)
            
            # Try standard pattern
            for j in range(8):
                if j & 0b001:
                    solver3.add(sem.verify(j, letter_A))
                else:
                    solver3.add(z3.Not(sem.verify(j, letter_A)))
            
            if solver3.check() == z3.unsat:
                print(f"  Frame constraint {i} prevents standard pattern!")
                break
            else:
                print(f"  Frame constraint {i} OK")
            
            solver3.pop()

if __name__ == "__main__":
    investigate_atomic()