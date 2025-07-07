"""
Analyze why A has an unusual verifier pattern.
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

def analyze_pattern():
    """Analyze the verifier pattern for A."""
    
    print("=== Analyzing Verifier Pattern for A ===")
    
    settings = {
        'N': 3,
        'possible': False,
        'contingent': True,
        'non_empty': True,
        'non_null': True,
        'disjoint': False,
        'fusion_closure': False,
    }
    
    sem = ExclusionSemantics(settings)
    solver = z3.Solver()
    
    # Add frame constraints
    frame_constraints = sem._get_frame_constraints()
    for constraint in frame_constraints:
        solver.add(constraint)
    
    # Add atomic constraints
    letter_A = syntactic.AtomVal(0)
    atom_constraints = sem.atom_constraints(letter_A, [letter_A], settings)
    for label, constraint in atom_constraints:
        solver.add(constraint)
    
    if solver.check() == z3.sat:
        model = solver.model()
        
        print("\nCurrent verifier pattern for A:")
        verify = sem.verify
        verifiers = []
        non_verifiers = []
        
        for i in range(2**settings['N']):
            try:
                verifies = model.eval(verify(i, letter_A))
                if z3.is_true(verifies):
                    verifiers.append(i)
                    print(f"  {bin(i)} ({i}) verifies A")
                else:
                    non_verifiers.append(i)
            except:
                pass
        
        print(f"\nVerifiers: {[bin(v) for v in verifiers]}")
        print(f"Non-verifiers: {[bin(v) for v in non_verifiers]}")
        
        # Key observation: 0b000 doesn't verify A (due to non_null)
        # But ALL other states verify A!
        
        print("\n\nIMPORTANT DISCOVERY:")
        print("All states except 0b000 verify A!")
        print("This is NOT the standard 'states with a-bit' pattern.")
        
        # Now let's see what happens with \exclude A
        print("\n\nAnalyzing three-condition constraint with this pattern...")
        
        # If almost all states verify A, then the three conditions become:
        # 1. For almost all states x, there exists y ⊑ x and h(x) excludes y
        # 2. For almost all states x, h(x) ⊑ main_world
        # 3. main_world is the fusion of almost all h(x) values
        
        print("\nThis means:")
        print("- h_sk must be defined for 7 out of 8 states")
        print("- The fusion of these 7 h_sk values must equal main_world")
        print("- Each h_sk(x) must exclude some part of x")
        
        # Test if this is satisfiable
        print("\n\nTesting if three-condition constraint can be satisfied...")
        
        solver2 = z3.Solver()
        
        # Copy existing constraints
        for constraint in frame_constraints:
            solver2.add(constraint)
        for label, constraint in atom_constraints:
            solver2.add(constraint)
        
        # Add three-condition constraint
        main_world = sem.main_world
        h_sk = z3.Function('h_sk', z3.BitVecSort(3), z3.BitVecSort(3))
        y_sk = z3.Function('y_sk', z3.BitVecSort(3), z3.BitVecSort(3))
        
        # For each verifier (all except 0)
        for v in verifiers:
            v_bv = z3.BitVecVal(v, 3)
            # Condition 1: y_sk(v) ⊑ v and h_sk(v) excludes y_sk(v)
            solver2.add((y_sk(v_bv) | v) == v)
            solver2.add((h_sk(v_bv) & y_sk(v_bv)) == 0)
            # Condition 2: h_sk(v) ⊑ main_world
            solver2.add((h_sk(v_bv) | main_world) == main_world)
        
        # Condition 3: main_world is fusion of h_sk values
        fusion = z3.BitVecVal(0, 3)
        for v in verifiers:
            v_bv = z3.BitVecVal(v, 3)
            fusion = fusion | h_sk(v_bv)
        solver2.add(main_world == fusion)
        
        result = solver2.check()
        print(f"\nCan three-condition constraint be satisfied? {result}")
        
        if result == z3.unsat:
            print("\nThe issue is that with 7 verifiers, the fusion constraint")
            print("becomes very restrictive. We need the OR of 7 different")
            print("h_sk values to equal main_world exactly.")

if __name__ == "__main__":
    analyze_pattern()