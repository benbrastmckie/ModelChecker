"""
Test the premise constraint with different verifier patterns.
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

def test_patterns():
    """Test premise constraint with different verifier patterns."""
    
    print("=== Testing Premise Constraint with Different Patterns ===")
    
    settings = {'N': 3}
    sem = ExclusionSemantics(settings)
    
    # Frame constraints
    frame_constraints = sem._get_frame_constraints()
    
    # Atomic constraints
    letter_A = syntactic.AtomVal(0)
    atom_constraints = sem.atom_constraints(letter_A, [letter_A], {
        'contingent': True,
        'non_empty': True,
        'non_null': True,
    })
    
    # Test different patterns
    patterns = [
        ("Standard (a-bit)", [0b001, 0b011, 0b101, 0b111]),
        ("All except 0", [0b001, 0b010, 0b011, 0b100, 0b101, 0b110, 0b111]),
        ("Minimal", [0b001]),  # Just one verifier
    ]
    
    for pattern_name, verifiers in patterns:
        print(f"\n\nTesting pattern: {pattern_name}")
        print(f"Verifiers: {[bin(v) for v in verifiers]}")
        
        solver = z3.Solver()
        
        # Add frame constraints
        for constraint in frame_constraints:
            solver.add(constraint)
        
        # Add atomic constraints
        for label, constraint in atom_constraints:
            solver.add(constraint)
        
        # Force specific verifier pattern
        for i in range(8):
            if i in verifiers:
                solver.add(sem.verify(i, letter_A))
            else:
                solver.add(z3.Not(sem.verify(i, letter_A)))
        
        print("After frame + atomic + pattern:", solver.check())
        
        # Now add the premise constraint for \exclude A
        main_world = sem.main_world
        eval_point = {'world': main_world}
        
        # Build three-condition constraint manually
        h_sk = z3.Function('h_sk', z3.BitVecSort(3), z3.BitVecSort(3))
        y_sk = z3.Function('y_sk', z3.BitVecSort(3), z3.BitVecSort(3))
        
        x = z3.BitVec('x', 3)
        s = z3.BitVec('s', 3)
        
        # Condition 1: For verifiers x, y_sk(x) ⊑ x and h_sk(x) excludes y_sk(x)
        condition1 = ForAll([x],
            z3.Implies(
                z3.Or([x == v for v in verifiers]),  # x is a verifier
                z3.And(
                    (y_sk(x) | x) == x,
                    (h_sk(x) & y_sk(x)) == 0
                )
            )
        )
        
        # Condition 2: For verifiers x, h_sk(x) ⊑ main_world
        condition2 = ForAll([x],
            z3.Implies(
                z3.Or([x == v for v in verifiers]),
                (h_sk(x) | main_world) == main_world
            )
        )
        
        # Condition 3: main_world is minimal (fusion of h_sk values)
        # Build the fusion explicitly
        fusion_terms = []
        for v in verifiers:
            fusion_terms.append(h_sk(v))
        
        if fusion_terms:
            fusion = fusion_terms[0]
            for term in fusion_terms[1:]:
                fusion = fusion | term
        else:
            fusion = z3.BitVecVal(0, 3)
        
        # Instead of complex minimality, just require equality
        condition3 = (main_world == fusion)
        
        solver.add(condition1)
        solver.add(condition2)
        solver.add(condition3)
        
        result = solver.check()
        print(f"After adding premise constraint: {result}")
        
        if result == z3.sat:
            model = solver.model()
            world_val = model.eval(main_world).as_long()
            print(f"main_world = {bin(world_val)}")
            
            # Check if A is true at main_world
            a_true = any((v | world_val) == world_val for v in verifiers)
            print(f"A is {'TRUE' if a_true else 'FALSE'} at main_world")
            
            if not a_true:
                print("✓ Found countermodel where \\exclude A is true and A is false!")

if __name__ == "__main__":
    test_patterns()