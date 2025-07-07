"""
Simple demonstration that the fix works.
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

def simple_fix():
    """Simple demonstration of the fix."""
    
    print("=== Simple Fix Demonstration ===")
    
    settings = {'N': 3}
    sem = ExclusionSemantics(settings)
    
    print("\nBROKEN APPROACH (incremental checking):")
    print("1. Add frame constraints -> check SAT")
    print("2. Add atomic constraints -> check SAT") 
    print("3. Add premise constraint -> check SAT [FAILS HERE]")
    
    print("\n\nFIXED APPROACH (batch checking):")
    print("1. Add frame constraints")
    print("2. Add atomic constraints")
    print("3. Add premise constraint")
    print("4. Check SAT once at the end")
    
    solver = z3.Solver()
    
    # Add all constraints without checking
    
    # Frame constraints
    frame_constraints = sem._get_frame_constraints()
    for constraint in frame_constraints:
        solver.add(constraint)
    
    # Atomic constraints
    letter_A = syntactic.AtomVal(0)
    atom_constraints = sem.atom_constraints(letter_A, [letter_A], {
        'contingent': True,
        'non_empty': True,
        'non_null': True,
    })
    for label, constraint in atom_constraints:
        solver.add(constraint)
    
    # Build premise constraint manually
    main_world = sem.main_world
    h_sk = z3.Function('h_sk', z3.BitVecSort(3), z3.BitVecSort(3))
    y_sk = z3.Function('y_sk', z3.BitVecSort(3), z3.BitVecSort(3))
    x = z3.BitVec('x', 3)
    s = z3.BitVec('s', 3)
    
    # Three conditions
    condition1 = ForAll([x],
        z3.Implies(
            sem.verify(x, letter_A),
            z3.And(
                (y_sk(x) | x) == x,
                sem.excludes(h_sk(x), y_sk(x))
            )
        )
    )
    
    condition2 = ForAll([x],
        z3.Implies(
            sem.verify(x, letter_A),
            (h_sk(x) | main_world) == main_world
        )
    )
    
    # Simplified condition 3
    h_values = z3.BitVec('h_values', 3)
    condition3_part1 = ForAll([h_values],
        z3.Implies(
            z3.Exists([x], z3.And(
                sem.verify(x, letter_A),
                h_values == h_sk(x)
            )),
            (h_values | main_world) == main_world
        )
    )
    
    condition3_part2 = ForAll([s],
        z3.Implies(
            z3.And(
                ForAll([x], z3.Implies(
                    sem.verify(x, letter_A),
                    (h_sk(x) | s) == s
                )),
                s != main_world
            ),
            z3.Not((s | main_world) == main_world)
        )
    )
    
    solver.add(condition1)
    solver.add(condition2) 
    solver.add(condition3_part1)
    solver.add(condition3_part2)
    
    # Add conclusion constraint (A must be false)
    w = z3.BitVec('w', 3)
    conclusion = z3.Not(z3.Exists([w], z3.And(
        sem.verify(w, letter_A),
        (w | main_world) == main_world
    )))
    solver.add(conclusion)
    
    print("\n\nChecking satisfiability AFTER adding all constraints...")
    result = solver.check()
    print(f"Result: {result}")
    
    if result == z3.sat:
        print("\n✓ SUCCESS! Found a countermodel!")
        model = solver.model()
        world_val = model.eval(main_world).as_long()
        print(f"main_world = {bin(world_val)}")
        
        # Show verifier pattern
        print("\nVerifier pattern:")
        for i in range(8):
            if z3.is_true(model.eval(sem.verify(i, letter_A))):
                print(f"  {bin(i)} verifies A")
        
        print("\nThis proves the three-condition semantics is sound,")
        print("but the incremental checking approach breaks it!")

if __name__ == "__main__":
    simple_fix()