"""
Demonstrate how to fix the incremental evaluation issue.
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

def demonstrate_fix():
    """Show how to fix the issue."""
    
    print("=== Demonstrating Fix for Incremental Evaluation ===")
    
    settings = {'N': 3}
    sem = ExclusionSemantics(settings)
    
    print("\nPROBLEM: Incremental evaluation locks verify(x, A) to partial model values")
    print("\nSOLUTION OPTIONS:")
    
    print("\n1. Don't check satisfiability after each constraint")
    print("   - Add all constraints first, then check once")
    print("   - This avoids premature model completion")
    
    solver1 = z3.Solver()
    
    # Add all frame constraints
    frame_constraints = sem._get_frame_constraints()
    for constraint in frame_constraints:
        solver1.add(constraint)
    
    # Add all atomic constraints
    letter_A = syntactic.AtomVal(0)
    atom_constraints = sem.atom_constraints(letter_A, [letter_A], {
        'contingent': True,
        'non_empty': True,
        'non_null': True,
    })
    for label, constraint in atom_constraints:
        solver1.add(constraint)
    
    # Add premise constraint WITHOUT checking first
    main_world = sem.main_world
    eval_point = {'world': main_world}
    
    # Get the premise constraint from the operator
    from operators import ExclusionOperator
    exclude_op = ExclusionOperator()
    exclude_op.semantics = sem
    
    # Create a mock sentence for A
    class MockSentence:
        def __init__(self, letter):
            self.sentence_letter = letter
            self.operator = None
    
    arg = MockSentence(letter_A)
    premise_constraint = exclude_op.true_at(arg, eval_point)
    
    solver1.add(premise_constraint)
    
    # NOW check satisfiability
    print("\nChecking with all constraints added at once...")
    result1 = solver1.check()
    print(f"Result: {result1}")
    
    if result1 == z3.sat:
        model = solver1.model()
        world_val = model.eval(main_world).as_long()
        print(f"main_world = {bin(world_val)}")
        
        # Check verifier pattern
        print("\nVerifier pattern in final model:")
        for i in range(8):
            if z3.is_true(model.eval(sem.verify(i, letter_A))):
                print(f"  {bin(i)} verifies A")
        
        # Check if we have a countermodel
        # A is false if no verifier is part of main_world
        verifiers = [i for i in range(8) if z3.is_true(model.eval(sem.verify(i, letter_A)))]
        a_true = any((v | world_val) == world_val for v in verifiers)
        
        print(f"\nA is {'TRUE' if a_true else 'FALSE'} at main_world")
        if not a_true:
            print("✓ COUNTERMODEL FOUND!")
    
    print("\n\n2. Alternative: Use fresh variables in quantifiers")
    print("   - Instead of verify(x, A), use a fresh function")
    print("   - Add constraints linking it to verify later")
    
    print("\n\n3. Alternative: Delay quantifier instantiation")
    print("   - Use custom quantifier handling")
    print("   - Only instantiate after model is more complete")
    
    print("\n\nCONCLUSION:")
    print("The incremental solver's eager satisfiability checking is")
    print("incompatible with complex quantified formulas that reference")
    print("functions that haven't been fully constrained yet.")

if __name__ == "__main__":
    demonstrate_fix()