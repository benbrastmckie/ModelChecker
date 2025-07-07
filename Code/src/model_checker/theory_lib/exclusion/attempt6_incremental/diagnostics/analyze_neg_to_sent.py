"""
Diagnostic script to analyze why NEG_TO_SENT_example has no countermodel.

This script investigates the constraint generation for the example:
Premise: \\exclude A
Conclusion: A
Expected: Should have a countermodel (false expectation)
"""

import z3
import sys
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from semantic import ExclusionSemantics, UnilateralProposition
from operators import exclusion_operators
from incremental_model import IncrementalModelStructure
from model_checker import syntactic

def analyze_neg_to_sent():
    """Analyze the NEG_TO_SENT example step by step."""
    
    print("=== ANALYZING NEG_TO_SENT EXAMPLE ===")
    print("Premise: \\exclude A")
    print("Conclusion: A")
    print("Expected: Should have countermodel where premise is true but conclusion is false")
    print()
    
    # Create semantics with N=3
    settings = {'N': 3}
    sem = ExclusionSemantics(settings)
    
    # Create syntax parser
    syntax = syntactic.Syntax(["\\exclude A"], ["A"], exclusion_operators)
    
    # Get the parsed formulas from syntax
    premise = syntax.premises[0]
    conclusion = syntax.conclusions[0]
    
    print("=== STEP 1: ANALYZE FORMULA STRUCTURE ===")
    print(f"Premise: {premise}")
    print(f"Premise has operator: {hasattr(premise, 'original_operator')}")
    if hasattr(premise, 'original_operator') and premise.original_operator:
        print(f"Premise operator: {premise.original_operator}")
        if hasattr(premise, 'original_arguments') and premise.original_arguments:
            print(f"Premise argument: {premise.original_arguments[0]}")
    print(f"Conclusion: {conclusion}")
    print(f"Conclusion is atomic: {conclusion.sentence_letter is not None}")
    print()
    
    print("=== STEP 2: ANALYZE VERIFIERS ===")
    # Get all possible states
    all_states = list(sem.get_all_bitvectors())
    print(f"Total states: {len(all_states)}")
    
    # Analyze verifiers for A
    print("\nChecking which states have the 'a' bit:")
    a_verifiers = []
    for state in all_states:
        state_int = state if isinstance(state, int) else state.as_long()
        has_a_bit = (state_int & 0b001) != 0
        if has_a_bit:
            a_verifiers.append(state_int)
            print(f"  State {bin(state_int)}: has 'a' bit (verifies A)")
    
    print(f"\nTotal states with 'a' bit (verifiers for A): {len(a_verifiers)}")
    
    print("\n=== STEP 3: ANALYZE EXCLUSION OPERATOR ===")
    print("ExclusionOperator.true_at generates three conditions:")
    print("1. For all x in Ver(A), y_sk(x) is part of x and h_sk(x) excludes y_sk(x)")
    print("2. For all x in Ver(A), h_sk(x) is part of eval_world")
    print("3. eval_world is minimal (fusion of all h_sk(x))")
    print()
    
    print("=== STEP 4: CHECK CONSTRAINT GENERATION ===")
    # Create a simple solver to test constraints
    solver = z3.Solver()
    
    # Add variables
    world = z3.BitVec('world', 3)
    
    # Get the ExclusionOperator from the premise
    exclude_op = premise.original_operator
    exclude_op.semantics = sem
    
    # Generate constraints for \exclude A being true at world
    print("Generating constraints for \\exclude A true at world...")
    
    # Create eval_point
    eval_point = {'world': world}
    
    # Get the constraint - ExclusionOperator is unary
    exclude_a_true = exclude_op.true_at(premise.original_arguments[0], eval_point)
    
    print("\nConstraint type:", type(exclude_a_true))
    
    # Add constraint that premise is true
    solver.add(exclude_a_true)
    
    # Add constraint that conclusion is false (A is false at world)
    # A is false when world doesn't have the 'a' bit
    a_false = (world & 0b001) == 0
    solver.add(a_false)
    
    print("\n=== STEP 5: CHECK SATISFIABILITY ===")
    result = solver.check()
    print(f"Solver result: {result}")
    
    if result == z3.sat:
        model = solver.model()
        world_val = model.eval(world).as_long()
        print(f"Found countermodel with world = {bin(world_val)}")
    else:
        print("No countermodel found - constraints are UNSAT")
        
        # Try to find why
        print("\n=== STEP 6: ANALYZE UNSATISFIABILITY ===")
        
        # Test if \exclude A can be true anywhere
        solver2 = z3.Solver()
        solver2.add(exclude_a_true)
        result2 = solver2.check()
        print(f"Can \\exclude A be true at any world? {result2}")
        
        if result2 == z3.sat:
            model2 = solver2.model()
            world_val2 = model2.eval(world).as_long()
            print(f"\\exclude A is true at world = {bin(world_val2)}")
            
            # Check if A is true at this world
            a_true_at_world = (world_val2 & 0b001) != 0
            print(f"Is A true at this world? {a_true_at_world}")
            
        # Check if the three-condition semantics is too restrictive
        print("\n=== STEP 7: EXAMINE THREE CONDITIONS ===")
        print("The issue might be in how the three conditions interact...")
        print("Condition 3 requires the evaluation world to be the fusion of h_sk values")
        print("This might force A to be true whenever \\exclude A is true")
        
        # Let's manually check a specific case
        print("\nManual check for world = 0b110 (no 'a' bit):")
        solver3 = z3.Solver()
        solver3.add(world == 0b110)
        solver3.add(exclude_a_true)
        result3 = solver3.check()
        print(f"Can \\exclude A be true at 0b110? {result3}")
        
        if result3 == z3.unsat:
            print("No - the three conditions prevent \\exclude A from being true here")
            print("\nThis suggests the three-condition semantics might be forcing")
            print("\\exclude A to only be true at worlds where A is also true,")
            print("which would explain why there's no countermodel.")

if __name__ == "__main__":
    analyze_neg_to_sent()