#!/usr/bin/env python3
"""
Debug whether Skolemization is actually being used in true_at.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.syntactic import Syntax
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics
from model_checker.theory_lib.exclusion.operators import create_operator_collection

def test_skolem_usage():
    """Test if Skolemization is being used."""
    print("TESTING SKOLEMIZATION USAGE")
    print("="*60)
    
    # Simple atomic sentence
    settings = {'N': 3}
    semantics = ExclusionSemantics(settings)
    
    # Enable Skolemization
    semantics.use_skolem_for_atoms = True
    print(f"Skolemization enabled: {hasattr(semantics, 'use_skolem_for_atoms') and semantics.use_skolem_for_atoms}")
    
    # Create a simple atomic sentence
    syntax = Syntax(['A'], [], create_operator_collection('MS'))
    A = syntax.sentence_letters[0]
    
    # Test true_at with atomic sentence
    eval_point = {"world": z3.BitVecVal(1, 3)}
    
    print("\nTesting true_at on atomic sentence 'A':")
    print("-"*40)
    
    # Get the formula
    formula = semantics.true_at(A, eval_point)
    formula_str = str(formula)
    
    print(f"Formula type: {type(formula)}")
    print(f"Contains 'f_atom': {'f_atom' in formula_str}")
    print(f"Contains 'Exists': {'Exists' in formula_str}")
    print(f"Formula length: {len(formula_str)}")
    
    # Check the structure
    if z3.is_and(formula):
        print("\nFormula is an And (Skolemized):")
        for i, child in enumerate(formula.children()):
            print(f"  Child {i}: {type(child).__name__}")
    elif z3.is_or(formula):
        print("\nFormula is an Or (expanded Exists):")
        print(f"  Number of disjuncts: {len(formula.children())}")
    
    # Now test with exclusion
    print("\n\nTesting with exclusion operator:")
    print("-"*40)
    
    # Create \\exclude A
    exclude_syntax = Syntax(['\\exclude A'], [], create_operator_collection('SK2'))
    exclude_A = exclude_syntax.premises[0]
    
    # Test true_at
    exclude_formula = semantics.true_at(exclude_A, eval_point)
    exclude_str = str(exclude_formula)
    
    print(f"Exclusion formula contains 'f_atom': {'f_atom' in exclude_str}")
    print(f"Exclusion formula contains 'h_sk2': {'h_sk2' in exclude_str}")
    
    # Disable Skolemization and compare
    print("\n\nComparing with Skolemization disabled:")
    print("-"*40)
    
    semantics.use_skolem_for_atoms = False
    
    formula_no_skolem = semantics.true_at(A, eval_point)
    no_skolem_str = str(formula_no_skolem)
    
    print(f"Without Skolem - Contains 'f_atom': {'f_atom' in no_skolem_str}")
    print(f"Without Skolem - Contains 'Exists': {'Exists' in no_skolem_str}")
    print(f"Without Skolem - Formula length: {len(no_skolem_str)}")
    
    print("\nConclusion:")
    if 'f_atom' in formula_str and 'f_atom' not in no_skolem_str:
        print("✓ Skolemization IS being used when enabled")
    else:
        print("✗ Skolemization is NOT being used properly")

if __name__ == "__main__":
    test_skolem_usage()