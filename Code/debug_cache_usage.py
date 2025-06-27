#!/usr/bin/env python3
"""
Debug Skolem function cache usage.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import Syntax, ModelConstraints

def debug_cache():
    """Debug the Skolem function cache."""
    print("DEBUGGING SKOLEM FUNCTION CACHE")
    print("="*60)
    
    premises, conclusions, settings = TN_ENTAIL_example
    
    # Create semantics
    semantics = ExclusionSemantics(settings)
    
    # SK2 operators
    sk2_operators = create_operator_collection("SK2")
    
    # Create syntax
    syntax = Syntax(premises, conclusions, sk2_operators)
    
    print(f"Initial cache: {semantics.atom_skolem_cache}")
    
    # Create constraints - this should populate the cache
    constraints = ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    
    print(f"\nAfter constraints:")
    print(f"  Cache: {list(semantics.atom_skolem_cache.keys())}")
    print(f"  Counter: {semantics.atom_skolem_counter}")
    
    # Check what constraints were generated
    if constraints.premise_constraints:
        constraint_str = str(constraints.premise_constraints[0])
        print(f"\nConstraint contains 'f_atom': {'f_atom' in constraint_str}")
        
        # Count occurrences
        for key in semantics.atom_skolem_cache:
            func_name = str(semantics.atom_skolem_cache[key])
            count = constraint_str.count(func_name)
            print(f"  {func_name} appears {count} times in constraint")
    
    # Create structure
    structure = ExclusionStructure(constraints, settings)
    
    if structure.z3_model:
        print("\nModel found!")
        
        # Check Skolem functions in model
        print("\nSkolem functions in Z3 model:")
        for decl in structure.z3_model.decls():
            if 'f_atom' in str(decl):
                print(f"  {decl}")
        
        # Interpret sentences
        structure.interpret(syntax.premises)
        
        # Now test evaluation
        print("\n\nEvaluating premise:")
        premise = syntax.premises[0]
        
        if premise.proposition:
            # Get the semantics from the structure
            eval_semantics = structure.semantics
            
            print(f"Evaluation semantics cache: {list(eval_semantics.atom_skolem_cache.keys())}")
            print(f"Same semantics object: {eval_semantics is semantics}")
            
            # Evaluate
            eval_point = {"world": eval_semantics.main_world}
            
            # Manually trace through the evaluation
            print("\nManual evaluation trace:")
            
            # The premise is \\exclude \\exclude \\exclude A
            # So we need to check if there's a state that verifies this
            # and is part of the main world
            
            # Get A
            A = syntax.sentence_letters[0]
            print(f"Atomic sentence A: {A}")
            print(f"A cache key: {str(A.sentence_letter)}")
            
            # Check if A's Skolem function is in cache
            A_key = str(A.sentence_letter)
            if A_key in eval_semantics.atom_skolem_cache:
                print(f"A's Skolem function IS in cache: {eval_semantics.atom_skolem_cache[A_key]}")
            else:
                print("A's Skolem function NOT in cache!")
            
            # Evaluate the premise
            result = premise.proposition.truth_value_at(eval_point)
            print(f"\nFinal evaluation result: {result}")

if __name__ == "__main__":
    debug_cache()