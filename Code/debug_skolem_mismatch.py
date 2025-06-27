#!/usr/bin/env python3
"""
Debug why Skolemization still gives false premises.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import Syntax, ModelConstraints

def debug_skolem_mismatch():
    """Debug the mismatch between constraint and evaluation Skolem functions."""
    print("DEBUGGING SKOLEM FUNCTION MISMATCH")
    print("="*60)
    
    premises, conclusions, settings = TN_ENTAIL_example
    
    # Create two separate semantics instances to track Skolem functions
    print("1. Creating semantics for constraints...")
    semantics_constraint = ExclusionSemantics(settings)
    
    # SK2 operators
    sk2_operators = create_operator_collection("SK2")
    
    # Create syntax
    syntax = Syntax(premises, conclusions, sk2_operators)
    
    # Track Skolem counter during constraint generation
    print(f"Initial atom_skolem_counter: {semantics_constraint.atom_skolem_counter}")
    
    # Create constraints
    constraints = ModelConstraints(settings, syntax, semantics_constraint, UnilateralProposition)
    
    print(f"After constraint generation: {semantics_constraint.atom_skolem_counter}")
    
    # Create structure
    structure = ExclusionStructure(constraints, settings)
    
    if structure.z3_model:
        print("\n2. Model found - checking Skolem functions in model:")
        
        # Check what Skolem functions are in the model
        for decl in structure.z3_model.decls():
            name = str(decl)
            if 'f_atom' in name:
                print(f"  Found in model: {name}")
        
        # Interpret sentences (this creates propositions)
        structure.interpret(syntax.premises)
        
        # Now check evaluation
        print("\n3. Evaluating premise:")
        
        # The semantics used for evaluation is the one in the structure
        eval_semantics = structure.semantics
        print(f"Evaluation semantics atom_skolem_counter: {eval_semantics.atom_skolem_counter}")
        
        # Get premise
        premise = syntax.premises[0]
        
        if premise.proposition:
            # Check the counter before evaluation
            counter_before = eval_semantics.atom_skolem_counter
            
            # Evaluate
            eval_point = {"world": eval_semantics.main_world}
            result = premise.proposition.truth_value_at(eval_point)
            
            counter_after = eval_semantics.atom_skolem_counter
            
            print(f"\nEvaluation result: {result}")
            print(f"Counter before evaluation: {counter_before}")
            print(f"Counter after evaluation: {counter_after}")
            print(f"New Skolem functions created during evaluation: {counter_after - counter_before}")
            
            # The problem is likely that evaluation creates NEW Skolem functions
            # that weren't part of the constraint solving
            
            print("\n4. Analyzing the issue:")
            print("-"*40)
            print("The problem is that constraint generation and evaluation")
            print("create DIFFERENT Skolem functions (f_atom_1 vs f_atom_2, etc.)")
            print("Z3 can't find values for the evaluation functions because")
            print("they weren't part of the constraint solving process.")
            
            # Try to understand what's happening with a simple atomic sentence
            print("\n5. Testing atomic sentence directly:")
            A = syntax.sentence_letters[0]
            
            # Get the constraint formula
            constraint_formula = eval_semantics.true_at(A, eval_point)
            print(f"\nAtomic constraint formula contains f_atom_{eval_semantics.atom_skolem_counter}")
            
            # Check if this can be satisfied
            test_result = structure.z3_model.evaluate(constraint_formula)
            print(f"Can satisfy atomic formula: {z3.is_true(test_result)}")

if __name__ == "__main__":
    debug_skolem_mismatch()