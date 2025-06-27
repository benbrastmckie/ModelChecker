#!/usr/bin/env python3
"""
Test a comprehensive Skolemization approach.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import Syntax, ModelConstraints

def analyze_formulas():
    """Analyze the formulas at each stage."""
    print("COMPREHENSIVE FORMULA ANALYSIS")
    print("="*60)
    
    premises, conclusions, settings = TN_ENTAIL_example
    
    # Create semantics with Skolemization enabled
    semantics = ExclusionSemantics(settings)
    semantics.use_skolem_for_atoms = True
    
    # SK2 operators
    sk2_operators = create_operator_collection("SK2")
    
    # Create syntax
    syntax = Syntax(premises, conclusions, sk2_operators)
    
    print(f"Premise: {premises[0]}")
    print(f"Conclusion: {conclusions[0]}")
    
    # Analyze constraint generation
    print("\n1. CONSTRAINT GENERATION PHASE:")
    print("-"*40)
    
    # Create constraints
    constraints = ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    
    # Check what constraints were generated
    print(f"Number of premise constraints: {len(constraints.premise_constraints)}")
    
    # Get the premise constraint formula
    if constraints.premise_constraints:
        premise_constraint = constraints.premise_constraints[0]
        constraint_str = str(premise_constraint)
        print(f"\nPremise constraint analysis:")
        print(f"  Contains 'f_atom': {'f_atom' in constraint_str}")
        print(f"  Contains 'h_sk2': {'h_sk2' in constraint_str}")
        print(f"  Contains 'Exists': {'Exists' in constraint_str}")
        print(f"  Length: {len(constraint_str)}")
    
    # Create structure and solve
    print("\n2. SOLVING PHASE:")
    print("-"*40)
    
    structure = ExclusionStructure(constraints, settings)
    
    print(f"Model found: {structure.z3_model is not None}")
    
    if structure.z3_model:
        # Check what's in the model
        print("\nModel declarations:")
        for decl in structure.z3_model.decls():
            name = str(decl)
            if 'atom' in name or 'sk2' in name or 'main' in name:
                print(f"  {name}")
        
        # Interpret sentences
        structure.interpret(syntax.premises)
        structure.interpret(syntax.conclusions)
        
        # Now analyze evaluation
        print("\n3. EVALUATION PHASE:")
        print("-"*40)
        
        eval_point = {"world": semantics.main_world}
        
        # Get the premise
        premise_sent = syntax.premises[0]
        
        if premise_sent.proposition:
            # Get the evaluation formula
            eval_formula = semantics.true_at(premise_sent, eval_point)
            eval_str = str(eval_formula)
            
            print(f"Evaluation formula analysis:")
            print(f"  Contains 'f_atom': {'f_atom' in eval_str}")
            print(f"  Contains 'h_sk2': {'h_sk2' in eval_str}")
            print(f"  Contains 'Exists': {'Exists' in eval_str}")
            print(f"  Length: {len(eval_str)}")
            
            # Evaluate it
            result = structure.z3_model.evaluate(eval_formula)
            print(f"\nEvaluation result: {z3.is_true(result)}")
            
            # Try to understand why it's false
            if not z3.is_true(result):
                print("\nDiagnosing false evaluation...")
                
                # The issue might be that the Skolem functions in constraints
                # are different from those in evaluation
                
                # Check if the main world verifies anything
                main_world_val = structure.z3_model.eval(semantics.main_world)
                print(f"Main world value: {main_world_val}")
                
                # Check atomic sentence A directly
                A = syntax.sentence_letters[0]
                
                # Create a fresh formula for A being true at main world
                fresh_eval_point = {"world": main_world_val}
                A_formula = semantics.true_at(A, fresh_eval_point)
                A_result = structure.z3_model.evaluate(A_formula)
                print(f"A true at main world: {z3.is_true(A_result)}")

if __name__ == "__main__":
    analyze_formulas()