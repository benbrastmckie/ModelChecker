#!/usr/bin/env python3
"""
Script to investigate false premise issues in exclusion theory.
Focuses on understanding Z3 constraints and model details.
"""

import sys
import os
sys.path.insert(0, 'src')

from model_checker.builder import BuildModule
from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example, DISJ_DM_RL_example
import z3

def analyze_example(example_data, example_name):
    """Analyze an example with detailed Z3 output."""
    print(f"\n{'='*60}")
    print(f"ANALYZING: {example_name}")
    print(f"{'='*60}\n")
    
    premises, conclusions, settings = example_data
    print(f"Premises: {premises}")
    print(f"Conclusions: {conclusions}")
    print(f"Settings: {settings}\n")
    
    # Create build module for exclusion theory
    from model_checker.theory_lib import exclusion
    build_module = BuildModule(exclusion)
    
    # Get semantic theory
    semantic_theory = build_module.semantic_theories['exclusion']
    
    # Create builder for this example
    builder = build_module.theory_builder(semantic_theory, example_data)
    
    # Access the model constraints before building
    model_constraints = builder.model_constraints
    semantics = model_constraints.semantics
    
    print("\n=== PREMISE CONSTRAINTS ===")
    for i, premise_constraint in enumerate(model_constraints.premise_constraints):
        print(f"\nPremise {i} constraint:")
        print(f"  Formula: {premise_constraint}")
        print(f"  Type: {type(premise_constraint)}")
        
    print("\n=== CONCLUSION CONSTRAINTS ===")
    for i, conclusion_constraint in enumerate(model_constraints.conclusion_constraints):
        print(f"\nConclusion {i} constraint:")
        print(f"  Formula: {conclusion_constraint}")
        print(f"  Type: {type(conclusion_constraint)}")
    
    # Build the model
    result = builder.build()
    
    if result == 'theorem':
        print("\nResult: THEOREM (no countermodel found)")
        return
    
    print(f"\nResult: COUNTERMODEL FOUND")
    
    # Get Z3 model
    z3_model = builder.result_structure.z3_model
    
    print("\n=== Z3 MODEL DECLARATIONS ===")
    for decl in z3_model.decls():
        print(f"  {decl.name()}: {decl}")
        if decl.name().startswith('h_') or decl.name() == 'h':
            print(f"    -> Function declaration for exclusion operator")
    
    # Test premise evaluation
    print("\n=== PREMISE EVALUATION ===")
    for i, premise in enumerate(builder.result_structure.premises):
        eval_point = builder.result_structure.main_point
        
        # Get the actual constraint formula
        premise_constraint = model_constraints.premise_constraints[i]
        
        # Evaluate in model
        try:
            result = z3_model.evaluate(premise_constraint)
            print(f"\nPremise {i}: {premise.sentence}")
            print(f"  Constraint evaluates to: {result}")
            print(f"  z3.is_true(result): {z3.is_true(result)}")
            
            # Also test truth_value_at method
            truth_val = premise.truth_value_at(eval_point)
            print(f"  truth_value_at returns: {truth_val}")
            
        except Exception as e:
            print(f"  Error evaluating: {e}")
    
    # Look for function witnesses
    print("\n=== FUNCTION WITNESS SEARCH ===")
    
    # Try to extract h functions
    h_functions = {}
    for decl in z3_model.decls():
        if decl.name().startswith('h_') or decl.name() == 'h':
            h_functions[decl.name()] = decl
            print(f"Found function: {decl.name()}")
            
            # Try to evaluate function at some points
            if decl.arity() == 1:
                print(f"  Testing function evaluation:")
                for i in range(8):  # Test first 8 bit vectors
                    bv = z3.BitVecVal(i, semantics.N)
                    try:
                        val = z3_model.evaluate(decl(bv))
                        print(f"    h({i}) = {val}")
                    except:
                        print(f"    h({i}) = <error>")
    
    if not h_functions:
        print("No h functions found in model!")
    
    # Display the model
    print("\n=== MODEL DISPLAY ===")
    builder.result_structure.display()


# Analyze problematic examples
if __name__ == "__main__":
    print("INVESTIGATING FALSE PREMISE ISSUES IN EXCLUSION THEORY")
    print("="*60)
    
    # Analyze Triple Negation Entailment
    analyze_example(TN_ENTAIL_example, "Triple Negation Entailment")
    
    # Analyze Disjunctive DeMorgan's RL
    analyze_example(DISJ_DM_RL_example, "Disjunctive DeMorgan's RL")