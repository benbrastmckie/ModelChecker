#!/usr/bin/env python3
"""
Analyze false premise issues by examining Z3 constraints and models directly.
"""

import sys
import os
sys.path.insert(0, 'src')

import z3
from model_checker.syntactic import Syntax
from model_checker.model import ModelConstraints, ModelDefaults
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import exclusion_operators

def analyze_example(name, premises, conclusions):
    """Analyze an example to understand false premise issues."""
    print(f"\n{'='*70}")
    print(f"ANALYZING: {name}")
    print(f"Premises: {premises}")
    print(f"Conclusions: {conclusions}")
    print(f"{'='*70}\n")
    
    # Settings
    settings = {
        'N': 3,
        'possible': False,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'fusion_closure': False,
        'max_time': 10,
        'expectation': False,  # Expecting countermodel
    }
    
    # Create components
    syntax = Syntax(premises, conclusions, exclusion_operators)
    semantics = ExclusionSemantics(settings)
    
    # Create model constraints
    model_constraints = ModelConstraints(
        settings,
        syntax,
        semantics,
        UnilateralProposition
    )
    
    # Create model defaults with constraints and settings
    model_defaults = ModelDefaults(model_constraints, settings)
    
    # The solve method is called in __init__, so check the results
    if model_defaults.timeout:
        print("TIMEOUT during solving")
        return
        
    if not model_defaults.z3_model_status:
        print("NO COUNTERMODEL FOUND (Theorem)")
        return
        
    is_sat = model_defaults.z3_model_status
    z3_model = model_defaults.z3_model
    
    if not is_sat:
        print("NO COUNTERMODEL FOUND (Theorem)")
        return
        
    print("COUNTERMODEL FOUND")
    
    # Analyze Z3 model
    print("\n=== Z3 MODEL ANALYSIS ===")
    print(f"Model has {len(z3_model.decls())} declarations")
    
    # Look for exclusion functions
    h_functions = []
    for decl in z3_model.decls():
        if 'h_ms_' in decl.name() or decl.name() == 'h':
            h_functions.append(decl)
            print(f"Found exclusion function: {decl.name()}")
    
    print(f"\nTotal exclusion functions: {len(h_functions)}")
    
    # Create model structure for evaluation
    model_structure = ExclusionStructure(model_constraints, z3_model)
    main_point = model_structure.main_point
    
    print(f"\nMain evaluation point: {main_point}")
    
    # Analyze premise evaluation
    print("\n=== PREMISE EVALUATION ANALYSIS ===")
    
    for i, premise_obj in enumerate(model_structure.premises):
        print(f"\nPremise {i}: {premises[i]}")
        
        # Method 1: Using truth_value_at
        truth_val = premise_obj.truth_value_at(main_point)
        print(f"  truth_value_at returns: {truth_val}")
        
        # Method 2: Direct constraint evaluation
        premise_constraint = model_constraints.premise_constraints[i]
        eval_result = z3_model.evaluate(premise_constraint)
        print(f"  Direct constraint evaluation: {eval_result}")
        print(f"  z3.is_true(eval_result): {z3.is_true(eval_result)}")
        
        # Method 3: Using semantics.true_at
        formula = semantics.true_at(premise_obj.sentence, main_point)
        formula_eval = z3_model.evaluate(formula)
        print(f"  semantics.true_at formula evaluation: {formula_eval}")
        
        # If premise is false, let's investigate why
        if not truth_val:
            print("\n  FALSE PREMISE DETECTED - Investigating...")
            
            # Check if this is an exclusion formula
            if premises[i].startswith('\\exclude'):
                print("  This is an exclusion formula")
                
                # Count nested exclusions
                exclusion_count = premises[i].count('\\exclude')
                print(f"  Number of nested exclusions: {exclusion_count}")
                
                # Look at the formula structure
                print(f"  Formula type: {type(formula)}")
                if hasattr(formula, 'children'):
                    print(f"  Formula has {len(formula.children())} children")
                
                # Check for existential quantifiers
                formula_str = str(formula)
                exists_count = formula_str.count('Exists')
                print(f"  Number of existential quantifiers: {exists_count}")
                
                # Try to understand why evaluation fails
                if exists_count > 0:
                    print("\n  DIAGNOSIS: Existential quantifier issue detected")
                    print("  Z3 can prove 'exists h such that P(h)' during solving")
                    print("  But cannot provide the specific h during evaluation")
                    print("  This is the core false premise problem")
    
    # Display the model
    print("\n=== MODEL DISPLAY ===")
    model_structure.display()

def main():
    """Analyze the key problematic examples."""
    
    # Triple Negation Entailment
    analyze_example(
        "Triple Negation Entailment",
        ['\\exclude \\exclude \\exclude A'],
        ['\\exclude A']
    )
    
    # Disjunctive DeMorgan's RL
    analyze_example(
        "Disjunctive DeMorgan's RL",
        ['(\\exclude A \\uniwedge \\exclude B)'],
        ['\\exclude (A \\univee B)']
    )
    
    # Working example for comparison
    analyze_example(
        "Conjunctive DeMorgan's RL (Working)",
        ['(\\exclude A \\univee \\exclude B)'],
        ['\\exclude (A \\uniwedge B)']
    )

if __name__ == "__main__":
    main()