#!/usr/bin/env python3
"""
Test false premise issues using the standard model checking flow.
"""

import sys
import os
sys.path.insert(0, 'src')

from model_checker.syntactic import Syntax
from model_checker.model import ModelConstraints
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import exclusion_operators

def test_example(name, premises, conclusions):
    """Test an example and analyze false premise issues."""
    print(f"\n{'='*70}")
    print(f"TESTING: {name}")
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
        'expectation': False,
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
    
    # Create model structure - this will solve and build the model
    try:
        model_structure = ExclusionStructure(model_constraints, settings)
    except Exception as e:
        print(f"Error creating model structure: {e}")
        return
    
    # Check if we found a countermodel
    if not model_structure.z3_model_status:
        print("NO COUNTERMODEL FOUND (Theorem)")
        return
        
    print("COUNTERMODEL FOUND")
    
    # Get the Z3 model
    z3_model = model_structure.z3_model
    main_point = model_structure.main_point
    
    # Analyze Z3 model functions
    print("\n=== Z3 MODEL FUNCTIONS ===")
    h_functions = []
    for decl in z3_model.decls():
        if 'h_ms_' in str(decl):
            h_functions.append(decl)
    print(f"Found {len(h_functions)} exclusion functions")
    
    # Test premise evaluation
    print("\n=== PREMISE EVALUATION ===")
    for i, premise_sent in enumerate(model_structure.premises):
        print(f"\nPremise {i}: {premises[i]}")
        
        # Get the proposition from the sentence
        premise_prop = premise_sent.proposition
        if premise_prop is None:
            print("  ERROR: No proposition found")
            continue
            
        truth_val = premise_prop.truth_value_at(main_point)
        print(f"  Evaluates to: {truth_val}")
        
        if not truth_val:
            print("  *** FALSE PREMISE DETECTED ***")
            
            # Analyze the formula
            formula = semantics.true_at(premise_sent, main_point)
            print(f"  Formula type: {type(formula).__name__}")
            
            # Check for nested exclusions
            exclusion_count = premises[i].count('\\exclude')
            print(f"  Number of exclusions: {exclusion_count}")
            
            # Check for existential quantifiers in formula string
            formula_str = str(formula)
            if 'Exists' in formula_str:
                exists_count = formula_str.count('Exists')
                print(f"  Existential quantifiers found: {exists_count}")
                print("\n  DIAGNOSIS: The false premise is caused by existential quantifiers")
                print("  in the exclusion operator. Z3 can prove 'exists h' during solving")
                print("  but cannot provide the specific h during evaluation.")
    
    # Display the full model
    print("\n=== MODEL DISPLAY ===")
    model_structure.display()
    
    # Additional analysis for MS strategy
    print("\n=== MS STRATEGY ANALYSIS ===")
    print("The MS (Multi-Sort) strategy is currently being used.")
    print("It creates typed exclusion functions (h_ms_N) but still uses")
    print("existential quantification, which causes the false premise issue.")

def main():
    """Test key examples."""
    
    # Test Triple Negation
    test_example(
        "Triple Negation Entailment",
        ['\\exclude \\exclude \\exclude A'],
        ['\\exclude A']
    )
    
    # Test Disjunctive DeMorgan's RL
    test_example(
        "Disjunctive DeMorgan's RL",
        ['(\\exclude A \\uniwedge \\exclude B)'],
        ['\\exclude (A \\univee B)']
    )
    
    # Test a working example
    test_example(
        "Simple Exclusion",
        ['\\exclude A'],
        ['\\exclude \\exclude \\exclude A']
    )

if __name__ == "__main__":
    main()