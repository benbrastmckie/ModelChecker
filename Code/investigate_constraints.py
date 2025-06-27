#!/usr/bin/env python3
"""
Direct investigation of Z3 constraints for false premise issues.
"""

import sys
import os
sys.path.insert(0, 'src')

import z3
from model_checker.syntactic import Syntax
from model_checker.model import ModelConstraints

# Import exclusion theory components
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import exclusion_operators

def investigate_triple_negation():
    """Investigate the Triple Negation Entailment example."""
    print("\n" + "="*60)
    print("INVESTIGATING: Triple Negation Entailment")
    print("\\exclude \\exclude \\exclude A ⊨ \\exclude A")
    print("="*60 + "\n")
    
    # Example settings
    settings = {
        'N': 3,
        'possible': False,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'fusion_closure': False,
    }
    
    # Create syntax and semantics
    premises = ['\\exclude \\exclude \\exclude A']
    conclusions = ['\\exclude A']
    syntax = Syntax(premises, conclusions, exclusion_operators)
    
    # Create semantics instance
    semantics = ExclusionSemantics(settings)
    proposition = UnilateralProposition
    
    # Create model constraints
    model_constraints = ModelConstraints(
        settings,
        syntax, 
        semantics, 
        proposition
    )
    
    print("=== PREMISE CONSTRAINTS ===")
    for i, premise_constraint in enumerate(model_constraints.premise_constraints):
        print(f"\nPremise {i}: {premises[i]}")
        print(f"Constraint: {premise_constraint}")
        print(f"Type: {type(premise_constraint)}")
        
        # Try to simplify the constraint
        try:
            simplified = z3.simplify(premise_constraint)
            print(f"Simplified: {simplified}")
        except:
            pass
    
    print("\n=== CONCLUSION CONSTRAINTS ===")
    for i, conclusion_constraint in enumerate(model_constraints.conclusion_constraints):
        print(f"\nConclusion {i}: {conclusions[i]}")
        print(f"Constraint: {conclusion_constraint}")
        
    print("\n=== SOLVING ===")
    # Check if satisfiable
    if model_constraints.solver.check() == z3.sat:
        print("COUNTERMODEL FOUND!")
        
        # Get the model
        z3_model = model_constraints.solver.model()
        
        print("\n=== Z3 MODEL ===")
        print(f"Number of declarations: {len(z3_model.decls())}")
        
        # Look for function declarations
        h_functions = []
        for decl in z3_model.decls():
            print(f"  {decl.name()}: {decl}")
            if decl.name().startswith('h_') or decl.name() == 'h':
                h_functions.append(decl)
                
        print(f"\nFound {len(h_functions)} h functions")
        
        # Create model structure
        model_structure = ExclusionStructure(
            model_constraints,
            z3_model
        )
        
        print("\n=== EVALUATING PREMISE IN MODEL ===")
        main_point = model_structure.main_point
        
        # Get the premise
        premise_obj = model_structure.premises[0]
        
        # Evaluate using truth_value_at
        truth_val = premise_obj.truth_value_at(main_point)
        print(f"Premise truth_value_at: {truth_val}")
        
        # Try direct evaluation of the constraint
        premise_constraint = model_constraints.premise_constraints[0]
        eval_result = z3_model.evaluate(premise_constraint)
        print(f"Direct constraint evaluation: {eval_result}")
        print(f"z3.is_true(eval_result): {z3.is_true(eval_result)}")
        
        # Let's trace through the evaluation
        print("\n=== TRACING EVALUATION ===")
        
        # Get the formula used for evaluation
        formula = model_constraints.semantics.true_at(premise_obj.sentence, main_point)
        print(f"Formula for evaluation: {formula}")
        
        # Evaluate it
        formula_result = z3_model.evaluate(formula)
        print(f"Formula evaluates to: {formula_result}")
        
        # Display the model
        print("\n=== MODEL DISPLAY ===")
        model_structure.display()
        
    else:
        print("No countermodel found (THEOREM)")

def investigate_disjunctive_demorgan():
    """Investigate the Disjunctive DeMorgan's RL example."""
    print("\n" + "="*60)
    print("INVESTIGATING: Disjunctive DeMorgan's RL")
    print("(\\exclude A \\uniwedge \\exclude B) ⊨ \\exclude (A \\univee B)")
    print("="*60 + "\n")
    
    # Example settings
    settings = {
        'N': 3,
        'possible': False,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'fusion_closure': False,
    }
    
    # Create syntax and semantics
    premises = ['(\\exclude A \\uniwedge \\exclude B)']
    conclusions = ['\\exclude (A \\univee B)']
    syntax = Syntax(premises, conclusions, exclusion_operators)
    
    # Create semantics instance
    semantics = ExclusionSemantics(settings)
    proposition = UnilateralProposition
    
    # Create model constraints
    model_constraints = ModelConstraints(
        settings,
        syntax, 
        semantics, 
        proposition
    )
    
    print("=== SOLVING ===")
    if model_constraints.solver.check() == z3.sat:
        print("COUNTERMODEL FOUND!")
        
        z3_model = model_constraints.solver.model()
        model_structure = ExclusionStructure(
            model_constraints,
            z3_model
        )
        
        print("\n=== EVALUATING PREMISE ===")
        premise_obj = model_structure.premises[0]
        main_point = model_structure.main_point
        
        truth_val = premise_obj.truth_value_at(main_point)
        print(f"Premise truth_value_at: {truth_val}")
        
        # Display model
        print("\n=== MODEL DISPLAY ===")
        model_structure.display()
    else:
        print("No countermodel found (THEOREM)")

if __name__ == "__main__":
    investigate_triple_negation()
    investigate_disjunctive_demorgan()