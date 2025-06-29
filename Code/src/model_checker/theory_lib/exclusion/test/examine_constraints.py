"""Examine the actual Z3 constraints generated for premises and conclusions."""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../../..'))

from model_checker.theory_lib.exclusion import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import model, syntactic
import z3


def examine_constraints_simple():
    """Examine constraints for a simple atomic example."""
    
    print("EXAMINING CONSTRAINTS FOR SIMPLE ATOMIC CASE")
    print("="*60)
    
    # Use the simplest possible case - just atomic A
    premises = ["A"]
    conclusions = ["\\exclude A"]
    
    settings = {
        'N': 3,
        'possible': False,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'fusion_closure': False,
        'max_time': 5,
        'expectation': False,
        'exclusion_strategy': 'QA',
        'print_constraints': False,
        'print_z3': False,
    }
    
    # Create components
    semantics = ExclusionSemantics(settings)
    operators = create_operator_collection('QA')
    syntax = syntactic.Syntax(premises, conclusions, operators)
    
    print(f"\nMain point: {semantics.main_point}")
    print(f"Main world symbol: {semantics.main_point['world']}")
    
    # Look at the verify function for atomic A
    print("\n1. ATOMIC PROPOSITION HANDLING:")
    print(f"Sentence letters: {syntax.sentence_letters}")
    
    # Create constraints but don't solve yet
    constraints = model.ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    
    print("\n2. EXAMINING PREMISE CONSTRAINTS:")
    print(f"Number of premise constraints: {len(constraints.premise_constraints)}")
    if constraints.premise_constraints:
        premise_constraint = constraints.premise_constraints[0]
        print(f"Premise constraint: {premise_constraint}")
        print(f"Simplified: {z3.simplify(premise_constraint)}")
        
    print("\n3. EXAMINING CONCLUSION CONSTRAINTS:")
    print(f"Number of conclusion constraints: {len(constraints.conclusion_constraints)}")
    if constraints.conclusion_constraints:
        conclusion_constraint = constraints.conclusion_constraints[0]
        print(f"Conclusion constraint: {conclusion_constraint}")
        print(f"Simplified: {z3.simplify(conclusion_constraint)}")
        
    # Now solve and see what happens
    print("\n4. SOLVING THE MODEL:")
    structure = ExclusionStructure(constraints, settings)
    
    if structure.z3_model:
        print("Model found!")
        z3_model = structure.z3_model
        
        # Check constraint satisfaction
        print("\n5. CONSTRAINT SATISFACTION:")
        if constraints.premise_constraints:
            eval_result = z3_model.evaluate(constraints.premise_constraints[0])
            print(f"Premise constraint evaluates to: {eval_result}")
            
        if constraints.conclusion_constraints:
            eval_result = z3_model.evaluate(constraints.conclusion_constraints[0])
            print(f"Conclusion constraint evaluates to: {eval_result}")
            
        # Now check actual truth after interpretation
        structure.interpret(syntax.premises)
        structure.interpret(syntax.conclusions)
        
        main_point = structure.main_point
        
        print("\n6. ACTUAL TRUTH VALUES:")
        for i, premise in enumerate(syntax.premises):
            if premise.proposition:
                truth = premise.proposition.truth_value_at(main_point)
                verifiers = premise.proposition.verifiers
                print(f"Premise {i} truth: {truth}, verifiers: {verifiers}")
                
        for i, conclusion in enumerate(syntax.conclusions):
            if conclusion.proposition:
                truth = conclusion.proposition.truth_value_at(main_point)
                verifiers = conclusion.proposition.verifiers
                print(f"Conclusion {i} truth: {truth}, verifiers: {verifiers}")
                
        # Look at the verify function in the model
        print("\n7. EXAMINING VERIFY FUNCTION:")
        for decl in z3_model.decls():
            if 'verify' in str(decl).lower():
                print(f"{decl}: {z3_model[decl]}")
                
    else:
        print("No model found")


def examine_exclusion_case():
    """Examine constraints for exclusion case that fails."""
    
    print("\n\nEXAMINING CONSTRAINTS FOR EXCLUSION CASE")
    print("="*60)
    
    premises = ["\\exclude A"]
    conclusions = ["A"]
    
    settings = {
        'N': 3,
        'possible': False,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'fusion_closure': False,
        'max_time': 5,
        'expectation': False,
        'exclusion_strategy': 'QA',
        'print_constraints': False,  # Turn off for now
        'print_z3': False,
    }
    
    print("\nThis will show all generated constraints...")
    
    # Create components
    semantics = ExclusionSemantics(settings)
    operators = create_operator_collection('QA')
    syntax = syntactic.Syntax(premises, conclusions, operators)
    
    # Create constraints - this will print them
    constraints = model.ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    
    print("\n[Constraints printed above]")
    
    # Now solve
    structure = ExclusionStructure(constraints, settings)
    
    if structure.z3_model:
        print("\nMODEL FOUND - checking validity...")
        
        structure.interpret(syntax.premises)
        structure.interpret(syntax.conclusions)
        
        main_point = structure.main_point
        
        print("\nTRUTH VALUES:")
        for i, premise in enumerate(syntax.premises):
            if premise.proposition:
                truth = premise.proposition.truth_value_at(main_point)
                verifiers = premise.proposition.verifiers
                print(f"Premise '{premises[i]}' truth: {truth}, verifiers: {verifiers}")
                if not truth:
                    print("  ⚠️  FALSE PREMISE!")
                
        for i, conclusion in enumerate(syntax.conclusions):
            if conclusion.proposition:
                truth = conclusion.proposition.truth_value_at(main_point)
                verifiers = conclusion.proposition.verifiers
                print(f"Conclusion '{conclusions[i]}' truth: {truth}, verifiers: {verifiers}")
                if truth:
                    print("  ⚠️  TRUE CONCLUSION!")


def main():
    examine_constraints_simple()
    examine_exclusion_case()


if __name__ == '__main__':
    main()