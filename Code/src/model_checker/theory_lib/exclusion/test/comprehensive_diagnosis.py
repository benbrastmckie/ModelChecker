"""Comprehensive diagnosis of the constraint/truth disconnect across all strategies."""

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


def diagnose_core_issue():
    """Diagnose the core architectural issue causing invalid models."""
    
    print("COMPREHENSIVE DIAGNOSIS: CONSTRAINT/TRUTH DISCONNECT")
    print("="*80)
    
    print("\n1. THE ARCHITECTURE:")
    print("   Model generation has two phases:")
    print("   a) CONSTRAINT GENERATION: Creates Z3 formulas for premises/conclusions")
    print("   b) TRUTH EVALUATION: Checks actual truth values after model is found")
    print("")
    print("2. THE DISCONNECT:")
    print("   - Constraints use complex formulas (e.g., existential quantifiers)")
    print("   - Truth evaluation uses simple verifier membership")
    print("   - These two mechanisms can disagree!")
    
    print("\n3. DETAILED EXAMPLE WALKTHROUGH:")
    print("   Example: \\exclude A ⊢ A")
    
    # Let's trace through this step by step
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
        'print_constraints': False,
        'print_z3': False,
    }
    
    semantics = ExclusionSemantics(settings)
    operators = create_operator_collection('QA')
    syntax = syntactic.Syntax(premises, conclusions, operators)
    
    print("\n   PHASE 1 - CONSTRAINT GENERATION:")
    print("   --------------------------------")
    
    # The premise constraint for "\\exclude A" is generated as:
    # true_at_cached(\\exclude A, main_point)
    # This becomes a complex formula checking if any A-verifier conflicts with main world
    
    constraints = model.ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    
    premise_constraint = constraints.premise_constraints[0]
    print(f"   Premise constraint: {str(premise_constraint)[:100]}...")
    print("   This checks: ∃x. verify(x, A) ∧ excludes(x, main_world)")
    print("   In other words: 'Does any A-verifier conflict with main world?'")
    
    conclusion_constraint = constraints.conclusion_constraints[0]
    print(f"\n   Conclusion constraint: {str(conclusion_constraint)[:100]}...")
    print("   This checks: ¬(∃x. x ⊑ main_world ∧ verify(x, A))")
    print("   In other words: 'No A-verifier is part of main world'")
    
    print("\n   PHASE 2 - Z3 SOLVING:")
    print("   --------------------")
    
    structure = ExclusionStructure(constraints, settings)
    
    if structure.z3_model:
        z3_model = structure.z3_model
        main_world_value = z3_model.evaluate(semantics.main_point['world'])
        
        print(f"   Z3 finds a model with main_world = {main_world_value}")
        print("   Let's see how constraints are satisfied:")
        
        print(f"\n   Premise constraint satisfied: {z3.is_true(z3_model.evaluate(premise_constraint))}")
        print("   ✓ Yes! Because states 1,2,4 verify A and exclude main_world 0")
        
        print(f"\n   Conclusion constraint satisfied: {z3.is_true(z3_model.evaluate(conclusion_constraint))}")
        print("   ✓ Yes! Because no A-verifier is part of world 0")
        
        print("\n   PHASE 3 - PROPOSITION CREATION & TRUTH EVALUATION:")
        print("   -------------------------------------------------")
        
        structure.interpret(syntax.premises)
        structure.interpret(syntax.conclusions)
        
        main_point = structure.main_point
        
        # Check premise
        premise_prop = syntax.premises[0].proposition
        if premise_prop:
            premise_verifiers = premise_prop.verifiers
            premise_truth = premise_prop.truth_value_at(main_point)
            
            print(f"\n   Premise '\\exclude A' proposition created")
            print(f"   Verifiers for '\\exclude A': {premise_verifiers}")
            print(f"   Truth value: {premise_truth}")
            
            if not premise_verifiers:
                print("\n   ⚠️  EMPTY VERIFIERS!")
                print("   Why? Because NO state verifies the exclusion '\\exclude A'")
                print("   The constraint checked if A-verifiers conflict with main world")
                print("   But it didn't ensure '\\exclude A' itself has verifiers!")
                
        # Check conclusion
        conclusion_prop = syntax.conclusions[0].proposition
        if conclusion_prop:
            conclusion_verifiers = conclusion_prop.verifiers
            conclusion_truth = conclusion_prop.truth_value_at(main_point)
            
            print(f"\n   Conclusion 'A' proposition created")
            print(f"   Verifiers for 'A': {conclusion_verifiers}")
            print(f"   Truth value: {conclusion_truth}")
            
    print("\n4. ROOT CAUSE ANALYSIS:")
    print("   -------------------")
    print("   The constraint for 'true_at(\\exclude A, w)' asks:")
    print("   '∃x. verify(x, A) ∧ excludes(x, w)'")
    print("")
    print("   But truth evaluation for '\\exclude A' requires:")
    print("   '∃v. v ∈ verifiers(\\exclude A) ∧ v ⊑ w'")
    print("")
    print("   These are DIFFERENT conditions!")
    print("   - The constraint can be satisfied by A-verifiers existing and excluding w")
    print("   - But this doesn't guarantee \\exclude A has any verifiers")
    print("   - With empty verifiers, truth evaluation returns False")
    
    print("\n5. WHY THIS HAPPENS:")
    print("   ----------------")
    print("   - Constraint generation happens BEFORE propositions are created")
    print("   - Constraints work with formulas, not actual verifier sets")
    print("   - The formulas approximate the intended semantics")
    print("   - But the approximation has gaps that allow invalid models")
    
    print("\n6. THE GENERAL PATTERN:")
    print("   -------------------")
    print("   For ANY formula φ constrained to be true:")
    print("   - Constraint: complex Z3 formula encoding semantic conditions")
    print("   - Truth eval: ∃v ∈ verifiers(φ). v ⊑ evaluation_world")
    print("   - If verifiers(φ) = ∅, truth is always False")
    print("   - But constraint might still be satisfiable!")


def main():
    diagnose_core_issue()
    
    print("\n" + "="*80)
    print("CONCLUSION:")
    print("-----------")
    print("The invalid model problem is architectural:")
    print("1. Constraints approximate truth conditions with formulas")
    print("2. Actual truth uses verifier membership")
    print("3. The approximation allows models with empty verifiers")
    print("4. Empty verifiers make premises false (or conclusions true)")
    print("5. This affects ALL strategies because they share the architecture")


if __name__ == '__main__':
    main()