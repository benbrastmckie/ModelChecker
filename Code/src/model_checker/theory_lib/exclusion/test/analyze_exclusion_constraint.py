"""Analyze how exclusion operator constraints work."""

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


def analyze_exclusion_constraint():
    """Analyze the constraint for \\exclude A."""
    
    print("ANALYZING EXCLUSION CONSTRAINT")
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
        'print_constraints': False,
        'print_z3': False,
    }
    
    # Create components
    semantics = ExclusionSemantics(settings)
    operators = create_operator_collection('QA')
    syntax = syntactic.Syntax(premises, conclusions, operators)
    
    print(f"\nMain evaluation point: {semantics.main_point}")
    
    # Let's manually trace what the constraint should be for \\exclude A
    print("\n1. MANUAL CONSTRAINT CONSTRUCTION:")
    print("For '\\exclude A' to be true at main_point:")
    print("- We need the exclusion operator applied to A")
    print("- This uses the cached formula from formula_registry")
    
    # Get the premise sentence
    premise_sentence = syntax.premises[0]
    print(f"\nPremise sentence: {premise_sentence}")
    print(f"Operator: {premise_sentence.operator}")
    print(f"Arguments: {premise_sentence.arguments}")
    
    # Now generate the constraint
    print("\n2. GENERATING PREMISE CONSTRAINT:")
    
    # This is what happens: semantics.premise_behavior(premise)
    # which calls: semantics.true_at_cached(premise, semantics.main_point)
    
    # Let me trace through the formula registry
    print("\nFormula registry state:")
    print(f"Use formula registry: {semantics.use_formula_registry}")
    
    # Create model constraints to trigger constraint generation
    constraints = model.ModelConstraints(settings, syntax, semantics, UnilateralProposition)
    
    print("\n3. CONSTRAINT DETAILS:")
    print(f"Premise constraints: {len(constraints.premise_constraints)}")
    if constraints.premise_constraints:
        pc = constraints.premise_constraints[0]
        print(f"\nRaw constraint: {pc}")
        
        # Try to understand the structure
        if hasattr(pc, 'children'):
            print(f"Constraint children: {pc.children()}")
            
    print("\n4. SOLVING AND CHECKING:")
    structure = ExclusionStructure(constraints, settings)
    
    if structure.z3_model:
        print("Model found!")
        z3_model = structure.z3_model
        
        # Check how the premise constraint evaluates
        if constraints.premise_constraints:
            eval_result = z3_model.evaluate(constraints.premise_constraints[0])
            print(f"\nPremise constraint evaluates to: {eval_result}")
            
        # Look for exclusion-related assignments
        print("\n5. EXCLUSION-RELATED ASSIGNMENTS:")
        for decl in z3_model.decls():
            name = str(decl)
            if 'exclude' in name.lower() or 'excl' in name.lower() or 'f_' in name:
                print(f"{decl}: {z3_model[decl]}")
                
        # Now interpret and check truth
        structure.interpret(syntax.premises)
        structure.interpret(syntax.conclusions)
        
        main_point = structure.main_point
        premise_prop = syntax.premises[0].proposition
        
        print("\n6. TRUTH EVALUATION:")
        if premise_prop:
            truth = premise_prop.truth_value_at(main_point)
            verifiers = premise_prop.verifiers
            print(f"\\exclude A truth: {truth}")
            print(f"Verifiers: {verifiers}")
            
            if not verifiers:
                print("\n⚠️  KEY ISSUE: Empty verifiers!")
                print("The constraint was satisfied but verifiers are empty.")
                print("This means the constraint doesn't properly ensure non-empty verifiers.")
                
        # Let's also check what the exclusion function looks like
        print("\n7. UNDERSTANDING THE MODEL:")
        print(f"Main world in model: {z3_model.evaluate(semantics.main_point['world'])}")
        
        # Try to understand why the constraint passed
        print("\n8. DIAGNOSIS:")
        print("The constraint for '\\exclude A' uses a complex formula.")
        print("This formula can be satisfied even when no verifiers exist.")
        print("The disconnect is between:")
        print("- Constraint formula (allows empty verifier models)")
        print("- Truth evaluation (requires non-empty verifiers)")


def main():
    analyze_exclusion_constraint()


if __name__ == '__main__':
    main()