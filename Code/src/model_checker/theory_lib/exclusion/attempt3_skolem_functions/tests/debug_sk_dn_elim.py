"""
Debug script for SK implementation on DN_ELIM example

This script traces the evaluation of ¬¬A in the SK implementation
to understand why it's still showing as false.
"""

import z3
from model_checker import model, syntactic
from model_checker.theory_lib.exclusion import examples, semantic
from model_checker.theory_lib.exclusion.sk_exclusion import create_sk_operators
from model_checker.theory_lib.exclusion.sk_semantic import SKExclusionSemantics


def debug_dn_elim():
    """Debug DN_ELIM example with detailed tracing."""
    print("="*60)
    print("DEBUGGING DN_ELIM WITH SK IMPLEMENTATION")
    print("="*60)
    
    # Get example data
    premises, conclusions, settings = examples.DN_ELIM_example
    
    # Use SK operators
    operator_collection = create_sk_operators()
    
    # Create syntax with SK operators
    syntax = syntactic.Syntax(premises, conclusions, operator_collection)
    
    # Create SK semantics
    merged_settings = dict(settings)
    semantics = SKExclusionSemantics(merged_settings)
    
    # Initialize operators with SK semantics
    for op_name, op_class in operator_collection.items():
        op_instance = op_class(semantics)
        if not hasattr(semantics, 'operators'):
            semantics.operators = {}
        semantics.operators[op_name] = op_instance
    
    # Create constraints
    constraints = model.ModelConstraints(
        merged_settings, 
        syntax, 
        semantics, 
        semantic.UnilateralProposition
    )
    
    # Create model structure
    model_structure = semantic.ExclusionStructure(constraints, merged_settings)
    
    print(f"\nModel found: {model_structure.z3_model_status}")
    
    if model_structure.z3_model_status:
        # Interpret sentences
        model_structure.interpret(syntax.premises + syntax.conclusions)
        
        # Get the main world
        main_world = model_structure.z3_model[semantics.main_world]
        print(f"\nMain world: {main_world}")
        
        # Get the premise (¬¬A)
        premise = syntax.premises[0]
        print(f"\nPremise: {premise}")
        
        # Check truth value
        if hasattr(premise, 'proposition') and premise.proposition:
            truth_value = premise.proposition.truth_value_at(semantics.main_point)
            print(f"Truth value at main world: {truth_value}")
            
            # Get verifiers
            verifiers = premise.proposition.find_proposition()
            print(f"\nVerifiers for ¬¬A: {verifiers}")
            
            # Let's trace the evaluation manually
            print("\n" + "-"*40)
            print("MANUAL TRACE OF ¬¬A EVALUATION")
            print("-"*40)
            
            # Get the sentence letter A
            A = syntactic.Sentence("A")
            print(f"\nSentence letter A created")
            
            # Check what verifies A
            print("\nChecking verifiers of A...")
            # In exclusion semantics, atomic sentences are verified by states where verify(state, A) is true
            
            # Now let's check ¬A
            print("\nChecking ¬A...")
            # ¬A should be verified by states that exclude all verifiers of A
            
            # Finally check ¬¬A
            print("\nChecking ¬¬A...")
            # ¬¬A should be verified by states that exclude all verifiers of ¬A
            
            # Get the actual Z3 model values
            print("\n" + "-"*40)
            print("Z3 MODEL VALUES")
            print("-"*40)
            
            # Print all verify relations
            print("\nVerify relations:")
            for decl in model_structure.z3_model.decls():
                if 'verify' in str(decl):
                    print(f"  {decl}: {model_structure.z3_model[decl]}")
            
            # Print exclusion relations
            print("\nExclusion relations:")
            for decl in model_structure.z3_model.decls():
                if 'excludes' in str(decl):
                    val = model_structure.z3_model[decl]
                    # Only print non-trivial exclusions
                    if hasattr(val, 'else_value'):
                        print(f"  {decl}: {val}")


if __name__ == "__main__":
    debug_dn_elim()