#!/usr/bin/env python3
"""Simple test for exclusion theory with iterate=2"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

# Test exclusion with iterate=2
from model_checker.theory_lib.exclusion.semantic import WitnessSemantics, WitnessModelAdapter, WitnessProposition
from model_checker.builder.example import BuildExample

# Define a simple test
premises = ['~A']
conclusions = ['A']
settings = {
    'N': 3,
    'iterate': 2,  # This is the key test
    'max_time': 5,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

try:
    print("Testing exclusion theory with iterate=2...")
    
    # Create the example
    example = BuildExample(
        WitnessSemantics, WitnessModelAdapter, WitnessProposition,
        premises, conclusions, settings,
        example_name="EX_TEST",
        theory_name="Exclusion"
    )
    
    # Build and check
    models = example.build_and_check()
    
    print(f"✓ Exclusion theory successfully found {len(models)} models")
    
    # Check if MODEL 2 has proper propositions
    if len(models) >= 2:
        model2 = models[1]
        print("✓ MODEL 2 exists")
        
        # Look for sentence letters and their propositions
        if hasattr(model2, 'syntax') and hasattr(model2.syntax, 'sentence_letters'):
            letters = model2.syntax.sentence_letters
            print(f"✓ Found {len(letters)} sentence letters")
            
            for letter in letters:
                if hasattr(letter, 'proposition') and letter.proposition:
                    prop = letter.proposition
                    v_count = len(prop.verifiers) if hasattr(prop, 'verifiers') else 0
                    f_count = len(prop.falsifiers) if hasattr(prop, 'falsifiers') else 0
                    print(f"  Letter {letter.sentence_letter}: V={v_count}, F={f_count}")
        
except Exception as e:
    print(f"✗ Exclusion theory failed: {e}")
    import traceback
    traceback.print_exc()