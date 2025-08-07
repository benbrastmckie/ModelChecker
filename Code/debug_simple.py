#!/usr/bin/env python3
"""Simple debug to check MODEL 2 issue."""

import sys
import os
sys.path.insert(0, 'src')

# Import what we need
from model_checker.theory_lib.imposition.examples import IM_CM_0_example
from model_checker.theory_lib.imposition.semantic import ImpositionSemantics, ImpositionModelStructure
from model_checker.theory_lib.imposition.operators import imposition_operators
from model_checker.builder.example import BuildExample
from model_checker.iterate.interface import iterate_example

# Build the example
build_example = BuildExample(
    premises=IM_CM_0_example[0],
    conclusions=IM_CM_0_example[1], 
    semantics_class=ImpositionSemantics,
    model_structure_class=ImpositionModelStructure,
    settings=IM_CM_0_example[2],
    operators=imposition_operators
)

# Iterate to get multiple models
print("Finding models...")
model_structures = iterate_example(build_example)

if len(model_structures) > 1:
    print(f"\nFound {len(model_structures)} models")
    
    # Compare atomic propositions in both models
    for i, model in enumerate(model_structures):
        print(f"\n=== MODEL {i+1} ===")
        # Find proposition A
        for sentence in model.premises + model.conclusions:
            if sentence.name == "A" and sentence.sentence_letter is not None:
                prop = sentence.proposition
                print(f"Proposition A:")
                print(f"  Verifiers: {prop.verifiers}")
                print(f"  Falsifiers: {prop.falsifiers}")
                print(f"  Number of verifiers: {len(prop.verifiers)}")
                print(f"  Number of falsifiers: {len(prop.falsifiers)}")
                break