#!/usr/bin/env python3
"""Debug script to understand the imposition MODEL 2 issue."""

import sys
sys.path.insert(0, 'src')

from model_checker.builder.module import BuildModule

# Run the imposition example  
from model_checker.settings import Settings
settings = Settings()
settings.file_path = 'src/model_checker/theory_lib/imposition/examples.py'
module = BuildModule(settings)
module.run_examples()

# Check if we got multiple models
if hasattr(module, 'model_structures') and len(module.model_structures) > 1:
    print("\n\n=== DEBUGGING MODEL 2 ===")
    model2 = module.model_structures[1]
    
    # Check atomic propositions
    for sentence in model2.premises + model2.conclusions:
        if sentence.sentence_letter is not None:
            prop = sentence.proposition
            print(f"\nAtomic proposition: {sentence.name}")
            print(f"  Sentence letter: {sentence.sentence_letter}")
            print(f"  Verifiers: {prop.verifiers}")
            print(f"  Falsifiers: {prop.falsifiers}")
            
            # Try to manually check verify/falsify relations
            if model2.z3_model:
                print("  Manual check:")
                for state in model2.all_states[:4]:  # Check first few states
                    verify_result = model2.z3_model.eval(
                        model2.semantics.verify(state, sentence.sentence_letter),
                        model_completion=True
                    )
                    falsify_result = model2.z3_model.eval(
                        model2.semantics.falsify(state, sentence.sentence_letter), 
                        model_completion=True
                    )
                    print(f"    State {state}: verify={verify_result}, falsify={falsify_result}")