#!/usr/bin/env python3
"""
Script to check the actual results of all logos examples and determine correct expectation settings.
"""

import sys
sys.path.append('/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src')

from model_checker import run_test, ModelConstraints, Syntax
from model_checker.theory_lib.logos.semantic import LogosSemantics, LogosProposition, LogosModelStructure
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry

# Import all subtheory examples
from model_checker.theory_lib.logos.subtheories.extensional.examples import extensional_examples
from model_checker.theory_lib.logos.subtheories.modal.examples import modal_examples
from model_checker.theory_lib.logos.subtheories.constitutive.examples import constitutive_examples
from model_checker.theory_lib.logos.subtheories.counterfactual.examples import counterfactual_examples
from model_checker.theory_lib.logos.subtheories.relevance.examples import relevance_examples

# Create unified test example range
test_example_range = {
    **extensional_examples,
    **modal_examples,
    **constitutive_examples,
    **counterfactual_examples,
    **relevance_examples,
}

# Create operator registry for all subtheories
logos_registry = LogosOperatorRegistry()
logos_registry.load_subtheories(['extensional', 'modal', 'constitutive', 'counterfactual', 'relevance'])

print("Checking actual results for all examples...")
results = {}

for example_name, example_case in test_example_range.items():
    try:
        result = run_test(
            example_case,
            LogosSemantics,
            LogosProposition,
            logos_registry.get_operators(),
            Syntax,
            ModelConstraints,
            LogosModelStructure,
        )
        results[example_name] = result
        settings = example_case[2] if len(example_case) > 2 else {}
        current_expectation = settings.get('expectation', None)
        
        # Print examples where expectation doesn't match result
        if current_expectation is not None and current_expectation != result:
            print(f"{example_name}: Expected {current_expectation}, Got {result} - NEEDS FIX")
        
    except Exception as e:
        print(f"{example_name}: ERROR - {e}")
        results[example_name] = f"ERROR: {e}"

print(f"\nProcessed {len(results)} examples")