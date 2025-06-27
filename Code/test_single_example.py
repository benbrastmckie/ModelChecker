#!/usr/bin/env python3
"""
Test a single example to see the evaluation output.
"""

import sys
sys.path.insert(0, 'src')

from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example
from model_checker.builder import BuildModule

# Create a test module with only Triple Negation
test_examples = {
    "Triple Negation Entailment": TN_ENTAIL_example
}

# Import semantic theories
from model_checker.theory_lib.exclusion.semantic import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)
from model_checker.theory_lib.exclusion.operators import exclusion_operators

semantic_theories = {
    'exclusion': {
        'semantics': ExclusionSemantics,
        'proposition': UnilateralProposition,
        'model_structure': ExclusionStructure,
        'operators': exclusion_operators,
    }
}

# Create module
class TestModule:
    def __init__(self):
        self.semantic_theories = semantic_theories
        self.example_range = test_examples

if __name__ == '__main__':
    # Use BuildModule to run the test
    module = TestModule()
    
    # Run with print settings
    build = BuildModule(module, general_settings={'verbose': True})
    build.run_single_example("Triple Negation Entailment")