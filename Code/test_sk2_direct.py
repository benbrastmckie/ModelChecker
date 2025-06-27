#!/usr/bin/env python3
"""
Direct test of SK2 strategy by temporarily modifying the default.
"""

import sys
import os
sys.path.insert(0, 'src')

# Modify the default strategy before importing examples
from model_checker.theory_lib.exclusion import operators
operators.DEFAULT_STRATEGY = "SK2"

# Now run the examples
from model_checker.theory_lib.exclusion.examples import (
    TN_ENTAIL_example,
    DISJ_DM_RL_example
)

# Create a minimal test module
test_examples = {
    "Triple Negation (SK2)": TN_ENTAIL_example,
    "Disjunctive DeMorgan RL (SK2)": DISJ_DM_RL_example,
}

# Import after setting strategy
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

# Run with the custom settings
if __name__ == '__main__':
    print(f"Testing with SK2 strategy (current default: {operators.DEFAULT_STRATEGY})")
    print("="*60)
    
    # Import and run
    import subprocess
    
    # Create a test file
    test_content = f'''
import sys
import os
sys.path.insert(0, 'src')

from model_checker.theory_lib.exclusion import operators
operators.DEFAULT_STRATEGY = "SK2"

from model_checker.theory_lib.exclusion.examples import *

# Override example range
example_range = {{
    "Triple Negation (SK2)": TN_ENTAIL_example,
    "Disjunctive DeMorgan RL (SK2)": DISJ_DM_RL_example,
}}

if __name__ == '__main__':
    import subprocess
    subprocess.run(["python", "-m", "model_checker", __file__], cwd=os.path.dirname(__file__))
'''
    
    # Write temporary test file
    with open('temp_sk2_test.py', 'w') as f:
        f.write(test_content)
    
    try:
        # Run using model checker
        result = subprocess.run(
            ["python", "-m", "model_checker", "temp_sk2_test.py"],
            capture_output=True,
            text=True
        )
        print(result.stdout)
        if result.stderr:
            print("STDERR:")
            print(result.stderr)
    finally:
        # Clean up
        import os
        if os.path.exists('temp_sk2_test.py'):
            os.remove('temp_sk2_test.py')