"""
Test examples for SK2 strategy - copy of main examples but with SK2 as default.
"""

import sys
import os

# Add current directory to path before importing modules
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Get the src directory path
src_dir = os.path.join(current_dir, 'src')
if src_dir not in sys.path:
    sys.path.insert(0, src_dir)

# Exclusion imports
from model_checker.theory_lib.exclusion.semantic import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)

# Import operators and override default strategy
from model_checker.theory_lib.exclusion import operators
operators.DEFAULT_STRATEGY = "SK2"  # Use SK2 instead of MS
exclusion_operators = operators.create_operator_collection("SK2")

# We don't need default theory for this test

# Define semantic theories
exclusion_theory = {
    'semantics' : ExclusionSemantics,
    'proposition' : UnilateralProposition,
    'model_structure' : ExclusionStructure,
    'operators' : exclusion_operators,
}

# No default theory needed

# Define the theories to test
semantic_theories = {
    'exclusion' : exclusion_theory,
}

# Triple Negation Entailment
TN_ENTAIL_premises = ['\\exclude \\exclude \\exclude A']
TN_ENTAIL_conclusions = ['\\exclude A']
TN_ENTAIL_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 10,
    'expectation' : True,
}
TN_ENTAIL_example = [
    TN_ENTAIL_premises,
    TN_ENTAIL_conclusions,
    TN_ENTAIL_settings
]

# DISJUNCTIVE DEMORGAN'S LAW RL
DISJ_DM_RL_premises = ['(\\exclude A \\uniwedge \\exclude B)']
DISJ_DM_RL_conclusions = ['\\exclude (A \\univee B)']
DISJ_DM_RL_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 10,
    'expectation' : True,
}
DISJ_DM_RL_example = [
    DISJ_DM_RL_premises,
    DISJ_DM_RL_conclusions,
    DISJ_DM_RL_settings
]

# Define examples to run
example_range = {
    "Triple Negation Entailment (SK2)" : TN_ENTAIL_example,
    "Disjunctive DeMorgan's RL (SK2)" : DISJ_DM_RL_example,
}

if __name__ == '__main__':
    from model_checker.builder import BuildModule
    
    # Create a simple module object
    class SimpleModule:
        def __init__(self):
            self.semantic_theories = semantic_theories
            self.example_range = example_range
            self.file_path = __file__
    
    module = SimpleModule()
    
    # Build and run
    try:
        build_module = BuildModule(module)
        build_module.build_examples()
    except Exception as e:
        print(f"Error: {e}")
        # Try direct approach
        print("\nTrying direct approach...")
        from model_checker import __main__ as main_module
        main_module.main([__file__])