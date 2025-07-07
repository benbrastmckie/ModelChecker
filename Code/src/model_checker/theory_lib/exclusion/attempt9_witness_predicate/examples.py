"""
Examples Module for Witness Predicate Exclusion Theory

This module tests the witness predicate exclusion semantics implementation,
demonstrating that the FALSE PREMISE PROBLEM has been solved through
witness predicates in the model structure.

The witness predicate approach makes witness functions first-class model
citizens, enabling correct evaluation of formulas with existential quantification.

Usage:
------
This module can be run in two ways:

1. Command Line:
   ```bash
   model-checker path/to/this/examples.py
   # or
   ./dev_cli.py path/to/this/examples.py
   ```

2. IDE (VSCodium/VSCode):
   - Open this file in VSCodium/VSCode
   - Use the "Run Python File" play button in the top-right corner

Configuration:
-------------
The examples and theories to be run can be configured by:

1. Modifying which examples are run:
   - Edit the example_range dictionary
   - Comment/uncomment specific examples

2. To add new examples:
   - Define premises, conclusions, and settings
   - Add to example_range dictionary

Module Structure:
----------------
1. Imports:
   - Witness predicate exclusion components (semantic, operators)
   - Default theory components for comparison (optional)

2. Semantic Theories:
   - exclusion_theory: Witness predicate exclusion logic
   - default_theory: Classical logic implementation for comparison (optional)

3. Example Categories:
   - Frame Examples: Basic frame constraint tests
   - Negation Examples: Double/triple/quadruple negation tests
   - DeMorgan's Laws: All four forms
   - Distribution Laws: Conjunction/disjunction distribution
   - Absorption Laws: Various absorption patterns
   - Associativity Laws: Associativity tests
   - Identity Examples: Various logical identities

Example Format:
--------------
Each example is structured as a list: [premises, conclusions, settings]
- premises: List of formulas that serve as assumptions
- conclusions: List of formulas to be tested
- settings: Dictionary of specific settings for this example

Notes:
------
- The witness predicate theory solves examples that fail with static exclusion
- Examples marked with "FALSE PREMISE" comments failed in static approach
- At least one semantic theory must be included in semantic_theories
- At least one example must be included in example_range
"""

import os
import sys

# Import witness predicate exclusion components
from .semantic import WitnessPredicateSemantics, PredicateModelAdapter, WitnessPredicateProposition
from .operators import witness_predicate_operators

# Import exclusion theory components for proper printing
from model_checker.theory_lib.exclusion import ExclusionStructure

# Import custom structure that includes witness predicate printing
from .semantic import WitnessPredicateStructure

# Import default theory for comparison
from model_checker.theory_lib.default import (
    Semantics,
    Proposition,
    ModelStructure,
    default_operators,
)

##########################
### SET UP THE EXAMPLE ###
##########################

# Define semantic theories for testing
exclusion_theory = {
    "semantics": WitnessPredicateSemantics,
    "proposition": WitnessPredicateProposition,
    "model": WitnessPredicateStructure,
    "operators": witness_predicate_operators,
    "dictionary": {}  # No translation needed for exclusion theory
}

default_dictionary = {
    "\\exclude": "\\neg",
    "\\uniwedge": "\\wedge",
    "\\univee": "\\vee",
    "\\uniequiv": "\\equiv",
}

default_theory = {
    "semantics": Semantics,
    "proposition": Proposition,
    "model": ModelStructure,
    "operators": default_operators,
    "dictionary": default_dictionary,
}

#######################
### DEFINE SETTINGS ###
#######################

general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

example_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}

#####################
### FRAME EXAMPLES ###
#####################

# EMPTY CASE FOR CHECKING FRAME CONSTRAINTS
EMPTY_premises = []
EMPTY_conclusions = []
EMPTY_settings = {
    'N': 2,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 2,
    'iterate': 1,
    'expectation': True,
}
EMPTY_example = [
    EMPTY_premises,
    EMPTY_conclusions,
    EMPTY_settings,
]

# ATOMIC EXAMPLE
ATOMIC_premises = ['A']
ATOMIC_conclusions = ['A']
ATOMIC_settings = {
    'N': 2,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 2,
    'expectation': True,
}
ATOMIC_example = [
    ATOMIC_premises,
    ATOMIC_conclusions,
    ATOMIC_settings,
]

#############################
### NEGATION EXAMPLES     ###
### (PROBLEMATIC IN STATIC) #
#############################

# NEGATION TO SENTENCE
NEG_TO_SENT_premises = ['\\exclude A']
NEG_TO_SENT_conclusions = ['A']
NEG_TO_SENT_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': False,  # Note: expectation differs from elimination
}
NEG_TO_SENT_example = [
    NEG_TO_SENT_premises,
    NEG_TO_SENT_conclusions,
    NEG_TO_SENT_settings
]

# DOUBLE NEGATION ELIMINATION (FALSE PREMISE in static approach)
DN_ELIM_premises = ['\\exclude \\exclude A']
DN_ELIM_conclusions = ['A']
DN_ELIM_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'iterate': 1,
    'expectation': True,
}
DN_ELIM_example = [
    DN_ELIM_premises,
    DN_ELIM_conclusions,
    DN_ELIM_settings
]

# TRIPLE NEGATION ENTAILMENT (False premise in static approach)
TN_ENTAIL_premises = ['\\exclude \\exclude \\exclude A']
TN_ENTAIL_conclusions = ['\\exclude A']
TN_ENTAIL_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'expectation': True,
}
TN_ENTAIL_example = [
    TN_ENTAIL_premises,
    TN_ENTAIL_conclusions,
    TN_ENTAIL_settings
]

# DISJUNCTIVE SYLLOGISM (False premise in static approach)
DISJ_SYLL_premises = ['(A \\univee B)', '\\exclude B']
DISJ_SYLL_conclusions = ['A']
DISJ_SYLL_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': False,
}
DISJ_SYLL_example = [
    DISJ_SYLL_premises,
    DISJ_SYLL_conclusions,
    DISJ_SYLL_settings
]

# CONJUNCTION DEMORGANS LR (False premise in static approach)
CONJ_DM_LR_premises = ['\\exclude (A \\uniwedge B)']
CONJ_DM_LR_conclusions = ['(\\exclude A \\univee \\exclude B)']
CONJ_DM_LR_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': False,
}
CONJ_DM_LR_example = [
    CONJ_DM_LR_premises,
    CONJ_DM_LR_conclusions,
    CONJ_DM_LR_settings
]

# NO GLUTS (False premise in static approach)
NO_GLUT_premises = []
NO_GLUT_conclusions = ['\\exclude (A \\uniwedge \\exclude A)']
NO_GLUT_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
NO_GLUT_example = [
    NO_GLUT_premises,
    NO_GLUT_conclusions,
    NO_GLUT_settings,
]

########################
### EXAMPLE REGISTRY ###
########################

# Which examples to run - start with problematic examples
example_range = {
    # Frame examples
    "Only Frame Constraints": EMPTY_example,
    "Atomic Example": ATOMIC_example,
    
    # Classical negation examples (Problematic in static)
    "Negation to Sentence": NEG_TO_SENT_example,
    "Double Negation Elimination": DN_ELIM_example,
    "Triple Negation Entailment": TN_ENTAIL_example,
    "Disjunctive Syllogism": DISJ_SYLL_example,
    "Conjunctive DeMorgan's LR": CONJ_DM_LR_example,
    "No Gluts": NO_GLUT_example,
}

# Test subset - focus on core problematic examples
test_example_range = {
    "NO_GLUT": NO_GLUT_example,
}

# Switch between full suite and test subset
example_range = test_example_range  # Uncomment to use test subset

# Which semantic theories to compare
semantic_theories = {
    "exclusion_theory": exclusion_theory,
    # "default_theory": default_theory,  # Uncomment to compare with classical logic
}

if __name__ == "__main__":
    # This allows the module to be run with dev_cli.py
    # The ModelChecker framework will use example_range and semantic_theories
    pass