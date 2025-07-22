"""
Examples Module for Exclusion Theory

This module provides examples for the exclusion (witness uninegation) semantic framework,
including both countermodels showing invalidity and theorems showing validity.

The exclusion theory tests witness uninegation semantics implementation,
demonstrating that the FALSE PREMISE PROBLEM has been solved through
witness predicates in the model structure. The witness predicate approach
makes witness functions first-class model citizens, enabling correct
evaluation of formulas with existential quantification.

Example Categories:
------------------
1. Exclusion Logic Countermodels (EX_CM_*):
   - Frame constraint tests (empty models, gaps, gluts)
   - Negation problems (false premise issues from static approach)
   - DeMorgan's law failures
   - Identity relation failures

2. Exclusion Logic Theorems (EX_TH_*):
   - Distribution laws (conjunction/disjunction)
   - Absorption laws
   - Associativity laws
   - Valid logical identities

Usage:
------
This module can be run directly with model-checker or dev_cli.py:

```bash
model-checker path/to/this/examples.py
# or in development:
./dev_cli.py path/to/this/examples.py
```

To use a specific collection of examples, modify the example_range dictionary below.
"""

# Standard imports
import os
import sys

# Add current directory to path for proper imports
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Import witness uninegation components
from .semantic import WitnessSemantics, WitnessModelAdapter, WitnessProposition
from .operators import witness_operators

# Import custom structure that includes witness printing
from .semantic import WitnessStructure

# Import default theory for comparison
from model_checker.theory_lib.default import (
    Semantics,
    Proposition,
    ModelStructure,
    default_operators,
)


#####################
### COUNTERMODELS ###
#####################

# EX_CM_1: EMPTY CASE FOR CHECKING FRAME CONSTRAINTS
EX_CM_1_premises = []
EX_CM_1_conclusions = []
EX_CM_1_settings = {
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
EX_CM_1_example = [
    EX_CM_1_premises,
    EX_CM_1_conclusions,
    EX_CM_1_settings,
]

# EX_CM_2: GAPS CASE
EX_CM_2_premises = []
EX_CM_2_conclusions = []
EX_CM_2_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}
EX_CM_2_example = [
    EX_CM_2_premises,
    EX_CM_2_conclusions,
    EX_CM_2_settings,
]

# EX_CM_3: NO GLUT CASE
EX_CM_3_premises = []
EX_CM_3_conclusions = []
EX_CM_3_settings = {
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
EX_CM_3_example = [
    EX_CM_3_premises,
    EX_CM_3_conclusions,
    EX_CM_3_settings,
]

# EX_CM_4: NEGATION TO SENTENCE (FALSE PREMISE PROBLEM)
EX_CM_4_premises = ['\\func_unineg A']
EX_CM_4_conclusions = ['A']
EX_CM_4_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'iterate': 1,
    'expectation': True,
}
EX_CM_4_example = [
    EX_CM_4_premises,
    EX_CM_4_conclusions,
    EX_CM_4_settings,
]

# EX_CM_5: SENTENCE TO NEGATION (FALSE PREMISE PROBLEM)
EX_CM_5_premises = ['A']
EX_CM_5_conclusions = ['\\func_unineg A']
EX_CM_5_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'iterate': 1,
    'expectation': True,
}
EX_CM_5_example = [
    EX_CM_5_premises,
    EX_CM_5_conclusions,
    EX_CM_5_settings,
]

# EX_CM_6: DOUBLE NEGATION ELIMINATION (FALSE PREMISE PROBLEM)
EX_CM_6_premises = ['\\func_unineg \\func_unineg A']
EX_CM_6_conclusions = ['A']
EX_CM_6_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'iterate': 1,
    'expectation': True,
}
EX_CM_6_example = [
    EX_CM_6_premises,
    EX_CM_6_conclusions,
    EX_CM_6_settings,
]

# EX_CM_7: DOUBLE NEGATION INTRODUCTION (FALSE PREMISE PROBLEM)
EX_CM_7_premises = ['A']
EX_CM_7_conclusions = ['\\func_unineg \\func_unineg A']
EX_CM_7_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'iterate': 1,
    'expectation': True,
}
EX_CM_7_example = [
    EX_CM_7_premises,
    EX_CM_7_conclusions,
    EX_CM_7_settings,
]

# EX_CM_8: TRIPLE NEGATION ENTAILMENT (FALSE PREMISE PROBLEM)
EX_CM_8_premises = ['\\func_unineg \\func_unineg \\func_unineg A']
EX_CM_8_conclusions = ['\\func_unineg A']
EX_CM_8_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 20,
    'expectation': True,
}
EX_CM_8_example = [
    EX_CM_8_premises,
    EX_CM_8_conclusions,
    EX_CM_8_settings,
]

# EX_CM_9: QUADRUPLE NEGATION ENTAILMENT (FALSE PREMISE PROBLEM)
EX_CM_9_premises = ['\\func_unineg \\func_unineg \\func_unineg \\func_unineg A']
EX_CM_9_conclusions = ['A']
EX_CM_9_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 20,
    'expectation': True,
}
EX_CM_9_example = [
    EX_CM_9_premises,
    EX_CM_9_conclusions,
    EX_CM_9_settings,
]

# EX_CM_10: CONJUNCTION DEMORGAN LR (FALSE PREMISE PROBLEM)
EX_CM_10_premises = ['(\\func_unineg A \\univee \\func_unineg B)']
EX_CM_10_conclusions = ['\\func_unineg (A \\uniwedge B)']
EX_CM_10_settings = {
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
EX_CM_10_example = [
    EX_CM_10_premises,
    EX_CM_10_conclusions,
    EX_CM_10_settings,
]

# EX_CM_11: CONJUNCTION DEMORGAN RL (FALSE PREMISE PROBLEM)
EX_CM_11_premises = ['\\func_unineg (A \\uniwedge B)']
EX_CM_11_conclusions = ['(\\func_unineg A \\univee \\func_unineg B)']
EX_CM_11_settings = {
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
EX_CM_11_example = [
    EX_CM_11_premises,
    EX_CM_11_conclusions,
    EX_CM_11_settings,
]

# EX_CM_12: DISJUNCTION DEMORGAN LR (FALSE PREMISE PROBLEM)
EX_CM_12_premises = ['\\func_unineg (A \\univee B)']
EX_CM_12_conclusions = ['(\\func_unineg A \\uniwedge \\func_unineg B)']
EX_CM_12_settings = {
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
EX_CM_12_example = [
    EX_CM_12_premises,
    EX_CM_12_conclusions,
    EX_CM_12_settings,
]

# EX_CM_13: DISJUNCTION DEMORGAN RL (FALSE PREMISE PROBLEM)
EX_CM_13_premises = ['(\\func_unineg A \\uniwedge \\func_unineg B)']
EX_CM_13_conclusions = ['\\func_unineg (A \\univee B)']
EX_CM_13_settings = {
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
EX_CM_13_example = [
    EX_CM_13_premises,
    EX_CM_13_conclusions,
    EX_CM_13_settings,
]

# EX_CM_14: DOUBLE NEGATION IDENTITY
EX_CM_14_premises = []
EX_CM_14_conclusions = ['(\\func_unineg \\func_unineg A \\uniequiv A)']
EX_CM_14_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}
EX_CM_14_example = [
    EX_CM_14_premises,
    EX_CM_14_conclusions,
    EX_CM_14_settings,
]

# EX_CM_15: TRIPLE NEGATION IDENTITY
EX_CM_15_premises = []
EX_CM_15_conclusions = ['(\\func_unineg \\func_unineg \\func_unineg A \\uniequiv \\func_unineg A)']
EX_CM_15_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}
EX_CM_15_example = [
    EX_CM_15_premises,
    EX_CM_15_conclusions,
    EX_CM_15_settings,
]

# EX_CM_16: CONJUNCTION DEMORGAN IDENTITY
EX_CM_16_premises = []
EX_CM_16_conclusions = ['(\\func_unineg (A \\uniwedge B) \\uniequiv (\\func_unineg A \\univee \\func_unineg B))']
EX_CM_16_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}
EX_CM_16_example = [
    EX_CM_16_premises,
    EX_CM_16_conclusions,
    EX_CM_16_settings,
]

# EX_CM_17: DISJUNCTION DEMORGAN IDENTITY
EX_CM_17_premises = []
EX_CM_17_conclusions = ['(\\func_unineg (A \\univee B) \\uniequiv (\\func_unineg A \\uniwedge \\func_unineg B))']
EX_CM_17_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}
EX_CM_17_example = [
    EX_CM_17_premises,
    EX_CM_17_conclusions,
    EX_CM_17_settings,
]

# EX_CM_18: DISJUNCTION DISTRIBUTION IDENTITY
EX_CM_18_premises = []
EX_CM_18_conclusions = ['((A \\univee (B \\uniwedge C)) \\uniequiv ((A \\univee B) \\uniwedge (A \\univee C)))']
EX_CM_18_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}
EX_CM_18_example = [
    EX_CM_18_premises,
    EX_CM_18_conclusions,
    EX_CM_18_settings,
]

# EX_CM_19: COMPLEX DEMORGAN (THEOREM 17)
EX_CM_19_premises = []
EX_CM_19_conclusions = ['((\\func_unineg (A \\univee B) \\uniequiv (\\func_unineg A \\uniwedge \\func_unineg B)) \\uniwedge (\\func_unineg (A \\uniwedge B) \\uniequiv (\\func_unineg A \\univee \\func_unineg B)))']
EX_CM_19_settings = {
    'N': 4,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'expectation': True,
}
EX_CM_19_example = [
    EX_CM_19_premises,
    EX_CM_19_conclusions,
    EX_CM_19_settings,
]

# EX_CM_20: DEMORGAN COMPLEX
EX_CM_20_premises = []
EX_CM_20_conclusions = ['(\\func_unineg (A \\univee B) \\uniequiv (\\func_unineg A \\uniwedge \\func_unineg B))']
EX_CM_20_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}
EX_CM_20_example = [
    EX_CM_20_premises,
    EX_CM_20_conclusions,
    EX_CM_20_settings,
]

# EX_CM_21: BASIC TEST
EX_CM_21_premises = ['A']
EX_CM_21_conclusions = ['B']
EX_CM_21_settings = {
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
EX_CM_21_example = [
    EX_CM_21_premises,
    EX_CM_21_conclusions,
    EX_CM_21_settings,
]

# EX_CM_22: DISTRIBUTION TEST
EX_CM_22_premises = ['(A \\uniwedge (B \\univee C))']
EX_CM_22_conclusions = ['((A \\uniwedge B) \\univee (A \\uniwedge D))']
EX_CM_22_settings = {
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
EX_CM_22_example = [
    EX_CM_22_premises,
    EX_CM_22_conclusions,
    EX_CM_22_settings,
]



################
### THEOREMS ###
################

# EX_TH_1: ATOMIC THEOREM
EX_TH_1_premises = ['A']
EX_TH_1_conclusions = ['A']
EX_TH_1_settings = {
    'N': 2,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 2,
    'expectation': False,
}
EX_TH_1_example = [
    EX_TH_1_premises,
    EX_TH_1_conclusions,
    EX_TH_1_settings,
]

# EX_TH_2: DISJUNCTIVE SYLLOGISM
EX_TH_2_premises = ['(A \\univee B)', '\\func_unineg A']
EX_TH_2_conclusions = ['B']
EX_TH_2_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'iterate': 1,
    'expectation': False,
}
EX_TH_2_example = [
    EX_TH_2_premises,
    EX_TH_2_conclusions,
    EX_TH_2_settings,
]

# EX_TH_3: CONJUNCTION DISTRIBUTION LR
EX_TH_3_premises = ['(A \\uniwedge (B \\univee C))']
EX_TH_3_conclusions = ['((A \\uniwedge B) \\univee (A \\uniwedge C))']
EX_TH_3_settings = {
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
EX_TH_3_example = [
    EX_TH_3_premises,
    EX_TH_3_conclusions,
    EX_TH_3_settings,
]

# EX_TH_4: CONJUNCTION DISTRIBUTION RL
EX_TH_4_premises = ['((A \\uniwedge B) \\univee (A \\uniwedge C))']
EX_TH_4_conclusions = ['(A \\uniwedge (B \\univee C))']
EX_TH_4_settings = {
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
EX_TH_4_example = [
    EX_TH_4_premises,
    EX_TH_4_conclusions,
    EX_TH_4_settings,
]

# EX_TH_5: DISJUNCTION DISTRIBUTION LR
EX_TH_5_premises = ['(A \\univee (B \\uniwedge C))']
EX_TH_5_conclusions = ['((A \\univee B) \\uniwedge (A \\univee C))']
EX_TH_5_settings = {
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
EX_TH_5_example = [
    EX_TH_5_premises,
    EX_TH_5_conclusions,
    EX_TH_5_settings,
]

# EX_TH_6: DISJUNCTION DISTRIBUTION RL
EX_TH_6_premises = ['((A \\univee B) \\uniwedge (A \\univee C))']
EX_TH_6_conclusions = ['(A \\univee (B \\uniwedge C))']
EX_TH_6_settings = {
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
EX_TH_6_example = [
    EX_TH_6_premises,
    EX_TH_6_conclusions,
    EX_TH_6_settings,
]

# EX_TH_7: CONJUNCTION ABSORPTION LR
EX_TH_7_premises = ['(A \\uniwedge (A \\univee B))']
EX_TH_7_conclusions = ['A']
EX_TH_7_settings = {
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
EX_TH_7_example = [
    EX_TH_7_premises,
    EX_TH_7_conclusions,
    EX_TH_7_settings,
]

# EX_TH_8: CONJUNCTION ABSORPTION RL
EX_TH_8_premises = ['A']
EX_TH_8_conclusions = ['(A \\uniwedge (A \\univee B))']
EX_TH_8_settings = {
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
EX_TH_8_example = [
    EX_TH_8_premises,
    EX_TH_8_conclusions,
    EX_TH_8_settings,
]

# EX_TH_9: DISJUNCTION ABSORPTION LR
EX_TH_9_premises = ['(A \\univee (A \\uniwedge B))']
EX_TH_9_conclusions = ['A']
EX_TH_9_settings = {
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
EX_TH_9_example = [
    EX_TH_9_premises,
    EX_TH_9_conclusions,
    EX_TH_9_settings,
]

# EX_TH_10: DISJUNCTION ABSORPTION RL
EX_TH_10_premises = ['A']
EX_TH_10_conclusions = ['(A \\univee (A \\uniwedge B))']
EX_TH_10_settings = {
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
EX_TH_10_example = [
    EX_TH_10_premises,
    EX_TH_10_conclusions,
    EX_TH_10_settings,
]

# EX_TH_11: CONJUNCTION ASSOCIATIVITY LR
EX_TH_11_premises = ['((A \\uniwedge B) \\uniwedge C)']
EX_TH_11_conclusions = ['(A \\uniwedge (B \\uniwedge C))']
EX_TH_11_settings = {
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
EX_TH_11_example = [
    EX_TH_11_premises,
    EX_TH_11_conclusions,
    EX_TH_11_settings,
]

# EX_TH_12: CONJUNCTION ASSOCIATIVITY RL
EX_TH_12_premises = ['(A \\uniwedge (B \\uniwedge C))']
EX_TH_12_conclusions = ['((A \\uniwedge B) \\uniwedge C)']
EX_TH_12_settings = {
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
EX_TH_12_example = [
    EX_TH_12_premises,
    EX_TH_12_conclusions,
    EX_TH_12_settings,
]

# EX_TH_13: DISJUNCTION ASSOCIATIVITY LR
EX_TH_13_premises = ['((A \\univee B) \\univee C)']
EX_TH_13_conclusions = ['(A \\univee (B \\univee C))']
EX_TH_13_settings = {
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
EX_TH_13_example = [
    EX_TH_13_premises,
    EX_TH_13_conclusions,
    EX_TH_13_settings,
]

# EX_TH_14: DISJUNCTION ASSOCIATIVITY RL
EX_TH_14_premises = ['(A \\univee (B \\univee C))']
EX_TH_14_conclusions = ['((A \\univee B) \\univee C)']
EX_TH_14_settings = {
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
EX_TH_14_example = [
    EX_TH_14_premises,
    EX_TH_14_conclusions,
    EX_TH_14_settings,
]

# EX_TH_15: CONJUNCTION DISTRIBUTION IDENTITY
EX_TH_15_premises = []
EX_TH_15_conclusions = ['((A \\uniwedge (B \\univee C)) \\uniequiv ((A \\uniwedge B) \\univee (A \\uniwedge C)))']
EX_TH_15_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': False,
}
EX_TH_15_example = [
    EX_TH_15_premises,
    EX_TH_15_conclusions,
    EX_TH_15_settings,
]

# EX_TH_16: COMPLEX UNILATERAL FORMULA
EX_TH_16_premises = ['(A \\uniwedge (B \\univee C))']
EX_TH_16_conclusions = ['((A \\univee B) \\uniwedge (A \\univee B))']
EX_TH_16_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'expectation': False,
}
EX_TH_16_example = [
    EX_TH_16_premises,
    EX_TH_16_conclusions,
    EX_TH_16_settings,
]



# Create collections for different exclusion example types
exclusion_cm_examples = {
    "EX_CM_1": EX_CM_1_example,    # EMPTY CASE FOR CHECKING FRAME CONSTRAINTS
    "EX_CM_2": EX_CM_2_example,    # GAPS CASE
    "EX_CM_3": EX_CM_3_example,    # NO GLUT CASE
    "EX_CM_4": EX_CM_4_example,    # NEGATION TO SENTENCE (FALSE PREMISE PROBLEM)
    "EX_CM_5": EX_CM_5_example,    # SENTENCE TO NEGATION (FALSE PREMISE PROBLEM)
    "EX_CM_6": EX_CM_6_example,    # DOUBLE NEGATION ELIMINATION (FALSE PREMISE PROBLEM)
    "EX_CM_7": EX_CM_7_example,    # DOUBLE NEGATION INTRODUCTION (FALSE PREMISE PROBLEM)
    "EX_CM_8": EX_CM_8_example,    # TRIPLE NEGATION ENTAILMENT (FALSE PREMISE PROBLEM)
    "EX_CM_9": EX_CM_9_example,    # QUADRUPLE NEGATION ENTAILMENT (FALSE PREMISE PROBLEM)
    "EX_CM_10": EX_CM_10_example,  # CONJUNCTION DEMORGAN LR (FALSE PREMISE PROBLEM)
    "EX_CM_11": EX_CM_11_example,  # CONJUNCTION DEMORGAN RL (FALSE PREMISE PROBLEM)
    "EX_CM_12": EX_CM_12_example,  # DISJUNCTION DEMORGAN LR (FALSE PREMISE PROBLEM)
    "EX_CM_13": EX_CM_13_example,  # DISJUNCTION DEMORGAN RL (FALSE PREMISE PROBLEM)
    "EX_CM_14": EX_CM_14_example,  # DOUBLE NEGATION IDENTITY
    "EX_CM_15": EX_CM_15_example,  # TRIPLE NEGATION IDENTITY
    "EX_CM_16": EX_CM_16_example,  # CONJUNCTION DEMORGAN IDENTITY
    "EX_CM_17": EX_CM_17_example,  # DISJUNCTION DEMORGAN IDENTITY
    "EX_CM_18": EX_CM_18_example,  # DISJUNCTION DISTRIBUTION IDENTITY
    "EX_CM_19": EX_CM_19_example,  # COMPLEX DEMORGAN (THEOREM 17)
    "EX_CM_20": EX_CM_20_example,  # DEMORGAN COMPLEX
    "EX_CM_21": EX_CM_21_example,  # BASIC TEST
    "EX_CM_22": EX_CM_22_example,  # DISTRIBUTION TEST
}

exclusion_th_examples = {
    "EX_TH_1": EX_TH_1_example,    # ATOMIC THEOREM
    "EX_TH_2": EX_TH_2_example,    # DISJUNCTIVE SYLLOGISM
    "EX_TH_3": EX_TH_3_example,    # CONJUNCTION DISTRIBUTION LR
    "EX_TH_4": EX_TH_4_example,    # CONJUNCTION DISTRIBUTION RL
    "EX_TH_5": EX_TH_5_example,    # DISJUNCTION DISTRIBUTION LR
    "EX_TH_6": EX_TH_6_example,    # DISJUNCTION DISTRIBUTION RL
    "EX_TH_7": EX_TH_7_example,    # CONJUNCTION ABSORPTION LR
    "EX_TH_8": EX_TH_8_example,    # CONJUNCTION ABSORPTION RL
    "EX_TH_9": EX_TH_9_example,    # DISJUNCTION ABSORPTION LR
    "EX_TH_10": EX_TH_10_example,  # DISJUNCTION ABSORPTION RL
    "EX_TH_11": EX_TH_11_example,  # CONJUNCTION ASSOCIATIVITY LR
    "EX_TH_12": EX_TH_12_example,  # CONJUNCTION ASSOCIATIVITY RL
    "EX_TH_13": EX_TH_13_example,  # DISJUNCTION ASSOCIATIVITY LR
    "EX_TH_14": EX_TH_14_example,  # DISJUNCTION ASSOCIATIVITY RL
    "EX_TH_15": EX_TH_15_example,  # CONJUNCTION DISTRIBUTION IDENTITY
    "EX_TH_16": EX_TH_16_example,  # COMPLEX UNILATERAL FORMULA
}

# Combined collection of all exclusion examples
unit_tests = {**exclusion_cm_examples, **exclusion_th_examples}

# Aliases for main dictionary (backward compatibility)
test_example_range = unit_tests
all_exclusion_examples = unit_tests

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Define semantic theories for testing
unilateral_theory = {
    "semantics": WitnessSemantics,
    "proposition": WitnessProposition,
    "model": WitnessStructure,
    "operators": witness_operators,
    "dictionary": {}  # No translation needed for unilateral theory
}

default_dictionary = {
    "\\func_unineg": "\\neg",
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

# Specify which theories to use
semantic_theories = {
    "unilateral_theory": unilateral_theory,
    # "default_theory": default_theory,  # Uncomment to compare with bilateral logic
}

# Default example range (curated subset for direct execution)
example_range = {
    # Frame examples
    "EX_CM_1": EX_CM_1_example,    # EMPTY CASE FOR CHECKING FRAME CONSTRAINTS
    "EX_CM_2": EX_CM_2_example,    # GAPS CASE
    "EX_CM_3": EX_CM_3_example,    # NO GLUT CASE
    "EX_TH_1": EX_TH_1_example,    # ATOMIC THEOREM
    
    # Basic countermodel examples
    "EX_CM_21": EX_CM_21_example,  # BASIC TEST
    "EX_TH_2": EX_TH_2_example,    # DISJUNCTIVE SYLLOGISM
    
    # Bilateral negation examples (Problematic in static)
    "EX_CM_4": EX_CM_4_example,    # NEGATION TO SENTENCE (FALSE PREMISE PROBLEM)
    "EX_CM_5": EX_CM_5_example,    # SENTENCE TO NEGATION (FALSE PREMISE PROBLEM)
    "EX_CM_6": EX_CM_6_example,    # DOUBLE NEGATION ELIMINATION (FALSE PREMISE PROBLEM)
    "EX_CM_7": EX_CM_7_example,    # DOUBLE NEGATION INTRODUCTION (FALSE PREMISE PROBLEM)
    "EX_CM_8": EX_CM_8_example,    # TRIPLE NEGATION ENTAILMENT (FALSE PREMISE PROBLEM)
    "EX_CM_9": EX_CM_9_example,    # QUADRUPLE NEGATION ENTAILMENT (FALSE PREMISE PROBLEM)

    # DeMorgan's laws (Problematic in static)
    "EX_CM_10": EX_CM_10_example,  # CONJUNCTION DEMORGAN LR (FALSE PREMISE PROBLEM)
    "EX_CM_11": EX_CM_11_example,  # CONJUNCTION DEMORGAN RL (FALSE PREMISE PROBLEM)
    "EX_CM_12": EX_CM_12_example,  # DISJUNCTION DEMORGAN LR (FALSE PREMISE PROBLEM)
    "EX_CM_13": EX_CM_13_example,  # DISJUNCTION DEMORGAN RL (FALSE PREMISE PROBLEM)

    # Distribution laws
    "EX_TH_3": EX_TH_3_example,    # CONJUNCTION DISTRIBUTION LR
    "EX_TH_4": EX_TH_4_example,    # CONJUNCTION DISTRIBUTION RL
    "EX_TH_5": EX_TH_5_example,    # DISJUNCTION DISTRIBUTION LR
    "EX_TH_6": EX_TH_6_example,    # DISJUNCTION DISTRIBUTION RL

    # Absorption laws
    "EX_TH_7": EX_TH_7_example,    # CONJUNCTION ABSORPTION LR
    "EX_TH_8": EX_TH_8_example,    # CONJUNCTION ABSORPTION RL
    "EX_TH_9": EX_TH_9_example,    # DISJUNCTION ABSORPTION LR
    "EX_TH_10": EX_TH_10_example,  # DISJUNCTION ABSORPTION RL

    # Associativity laws
    "EX_TH_11": EX_TH_11_example,  # CONJUNCTION ASSOCIATIVITY LR
    "EX_TH_12": EX_TH_12_example,  # CONJUNCTION ASSOCIATIVITY RL
    "EX_TH_13": EX_TH_13_example,  # DISJUNCTION ASSOCIATIVITY LR
    "EX_TH_14": EX_TH_14_example,  # DISJUNCTION ASSOCIATIVITY RL

    # Identity examples
    "EX_CM_14": EX_CM_14_example,  # DOUBLE NEGATION IDENTITY
    "EX_CM_15": EX_CM_15_example,  # TRIPLE NEGATION IDENTITY
    "EX_CM_16": EX_CM_16_example,  # CONJUNCTION DEMORGAN IDENTITY
    "EX_CM_17": EX_CM_17_example,  # DISJUNCTION DEMORGAN IDENTITY
    "EX_TH_15": EX_TH_15_example,  # CONJUNCTION DISTRIBUTION IDENTITY
    "EX_CM_18": EX_CM_18_example,  # DISJUNCTION DISTRIBUTION IDENTITY

    # Complex examples
    "EX_CM_19": EX_CM_19_example,  # COMPLEX DEMORGAN (THEOREM 17)
    "EX_CM_20": EX_CM_20_example,  # DEMORGAN COMPLEX
    "EX_TH_16": EX_TH_16_example,  # COMPLEX UNILATERAL FORMULA
}


def get_examples():
    """
    Get all exclusion examples.
    
    Returns:
        dict: Dictionary containing all exclusion examples
    """
    return {
        'countermodels': exclusion_cm_examples,
        'theorems': exclusion_th_examples,
        'all': unit_tests
    }


# Make this module runnable from the command line
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)
