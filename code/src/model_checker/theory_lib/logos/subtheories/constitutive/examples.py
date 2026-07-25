"""
Constitutive Examples Module for Logos Theory

This module provides constitutive-specific examples for the logos semantic framework,
including both countermodels showing invalidity and theorems showing validity.

Example Categories:
------------------
1. Constitutive Logic Countermodels (CL_CM_*):
   - Tests for invalid constitutive arguments
   - Ground/essence operators and identity relations

2. Constitutive Logic Theorems (CL_TH_*):
   - Tests for valid constitutive arguments
   - Relationships between ground, essence and identity

3. Relevance Logic Countermodels/Theorems (REL_CM_*/REL_TH_*):
   - Absorbed from the former relevance subtheory, which contributed no
     operators of its own -- RelevanceOperator (\\preceq) is defined here.

Usage:
------
This module can be run directly with model-checker or dev_cli.py:

```bash
model-checker path/to/this/constitutive.py
# or in development:
./dev_cli.py path/to/this/constitutive.py
```

To use a specific collection of examples, modify the example_range dictionary below.
"""

import os
import subprocess
import sys

from ...operators import LogosOperatorRegistry
from ...semantic import LogosSemantics, LogosProposition, LogosModelStructure

# Standard imports

# Add parent directories to path for proper imports
current_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(current_dir)
parent_parent_dir = os.path.dirname(parent_dir)
if parent_dir not in sys.path:
    sys.path.insert(0, parent_dir)
if parent_parent_dir not in sys.path:
    sys.path.insert(0, parent_parent_dir)

# Import semantic classes - already imported above

# Import operators


#####################
### COUNTERMODELS ###
#####################

# CL_CM_1: EQUIVALENCE OF TAUTOLOGIES
CL_CM_1_premises = []
CL_CM_1_conclusions = ['((A \\vee \\neg A) \\equiv (B \\vee \\neg B))']
CL_CM_1_settings = {
    'N': 4,
    'contingent': True,
    'non_null': False,
    'non_empty': False,
    'disjoint': True,
    'max_time': 1,
    'iterate': 2,
    'expectation': True,
}
CL_CM_1_example = [
    CL_CM_1_premises,
    CL_CM_1_conclusions,
    CL_CM_1_settings,
]

# CL_CM_2: EQUIVALENCE OF CONTRADICTIONS
CL_CM_2_premises = []
CL_CM_2_conclusions = ['((A \\wedge \\neg A) \\equiv (B \\wedge \\neg B))']
CL_CM_2_settings = {
    'N': 4,
    'contingent': True,
    'non_null': False,
    'non_empty': False,
    'disjoint': True,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CL_CM_2_example = [
    CL_CM_2_premises,
    CL_CM_2_conclusions,
    CL_CM_2_settings,
]

# CL_CM_3: GROUND CONJUNCTION SUPPLEMENTATION
CL_CM_3_premises = ['(A \\leq B)','(C \\leq D)']
CL_CM_3_conclusions = ['((A \\wedge C) \\leq (B \\wedge D))']
CL_CM_3_settings = {
    'N': 4,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 2,
    'expectation': True,
}
CL_CM_3_example = [
    CL_CM_3_premises,
    CL_CM_3_conclusions,
    CL_CM_3_settings,
]

# CL_CM_4: ESSENCE DISJUNCTION SUPPLEMENTATION
CL_CM_4_premises = ['(A \\sqsubseteq B)','(C \\sqsubseteq D)']
CL_CM_4_conclusions = ['((A \\vee C) \\sqsubseteq (B \\vee D))']
CL_CM_4_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CL_CM_4_example = [
    CL_CM_4_premises,
    CL_CM_4_conclusions,
    CL_CM_4_settings,
]

# CL_CM_5: IDENTITY ABSORPTION: DISJUNCTION OVER CONJUNCTION
CL_CM_5_premises = []
CL_CM_5_conclusions = ['(A \\equiv (A \\vee (A \\wedge B)))']
CL_CM_5_settings = {
    'N': 4,
    'contingent': True,
    'non_null': False,
    'non_empty': False,
    'disjoint': True,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CL_CM_5_example = [
    CL_CM_5_premises,
    CL_CM_5_conclusions,
    CL_CM_5_settings,
]

# CL_CM_6: IDENTITY ABSORPTION: CONJUNCTION OVER DISJUNCTION
CL_CM_6_premises = []
CL_CM_6_conclusions = ['(A \\equiv (A \\wedge (A \\vee B)))']
CL_CM_6_settings = {
    'N': 4,
    'contingent': True,
    'non_null': False,
    'non_empty': False,
    'disjoint': True,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CL_CM_6_example = [
    CL_CM_6_premises,
    CL_CM_6_conclusions,
    CL_CM_6_settings,
]

# CL_CM_7: IDENTITY DISTRIBUTION: CONJUNCTION OVER DISJUNCTION
CL_CM_7_premises = []
CL_CM_7_conclusions = ['((A \\wedge (B \\vee C)) \\equiv ((A \\wedge B) \\vee (A \\wedge C)))']
CL_CM_7_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': True,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CL_CM_7_example = [
    CL_CM_7_premises,
    CL_CM_7_conclusions,
    CL_CM_7_settings,
]

# CL_CM_8: IDENTITY DISTRIBUTION: DISJUNCTION OVER CONJUNCTION
CL_CM_8_premises = []
CL_CM_8_conclusions = ['((A \\vee (B \\wedge C)) \\equiv ((A \\vee B) \\wedge (A \\vee C)))']
CL_CM_8_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': True,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CL_CM_8_example = [
    CL_CM_8_premises,
    CL_CM_8_conclusions,
    CL_CM_8_settings,
]

# CL_CM_9: STRICT IMPLICATION TO GROUND
CL_CM_9_premises = ['\\Box (A \\rightarrow B)']
CL_CM_9_conclusions = ['(A \\leq B)']
CL_CM_9_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 2,
    'expectation': True,
}
CL_CM_9_example = [
    CL_CM_9_premises,
    CL_CM_9_conclusions,
    CL_CM_9_settings,
]

# CL_CM_10: STRICT IMPLICATION TO ESSENCE
CL_CM_10_premises = ['\\Box (B \\rightarrow A)']
CL_CM_10_conclusions = ['(A \\sqsubseteq B)']
CL_CM_10_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CL_CM_10_example = [
    CL_CM_10_premises,
    CL_CM_10_conclusions,
    CL_CM_10_settings,
]

# CL_CM_11: ESSENCE DISTRIBUTION
CL_CM_11_premises = []
CL_CM_11_conclusions = ['(((A \\vee B) \\wedge (A \\vee C)) \\sqsubseteq (A \\vee (B \\wedge C)))']
CL_CM_11_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CL_CM_11_example = [
    CL_CM_11_premises,
    CL_CM_11_conclusions,
    CL_CM_11_settings,
]

# CL_CM_12: GROUND DISTRIBUTION
CL_CM_12_premises = []
CL_CM_12_conclusions = ['(((A \\wedge B) \\vee (A \\wedge C)) \\leq (A \\wedge (B \\vee C)))']
CL_CM_12_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CL_CM_12_example = [
    CL_CM_12_premises,
    CL_CM_12_conclusions,
    CL_CM_12_settings,
]

# CL_CM_13: SHANNON EXPANSION
CL_CM_13_premises = []
CL_CM_13_conclusions = ['(A \\equiv ((A \\wedge B) \\vee (A \\wedge \\neg B)))']
CL_CM_13_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CL_CM_13_example = [
    CL_CM_13_premises,
    CL_CM_13_conclusions,
    CL_CM_13_settings,
]

# CL_CM_14: DUAL SHANNON EXPANSION
CL_CM_14_premises = []
CL_CM_14_conclusions = ['(A \\equiv ((A \\vee B) \\wedge (A \\vee \\neg B)))']
CL_CM_14_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CL_CM_14_example = [
    CL_CM_14_premises,
    CL_CM_14_conclusions,
    CL_CM_14_settings,
]






################
### THEOREMS ###
################

# CL_TH_1: GROUND TO ESSENCE
CL_TH_1_premises = ['(A \\leq B)']
CL_TH_1_conclusions = ['(\\neg A \\sqsubseteq \\neg B)']
CL_TH_1_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_1_example = [
    CL_TH_1_premises,
    CL_TH_1_conclusions,
    CL_TH_1_settings,
]

# CL_TH_2: ESSENCE TO GROUND 
CL_TH_2_premises = ['(A \\sqsubseteq B)']
CL_TH_2_conclusions = ['(\\neg A \\leq \\neg B)']
CL_TH_2_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_2_example = [
    CL_TH_2_premises,
    CL_TH_2_conclusions,
    CL_TH_2_settings,
]

# CL_TH_3: ESSENCE TO IDENTITY
CL_TH_3_premises = ['(A \\sqsubseteq B)']
CL_TH_3_conclusions = ['((A \\wedge B) \\equiv B)']
CL_TH_3_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_3_example = [
    CL_TH_3_premises,
    CL_TH_3_conclusions,
    CL_TH_3_settings,
]

# CL_TH_4: IDENTITY TO ESSENCE 
CL_TH_4_premises = ['((A \\wedge B) \\equiv B)']
CL_TH_4_conclusions = ['(A \\sqsubseteq B)']
CL_TH_4_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_4_example = [
    CL_TH_4_premises,
    CL_TH_4_conclusions,
    CL_TH_4_settings,
]

# CL_TH_5: GROUND TO IDENTITY
CL_TH_5_premises = ['(A \\leq B)']
CL_TH_5_conclusions = ['((A \\vee B) \\equiv B)']
CL_TH_5_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_5_example = [
    CL_TH_5_premises,
    CL_TH_5_conclusions,
    CL_TH_5_settings,
]

# CL_TH_6: IDENTITY TO GROUND 
CL_TH_6_premises = ['((A \\vee B) \\equiv B)']
CL_TH_6_conclusions = ['(A \\leq B)']
CL_TH_6_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_6_example = [
    CL_TH_6_premises,
    CL_TH_6_conclusions,
    CL_TH_6_settings,
]

# CL_TH_7: NEGATION TRANSPARENCY
CL_TH_7_premises = ['(A \\equiv B)']
CL_TH_7_conclusions = ['(\\neg A \\equiv \\neg B)']
CL_TH_7_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_7_example = [
    CL_TH_7_premises,
    CL_TH_7_conclusions,
    CL_TH_7_settings,
]

# CL_TH_8: REVERSE NEGATION TRANSPARENCY
CL_TH_8_premises = ['(\\neg A \\equiv \\neg B)']
CL_TH_8_conclusions = ['(A \\equiv B)']
CL_TH_8_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_8_example = [
    CL_TH_8_premises,
    CL_TH_8_conclusions,
    CL_TH_8_settings,
]

# CL_TH_9: ABSORPTION IDENTITY
CL_TH_9_premises = ['(A \\vee (A \\wedge B))']
CL_TH_9_conclusions = ['(A \\wedge (A \\vee B))']
CL_TH_9_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_9_example = [
    CL_TH_9_premises,
    CL_TH_9_conclusions,
    CL_TH_9_settings,
]

# CL_TH_10: ABSORPTION REDUCTION: CONJUNCTION OVER DISJUNCTION
CL_TH_10_premises = []
CL_TH_10_conclusions = ['(A \\Rightarrow (A \\wedge (A \\vee B)))']
CL_TH_10_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_10_example = [
    CL_TH_10_premises,
    CL_TH_10_conclusions,
    CL_TH_10_settings,
]

# CL_TH_11: ABSORPTION REDUCTION: DISJUNCTION OVER CONJUNCTION
CL_TH_11_premises = []
CL_TH_11_conclusions = ['(A \\Rightarrow (A \\vee (A \\wedge B)))']
CL_TH_11_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_11_example = [
    CL_TH_11_premises,
    CL_TH_11_conclusions,
    CL_TH_11_settings,
]

# CL_TH_12: DISTRIBUTION REDUCTION: DISJUNCTION OVER CONJUNCTION
CL_TH_12_premises = []
CL_TH_12_conclusions = ['((A \\vee (A \\wedge B)) \\Rightarrow (A \\wedge (A \\vee B)))']
CL_TH_12_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_12_example = [
    CL_TH_12_premises,
    CL_TH_12_conclusions,
    CL_TH_12_settings,
]

# CL_TH_13: DISTRIBUTION REDUCTION: CONJUNCTION OVER DISJUNCTION
CL_TH_13_premises = []
CL_TH_13_conclusions = ['((A \\wedge (A \\vee B)) \\Rightarrow (A \\vee (A \\wedge B)))']
CL_TH_13_settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_13_example = [
    CL_TH_13_premises,
    CL_TH_13_conclusions,
    CL_TH_13_settings,
]

# CL_TH_14: GROUND TO STRICT IMPLICATION
CL_TH_14_premises = ['(A \\leq B)']
CL_TH_14_conclusions = ['\\Box (A \\rightarrow B)']
CL_TH_14_settings = {
    'N': 4,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_14_example = [
    CL_TH_14_premises,
    CL_TH_14_conclusions,
    CL_TH_14_settings,
]

# CL_TH_15: ESSENCE TO CONVERSE STRICT IMPLICATION
CL_TH_15_premises = ['(A \\sqsubseteq B)']
CL_TH_15_conclusions = ['\\Box (B \\rightarrow A)']
CL_TH_15_settings = {
    'N': 4,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_15_example = [
    CL_TH_15_premises,
    CL_TH_15_conclusions,
    CL_TH_15_settings,
]

# CL_TH_16: GROUNDING ANTI-SYMMETRY
CL_TH_16_premises = ['(A \\leq B)', '(B \\leq A)']
CL_TH_16_conclusions = ['(A \\equiv B)']
CL_TH_16_settings = {
    'N': 2,
    'M': 2,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 2,
    'expectation': False,
}
CL_TH_16_example = [
    CL_TH_16_premises,
    CL_TH_16_conclusions,
    CL_TH_16_settings,
]

# CL_TH_17: ESSENCE ANTI-SYMMETRY
CL_TH_17_premises = ['(A \\sqsubseteq B)', '(B \\sqsubseteq A)']
CL_TH_17_conclusions = ['(A \\equiv B)']
CL_TH_17_settings = {
    'N': 2,
    'M': 2,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 2,
    'expectation': False,
}
CL_TH_17_example = [
    CL_TH_17_premises,
    CL_TH_17_conclusions,
    CL_TH_17_settings,
]

# CL_TH_18: GROUNDING TRANSITIVITY
CL_TH_18_premises = ['(A \\leq B)', '(B \\leq C)']
CL_TH_18_conclusions = ['(A \\leq C)']
CL_TH_18_settings = {
    'N': 2,
    'M': 2,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 2,
    'expectation': False,
}
CL_TH_18_example = [
    CL_TH_18_premises,
    CL_TH_18_conclusions,
    CL_TH_18_settings,
]

# CL_TH_19: ESSENCE TRANSITIVITY
CL_TH_19_premises = ['(A \\sqsubseteq B)', '(B \\sqsubseteq C)']
CL_TH_19_conclusions = ['(A \\sqsubseteq C)']
CL_TH_19_settings = {
    'N': 2,
    'M': 2,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 2,
    'expectation': False,
}
CL_TH_19_example = [
    CL_TH_19_premises,
    CL_TH_19_conclusions,
    CL_TH_19_settings,
]

# CL_TH_20: ABSORPTION DUALITY
CL_TH_20_premises = []
CL_TH_20_conclusions = ['((A \\vee (A \\wedge B)) \\equiv (A \\wedge (A \\vee B)))']
CL_TH_20_settings = {
    'N': 4,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CL_TH_20_example = [
    CL_TH_20_premises,
    CL_TH_20_conclusions,
    CL_TH_20_settings,
]

#####################
### RELEVANCE (\\preceq)
#####################
#
# Absorbed from the former relevance subtheory: RelevanceOperator (\\preceq) is
# defined and registered in this module (see RelevanceOperator above), so its
# examples live alongside the other constitutive-family examples rather than
# in a separate subtheory that contributed zero operators of its own.

# REL_CM_1: ANTECEDENT STRENGTHENING
REL_CM_1_premises = []
REL_CM_1_conclusions = ['((A \\wedge B) \\preceq A)']
REL_CM_1_settings = {
    'N': 4,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 2,
    'expectation': True,
}
REL_CM_1_example = [
    REL_CM_1_premises,
    REL_CM_1_conclusions,
    REL_CM_1_settings,
]

# REL_CM_2: ANTECEDENT WEAKENING
REL_CM_2_premises = []
REL_CM_2_conclusions = ['((A \\vee B) \\preceq A)']
REL_CM_2_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
REL_CM_2_example = [
    REL_CM_2_premises,
    REL_CM_2_conclusions,
    REL_CM_2_settings,
]

# REL_CM_3: RELEVANCE TRANSITIVITY
REL_CM_3_premises = ['(A \\preceq B)', '(B \\preceq C)']
REL_CM_3_conclusions = ['(A \\preceq C)']
REL_CM_3_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
REL_CM_3_example = [
    REL_CM_3_premises,
    REL_CM_3_conclusions,
    REL_CM_3_settings,
]

# REL_CM_4: RELEVANT IMPLICATION: GROUND
REL_CM_4_premises = ['\\Box (A \\rightarrow B)', '(A \\preceq B)']
REL_CM_4_conclusions = ['(A \\leq B)']
REL_CM_4_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
REL_CM_4_example = [
    REL_CM_4_premises,
    REL_CM_4_conclusions,
    REL_CM_4_settings,
]

# REL_CM_5: RELEVANT IMPLICATION: ESSENCE
REL_CM_5_premises = ['\\Box (B \\rightarrow A)', '(A \\preceq B)']
REL_CM_5_conclusions = ['(A \\sqsubseteq B)']
REL_CM_5_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
REL_CM_5_example = [
    REL_CM_5_premises,
    REL_CM_5_conclusions,
    REL_CM_5_settings,
]

# REL_CM_6: RELEVANT IMPLICATION: IDENTITY
REL_CM_6_premises = ['\\Box (A \\leftrightarrow B)', '(A \\preceq B)', '(B \\preceq A)']
REL_CM_6_conclusions = ['(A \\equiv B)']
REL_CM_6_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
REL_CM_6_example = [
    REL_CM_6_premises,
    REL_CM_6_conclusions,
    REL_CM_6_settings,
]

# REL_CM_7: STRICT IMPLICATION
REL_CM_7_premises = ['\\Box (A \\rightarrow B)']
REL_CM_7_conclusions = ['(A \\preceq B)']
REL_CM_7_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
REL_CM_7_example = [
    REL_CM_7_premises,
    REL_CM_7_conclusions,
    REL_CM_7_settings,
]

# REL_CM_8: REVERSE DISTRIBUTION: DISJUNCTION OVER CONJUNCTION
REL_CM_8_premises = []
REL_CM_8_conclusions = ['(((A \\vee B) \\wedge (A \\vee C)) \\preceq (A \\vee (B \\wedge C)))']
REL_CM_8_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
REL_CM_8_example = [
    REL_CM_8_premises,
    REL_CM_8_conclusions,
    REL_CM_8_settings,
]

# REL_CM_9: REVERSE DISTRIBUTION: CONJUNCTION OVER DISJUNCTION
REL_CM_9_premises = []
REL_CM_9_conclusions = ['(((A \\wedge B) \\vee (A \\wedge C)) \\preceq (A \\wedge (B \\vee C)))']
REL_CM_9_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
REL_CM_9_example = [
    REL_CM_9_premises,
    REL_CM_9_conclusions,
    REL_CM_9_settings,
]

# REL_CM_10: CONJUNCTION INTRODUCTION
REL_CM_10_premises = ['(A \\preceq B)']
REL_CM_10_conclusions = ['(A \\preceq (B \\wedge C))']
REL_CM_10_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
REL_CM_10_example = [
    REL_CM_10_premises,
    REL_CM_10_conclusions,
    REL_CM_10_settings,
]

# REL_CM_11: DISJUNCTION INTRODUCTION
REL_CM_11_premises = ['(A \\preceq B)']
REL_CM_11_conclusions = ['(A \\preceq (B \\vee C))']
REL_CM_11_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
REL_CM_11_example = [
    REL_CM_11_premises,
    REL_CM_11_conclusions,
    REL_CM_11_settings,
]

# REL_TH_1: RELEVANCE TO CONJUNCTION
REL_TH_1_premises = ['(A \\preceq B)']
REL_TH_1_conclusions = ['((A \\wedge B) \\leq B)']
REL_TH_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
REL_TH_1_example = [
    REL_TH_1_premises,
    REL_TH_1_conclusions,
    REL_TH_1_settings,
]

# REL_TH_2: RELEVANCE TO DISJUNCTION
REL_TH_2_premises = ['(A \\preceq B)']
REL_TH_2_conclusions = ['((A \\vee B) \\sqsubseteq B)']
REL_TH_2_settings = {
    'N': 3,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
REL_TH_2_example = [
    REL_TH_2_premises,
    REL_TH_2_conclusions,
    REL_TH_2_settings,
]

# REL_TH_3: CONJUNCTION TO RELEVANCE
REL_TH_3_premises = ['((A \\wedge B) \\leq B)']
REL_TH_3_conclusions = ['(A \\preceq B)']
REL_TH_3_settings = {
    'N': 3,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
REL_TH_3_example = [
    REL_TH_3_premises,
    REL_TH_3_conclusions,
    REL_TH_3_settings,
]

# REL_TH_4: DISJUNCTION TO RELEVANCE
REL_TH_4_premises = ['((A \\vee B) \\sqsubseteq B)']
REL_TH_4_conclusions = ['(A \\preceq B)']
REL_TH_4_settings = {
    'N': 3,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
REL_TH_4_example = [
    REL_TH_4_premises,
    REL_TH_4_conclusions,
    REL_TH_4_settings,
]

# REL_TH_5: CONJUNCTION INTRODUCTION
REL_TH_5_premises = []
REL_TH_5_conclusions = ['(A \\preceq (A \\wedge B))']
REL_TH_5_settings = {
    'N': 3,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
REL_TH_5_example = [
    REL_TH_5_premises,
    REL_TH_5_conclusions,
    REL_TH_5_settings,
]

# REL_TH_6: DISJUNCTION INTRODUCTION
REL_TH_6_premises = []
REL_TH_6_conclusions = ['(A \\preceq (A \\vee B))']
REL_TH_6_settings = {
    'N': 3,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
REL_TH_6_example = [
    REL_TH_6_premises,
    REL_TH_6_conclusions,
    REL_TH_6_settings,
]

# REL_TH_7: GROUNDING RELEVANCE
REL_TH_7_premises = ['(A \\leq B)']
REL_TH_7_conclusions = ['(A \\preceq B)']
REL_TH_7_settings = {
    'N': 3,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
REL_TH_7_example = [
    REL_TH_7_premises,
    REL_TH_7_conclusions,
    REL_TH_7_settings,
]

# REL_TH_8: ESSENCE RELEVANCE
REL_TH_8_premises = ['(A \\sqsubseteq B)']
REL_TH_8_conclusions = ['(A \\preceq B)']
REL_TH_8_settings = {
    'N': 3,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
REL_TH_8_example = [
    REL_TH_8_premises,
    REL_TH_8_conclusions,
    REL_TH_8_settings,
]

# REL_TH_9: IDENTITY RELEVANCE
REL_TH_9_premises = ['(A \\equiv B)']
REL_TH_9_conclusions = ['(A \\preceq B)']
REL_TH_9_settings = {
    'N': 3,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
REL_TH_9_example = [
    REL_TH_9_premises,
    REL_TH_9_conclusions,
    REL_TH_9_settings,
]




# Create collections for different constitutive example types
constitutive_cm_examples = {
    "CL_CM_1": CL_CM_1_example,   # EQUIVALENCE OF TAUTOLOGIES
    "CL_CM_2": CL_CM_2_example,   # EQUIVALENCE OF CONTRADICTIONS
    "CL_CM_3": CL_CM_3_example,   # GROUND CONJUNCTION SUPPLEMENTATION
    "CL_CM_4": CL_CM_4_example,   # ESSENCE DISJUNCTION SUPPLEMENTATION
    "CL_CM_5": CL_CM_5_example,   # IDENTITY ABSORPTION: DISJUNCTION OVER CONJUNCTION
    "CL_CM_6": CL_CM_6_example,   # IDENTITY ABSORPTION: CONJUNCTION OVER DISJUNCTION
    "CL_CM_7": CL_CM_7_example,   # IDENTITY DISTRIBUTION: CONJUNCTION OVER DISJUNCTION
    "CL_CM_8": CL_CM_8_example,   # IDENTITY DISTRIBUTION: DISJUNCTION OVER CONJUNCTION
    "CL_CM_9": CL_CM_9_example,   # STRICT IMPLICATION TO GROUND
    "CL_CM_10": CL_CM_10_example, # STRICT IMPLICATION TO ESSENCE
    "CL_CM_11": CL_CM_11_example, # ESSENCE DISTRIBUTION
    "CL_CM_12": CL_CM_12_example, # GROUND DISTRIBUTION
    "CL_CM_13": CL_CM_13_example, # SHANNON EXPANSION
    "CL_CM_14": CL_CM_14_example, # DUAL SHANNON EXPANSION
}

constitutive_th_examples = {
    "CL_TH_1": CL_TH_1_example,   # GROUND TO ESSENCE
    "CL_TH_2": CL_TH_2_example,   # ESSENCE TO GROUND
    "CL_TH_3": CL_TH_3_example,   # ESSENCE TO IDENTITY
    "CL_TH_4": CL_TH_4_example,   # IDENTITY TO ESSENCE
    "CL_TH_5": CL_TH_5_example,   # GROUND TO IDENTITY
    "CL_TH_6": CL_TH_6_example,   # IDENTITY TO GROUND
    "CL_TH_7": CL_TH_7_example,   # NEGATION TRANSPARENCY
    "CL_TH_8": CL_TH_8_example,   # REVERSE NEGATION TRANSPARENCY
    "CL_TH_9": CL_TH_9_example,   # ABSORPTION IDENTITY
    "CL_TH_10": CL_TH_10_example, # ABSORPTION REDUCTION: CONJUNCTION OVER DISJUNCTION
    "CL_TH_11": CL_TH_11_example, # ABSORPTION REDUCTION: DISJUNCTION OVER CONJUNCTION
    "CL_TH_12": CL_TH_12_example, # DISTRIBUTION REDUCTION: DISJUNCTION OVER CONJUNCTION
    "CL_TH_13": CL_TH_13_example, # DISTRIBUTION REDUCTION: CONJUNCTION OVER DISJUNCTION
    "CL_TH_14": CL_TH_14_example, # GROUND TO STRICT IMPLICATION
    "CL_TH_15": CL_TH_15_example, # ESSENCE TO CONVERSE STRICT IMPLICATION
    "CL_TH_16": CL_TH_16_example, # GROUNDING ANTI-SYMMETRY
    "CL_TH_17": CL_TH_17_example, # ESSENCE ANTI-SYMMETRY
    "CL_TH_18": CL_TH_18_example, # GROUNDING TRANSITIVITY
    "CL_TH_19": CL_TH_19_example, # ESSENCE TRANSITIVITY
    "CL_TH_20": CL_TH_20_example, # ABSORPTION DUALITY
}

# Relevance countermodels and theorems, absorbed from the former relevance
# subtheory (see the RELEVANCE section above). Kept in separate dicts, with
# their REL_ prefixes intact, so their provenance stays legible.
relevance_cm_examples = {
    "REL_CM_1": REL_CM_1_example,
    "REL_CM_2": REL_CM_2_example,
    "REL_CM_3": REL_CM_3_example,
    "REL_CM_4": REL_CM_4_example,
    "REL_CM_5": REL_CM_5_example,
    "REL_CM_6": REL_CM_6_example,
    "REL_CM_7": REL_CM_7_example,
    "REL_CM_8": REL_CM_8_example,
    "REL_CM_9": REL_CM_9_example,
    "REL_CM_10": REL_CM_10_example,
    "REL_CM_11": REL_CM_11_example,
}

relevance_th_examples = {
    "REL_TH_1": REL_TH_1_example,
    "REL_TH_2": REL_TH_2_example,
    "REL_TH_3": REL_TH_3_example,
    "REL_TH_4": REL_TH_4_example,
    "REL_TH_5": REL_TH_5_example,
    "REL_TH_6": REL_TH_6_example,
    "REL_TH_7": REL_TH_7_example,
    "REL_TH_8": REL_TH_8_example,
    "REL_TH_9": REL_TH_9_example,
}

# Combined collection of all constitutive examples (including the absorbed
# relevance examples)
unit_tests = {
    **constitutive_cm_examples,
    **constitutive_th_examples,
    **relevance_cm_examples,
    **relevance_th_examples,
}

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Create operator registry for constitutive theory
constitutive_registry = LogosOperatorRegistry()
constitutive_registry.load_subtheories(['extensional', 'constitutive', 'modal'])

# Define the semantic theory
constitutive_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": constitutive_registry.get_operators(),
}

# Specify which theories to use
semantic_theories = {
    "Brast-McKie": constitutive_theory,
}

# # Specify which examples to run by default when running this module directly
# # All examples included by default
# example_range = constitutive_examples

# Or specify particular examples to run
example_range = {

    # COUNTERMODELS
    # "CL_CM_1": CL_CM_1_example,   # EQUIVALENCE OF TAUTOLOGIES
    # "CL_CM_2": CL_CM_2_example,   # EQUIVALENCE OF CONTRADICTIONS
    # "CL_CM_3": CL_CM_3_example,   # GROUND CONJUNCTION SUPPLEMENTATION
    # "CL_CM_4": CL_CM_4_example,   # ESSENCE DISJUNCTION SUPPLEMENTATION
    # "CL_CM_5": CL_CM_5_example,   # IDENTITY ABSORPTION: DISJUNCTION OVER CONJUNCTION
    # "CL_CM_6": CL_CM_6_example,   # IDENTITY ABSORPTION: CONJUNCTION OVER DISJUNCTION
    "CL_CM_7": CL_CM_7_example,   # IDENTITY DISTRIBUTION: CONJUNCTION OVER DISJUNCTION
    "CL_CM_8": CL_CM_8_example,   # IDENTITY DISTRIBUTION: DISJUNCTION OVER CONJUNCTION
    # "CL_CM_9": CL_CM_9_example,   # STRICT IMPLICATION TO GROUND
    # "CL_CM_10": CL_CM_10_example, # STRICT IMPLICATION TO ESSENCE
    # "CL_CM_11": CL_CM_11_example, # ESSENCE DISTRIBUTION
    # "CL_CM_12": CL_CM_12_example, # GROUND DISTRIBUTION
    # "CL_CM_13": CL_CM_13_example, # SHANNON EXPANSION
    # "CL_CM_14": CL_CM_14_example, # DUAL SHANNON EXPANSION

    # THEOREMS
    # "CL_TH_1": CL_TH_1_example,   # GROUND TO ESSENCE
    # "CL_TH_2": CL_TH_2_example,   # ESSENCE TO GROUND
    # "CL_TH_3": CL_TH_3_example,   # ESSENCE TO IDENTITY
    # "CL_TH_4": CL_TH_4_example,   # IDENTITY TO ESSENCE
    # "CL_TH_5": CL_TH_5_example,   # GROUND TO IDENTITY
    # "CL_TH_6": CL_TH_6_example,   # IDENTITY TO GROUND
    # "CL_TH_7": CL_TH_7_example,   # NEGATION TRANSPARENCY
    # "CL_TH_8": CL_TH_8_example,   # REVERSE NEGATION TRANSPARENCY
    # "CL_TH_9": CL_TH_9_example,   # ABSORPTION IDENTITY
    # "CL_TH_10": CL_TH_10_example, # ABSORPTION REDUCTION: CONJUNCTION OVER DISJUNCTION
    # "CL_TH_11": CL_TH_11_example, # ABSORPTION REDUCTION: DISJUNCTION OVER CONJUNCTION
    # "CL_TH_12": CL_TH_12_example, # DISTRIBUTION REDUCTION: DISJUNCTION OVER CONJUNCTION
    # "CL_TH_13": CL_TH_13_example, # DISTRIBUTION REDUCTION: CONJUNCTION OVER DISJUNCTION
    # "CL_TH_14": CL_TH_14_example, # GROUND TO STRICT IMPLICATION
    # "CL_TH_15": CL_TH_15_example, # ESSENCE TO CONVERSE STRICT IMPLICATION
    # "CL_TH_16": CL_TH_16_example, # GROUNDING ANTI-SYMMETRY
    # "CL_TH_17": CL_TH_17_example, # ESSENCE ANTI-SYMMETRY
    # "CL_TH_18": CL_TH_18_example, # GROUNDING TRANSITIVITY
    # "CL_TH_19": CL_TH_19_example, # ESSENCE TRANSITIVITY
    # "CL_TH_20": CL_TH_20_example, # ABSORPTION DUALITY

    # RELEVANCE COUNTERMODELS (absorbed from the former relevance subtheory)
    "REL_CM_1": REL_CM_1_example,  # ANTECEDENT STRENGTHENING
    "REL_CM_2": REL_CM_2_example,  # ANTECEDENT WEAKENING
    # "REL_CM_3": REL_CM_3_example,  # RELEVANCE TRANSITIVITY
    # "REL_CM_4": REL_CM_4_example,  # RELEVANT IMPLICATION: GROUND
    # "REL_CM_5": REL_CM_5_example,  # RELEVANT IMPLICATION: ESSENCE
    # "REL_CM_6": REL_CM_6_example,  # RELEVANT IMPLICATION: IDENTITY
    # "REL_CM_7": REL_CM_7_example,  # STRICT IMPLICATION
    # "REL_CM_8": REL_CM_8_example,  # REVERSE DISTRIBUTION: DISJUNCTION OVER CONJUNCTION
    # "REL_CM_9": REL_CM_9_example,  # REVERSE DISTRIBUTION: CONJUNCTION OVER DISJUNCTION
    # "REL_CM_10": REL_CM_10_example,  # CONJUNCTION INTRODUCTION
    # "REL_CM_11": REL_CM_11_example,  # DISJUNCTION INTRODUCTION

    # RELEVANCE THEOREMS (absorbed from the former relevance subtheory)
    "REL_TH_1": REL_TH_1_example,  # RELEVANCE TO CONJUNCTION
    "REL_TH_2": REL_TH_2_example,  # RELEVANCE TO DISJUNCTION
    # "REL_TH_3": REL_TH_3_example,  # CONJUNCTION TO RELEVANCE
    # "REL_TH_4": REL_TH_4_example,  # DISJUNCTION TO RELEVANCE
    # "REL_TH_5": REL_TH_5_example,  # CONJUNCTION INTRODUCTION
    # "REL_TH_6": REL_TH_6_example,  # DISJUNCTION INTRODUCTION
    # "REL_TH_7": REL_TH_7_example,  # GROUNDING RELEVANCE
    # "REL_TH_8": REL_TH_8_example,  # ESSENCE RELEVANCE
    # "REL_TH_9": REL_TH_9_example,  # IDENTITY RELEVANCE

}

# Make this module runnable from the command line
if __name__ == '__main__':
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_parent_dir)
