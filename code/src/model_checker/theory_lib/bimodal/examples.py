"""
Examples Module for Bimodal Logic Theory

This module provides a comprehensive collection of test cases for bimodal semantic theory,
which combines temporal and modal operators to reason about what is true
at different times and in different possible worlds.

Usage:
------
This module can be run in two ways:

1. Command Line:
   ```bash
   model-checker path/to/this/examples.py
   ```

2. IDE (VSCodium/VSCode):
   - Open this file in VSCodium/VSCode
   - Use the "Run Python File" play button in the top-right corner
   - Or right-click in the editor and select "Run Python File"

Configuration:
-------------
The examples and theories to be run can be configured by:

1. Modifying which examples are run:
   - Edit the example_range dictionary
   - Comment/uncomment specific examples
   - Modify semantic_theories to change which theories to compare

2. To add new examples:
   - Define premises, conclusions, and settings
   - Follow the naming conventions:
     - Countermodels: EX_CM_*, MD_CM_*, TN_CM_*, BM_CM_*
     - Theorems: EX_TH_*, MD_TH_*, TN_TH_*, BM_TH_*
   - Add to example_range dictionary

Module Structure:
----------------
1. Imports:
   - System utilities (os, sys)
   - Local semantic definitions (BimodalSemantics, BimodalProposition, BimodalStructure)
   - Local operator definitions (bimodal_operators)

2. Semantic Theory:
   - bimodal_theory: Bimodal semantic framework configuration

3. Example Categories:
   - Extensional (EX_CM_*, EX_TH_*): Basic logical operations
   - Modal (MD_CM_*, MD_TH_*): Necessity and possibility operators
   - Tense (TN_CM_*, TN_TH_*): Temporal operators
   - Bimodal (BM_CM_*, BM_TH_*): Combined modal and temporal operators

4. Example Collections:
   - semantic_theories: Available semantic theory implementations
   - test_example_range: Complete set of test cases
   - example_range: Active subset of test cases for execution

Example Format:
--------------
Each example is structured as a list: [premises, conclusions, settings]
- premises: List of formulas that serve as assumptions
- conclusions: List of formulas to be tested
- settings: Dictionary of specific settings for this example

Settings Options:
----------------
- N: Number of atomic propositions (default: 1)
- M: Number of time points (default: 1)
- contingent: Whether to use contingent valuations
- disjoint: Whether to enforce disjoint valuations
- max_time: Maximum computation time in seconds
- expectation: Whether the example is expected to be valid

Notes:
------
- At least one semantic theory must be included in semantic_theories
- At least one example must be included in example_range
- Some examples may require adjusting the settings to produce good models

Help:
-----
More information can be found in the README.md for the bimodal theory.
"""

##########################
### DEFINE THE IMPORTS ###
##########################

# Standard imports
import sys
import os

# Add current directory to path before importing modules
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

from .semantic import (
    BimodalStructure,
    BimodalSemantics,
    BimodalProposition,
)
from .operators import bimodal_operators

#######################
### DEFAULT SETTINGS ###
#######################

general_settings = {
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
    "align_vertically": False,
}



####################################
### DEFINE THE SEMANTIC THEORIES ###
####################################

bimodal_theory = {
    "semantics": BimodalSemantics,
    "proposition": BimodalProposition,
    "model": BimodalStructure,
    "operators": bimodal_operators,
    # translation dictionary is only required for comparison theories
}



##############################################################################
############################### COUNTERMODELS ################################
##############################################################################

#################################
### EXTENSIONAL COUNTERMODELS ###
#################################

# EX_CM_1: DISJUNCTION TO CONJUNCTION
EX_CM_1_premises = ['(A \\vee B)']
EX_CM_1_conclusions = ['(A \\wedge B)']
EX_CM_1_settings = {
    'N' : 2,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,
    'expectation' : True,
}
EX_CM_1_example = [
    EX_CM_1_premises,
    EX_CM_1_conclusions,
    EX_CM_1_settings,
]



###########################
### MODAL COUNTERMODELS ###
###########################

# MD_CM_1: DISTRIBUTE NECESSITY OVER DISJUNCTION
MD_CM_1_premises = ['\\Box (A \\vee B)']
MD_CM_1_conclusions = ['\\Box A', '\\Box B']
MD_CM_1_settings = {
    'N' : 2,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : True,
}
MD_CM_1_example = [
    MD_CM_1_premises,
    MD_CM_1_conclusions,
    MD_CM_1_settings,
]

# MD_CM_2: DISTRIBUTE POSSIBILITY OVER CONJUNCTION
MD_CM_2_premises = ['\\Diamond (A \\vee B)']
MD_CM_2_conclusions = ['(\\Diamond A \\wedge \\Diamond B)']
MD_CM_2_settings = {
    'N' : 2,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
MD_CM_2_example = [
    MD_CM_2_premises,
    MD_CM_2_conclusions,
    MD_CM_2_settings,
]

# MD_CM_3: ACTUALITY TO NECESSITY
MD_CM_3_premises = ['A']
MD_CM_3_conclusions = ['\\Box A']
MD_CM_3_settings = {
    'N' : 2,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
MD_CM_3_example = [
    MD_CM_3_premises,
    MD_CM_3_conclusions,
    MD_CM_3_settings,
]

# MD_CM_4: POSSIBILITY TO ACTUALITY
MD_CM_4_premises = ['\\Diamond A']
MD_CM_4_conclusions = ['A']
MD_CM_4_settings = {
    'N' : 2,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
MD_CM_4_example = [
    MD_CM_4_premises,
    MD_CM_4_conclusions,
    MD_CM_4_settings,
]

# MD_CM_5: POSSIBILITY TO NECESSITY
MD_CM_5_premises = ['\\Diamond A']
MD_CM_5_conclusions = ['\\Box A']
MD_CM_5_settings = {
    'N' : 2,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
MD_CM_5_example = [
    MD_CM_5_premises,
    MD_CM_5_conclusions,
    MD_CM_5_settings,
]

# MD_CM_6: INCOMPATIBLE POSSIBILITIES
MD_CM_6_premises = ['\\Diamond A', '\\Diamond B']
MD_CM_6_conclusions = ['\\Diamond (A \\wedge B)']
MD_CM_6_settings = {
    'N' : 2,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
MD_CM_6_example = [
    MD_CM_6_premises,
    MD_CM_6_conclusions,
    MD_CM_6_settings,
]



###########################
### TENSE COUNTERMODELS ###
###########################

# TN_CM_1: 
TN_CM_1_premises = ['A']
TN_CM_1_conclusions = ['\\Future A']
TN_CM_1_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : True,
}
TN_CM_1_example = [
    TN_CM_1_premises,
    TN_CM_1_conclusions,
    TN_CM_1_settings,
]

# TN_CM_2: 
TN_CM_2_premises = ['\\future A', '\\future B']
TN_CM_2_conclusions = ['\\future (A \\wedge B)']
TN_CM_2_settings = {
    'N' : 2,
    'M' : 3,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,
    'expectation' : True,
}
TN_CM_2_example = [
    TN_CM_2_premises,
    TN_CM_2_conclusions,
    TN_CM_2_settings,
]




#############################
### BIMODAL COUNTERMODELS ###
#############################

# TN_CM_1: ALL FUTURE TO NECESSITY
BM_CM_1_premises = ['\\Future A']
BM_CM_1_conclusions = ['\\Box A']
BM_CM_1_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : True,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : True,
}
BM_CM_1_example = [
    BM_CM_1_premises,
    BM_CM_1_conclusions,
    BM_CM_1_settings,
]

# TN_CM_2: ALL PAST TO NECESSITY
BM_CM_2_premises = ['\\Past A']
BM_CM_2_conclusions = ['\\Box A']
BM_CM_2_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : True,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : True,
}
BM_CM_2_example = [
    BM_CM_2_premises,
    BM_CM_2_conclusions,
    BM_CM_2_settings,
]

# MD_CM_3: POSSIBILITY TO SOME FUTURE
BM_CM_3_premises = ['\\Diamond A']
BM_CM_3_conclusions = ['\\future A']
BM_CM_3_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : True,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,
}
BM_CM_3_example = [
    BM_CM_3_premises,
    BM_CM_3_conclusions,
    BM_CM_3_settings,
]

# MD_CM_4: POSSIBILITY TO SOME PAST
BM_CM_4_premises = ['\\Diamond A']
BM_CM_4_conclusions = ['\\past A']
BM_CM_4_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : True,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : True,
}
BM_CM_4_example = [
    BM_CM_4_premises,
    BM_CM_4_conclusions,
    BM_CM_4_settings,
]





##############################################################################
################################## THEOREMS ##################################
##############################################################################

############################
### EXTENSIONAL THEOREMS ###
############################

# EX_TH_1: CONJUNCTION TO DISJUNCTION 
EX_TH_1_premises = ['(A \\wedge B)']
EX_TH_1_conclusions = ['(A \\vee B)']
EX_TH_1_settings = {
    'N' : 2,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : False,
}
EX_TH_1_example = [
    EX_TH_1_premises,
    EX_TH_1_conclusions,
    EX_TH_1_settings,
]



######################
### MODAL THEOREMS ###
######################

# MD_TH_1: NECESSITY DISTRIBUTE OVER IMPLICATION
MD_TH_1_premises = ['\\Box (A \\rightarrow B)']
MD_TH_1_conclusions = ['(\\Box A \\rightarrow \\Box B)']
MD_TH_1_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : False,
}
MD_TH_1_example = [
    MD_TH_1_premises,
    MD_TH_1_conclusions,
    MD_TH_1_settings,
]

# MD_TH_2: TEST CONTINGENCY SETTING
MD_TH_2_premises = ['\\Box A']
MD_TH_2_conclusions = ['A']
MD_TH_2_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : True,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : False,
}
MD_TH_2_example = [
    MD_TH_2_premises,
    MD_TH_2_conclusions,
    MD_TH_2_settings,
]



######################
### TENSE THEOREMS ###
######################

# MD_TH_2: 
TN_TH_2_premises = ['A']
TN_TH_2_conclusions = ['\\Future \\past A']
TN_TH_2_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : False,
}
TN_TH_2_example = [
    TN_TH_2_premises,
    TN_TH_2_conclusions,
    TN_TH_2_settings,
]



########################
### BIMODAL THEOREMS ###
########################

# BM_TH_1: NECESSITY TO ALL FUTURE (PERPETUITY)
# NOTE: Under strict semantics (ProofChecker-aligned), atoms are false outside
# the world's domain. This breaks the perpetuity theorem because Future A requires
# A to be true at all future times, but atoms at times outside the world's interval
# are false. A countermodel can now be found.
BM_TH_1_premises = ['\\Box A']
BM_TH_1_conclusions = ['\\Future A']
BM_TH_1_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,  # Increased for strict semantics (harder problem)
    'expectation' : True,  # Now expects countermodel under strict semantics
}
BM_TH_1_example = [
    BM_TH_1_premises,
    BM_TH_1_conclusions,
    BM_TH_1_settings,
]

# BM_TH_2: NECESSITY TO ALL PAST (PERPETUITY)
# NOTE: Under strict semantics (ProofChecker-aligned), atoms are false outside
# the world's domain. This breaks the perpetuity theorem because Past A requires
# A to be true at all past times, but atoms at times outside the world's interval
# are false. A countermodel can now be found.
BM_TH_2_premises = ['\\Box A']
BM_TH_2_conclusions = ['\\Past A']
BM_TH_2_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : True,  # Now expects countermodel under strict semantics
}
BM_TH_2_example = [
    BM_TH_2_premises,
    BM_TH_2_conclusions,
    BM_TH_2_settings,
]

# BM_TH_3: POSSIBILITY TO SOME FUTURE (PERPETUITY)
BM_TH_3_premises = ['\\future A']
BM_TH_3_conclusions = ['\\Diamond A']
BM_TH_3_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : False,
}
BM_TH_3_example = [
    BM_TH_3_premises,
    BM_TH_3_conclusions,
    BM_TH_3_settings,
]

# BM_TH_4: POSSIBILITY TO SOME PAST (PERPETUITY) 
BM_TH_4_premises = ['\\past A']
BM_TH_4_conclusions = ['\\Diamond A']
BM_TH_4_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : False,
}
BM_TH_4_example = [
    BM_TH_4_premises,
    BM_TH_4_conclusions,
    BM_TH_4_settings,
]

# MD_CM_5: NECESSITY TO ALL FUTURE NECESSITY
BM_TH_5_premises = ['\\Box A']
BM_TH_5_conclusions = ['\\Future \\Box A']
BM_TH_5_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : True,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : False,
}
BM_TH_5_example = [
    BM_TH_5_premises,
    BM_TH_5_conclusions,
    BM_TH_5_settings,
]





##############################################################################
######################## BX AXIOM SYSTEM EXAMPLES ############################
##############################################################################
# The BX axiom system is defined in the BimodalLogic ProofChecker with 42
# axioms across 8 layers. This section adds examples for the 32 currently
# testable axioms (76% coverage). The remaining 10 axioms (layers 5-8) are
# blocked pending frame class support from tasks 91/92.
#
# BX Axiom Coverage after this section:
#   Layer 1: Propositional (4/4 tested)
#   Layer 2: S5 Modal (5/5 tested, modal_k_dist already covered by MD_TH_1)
#   Layer 3: BX Temporal (22/22 tested)
#   Layer 4: Modal-Temporal Interaction (1/1 tested, partially covered by BM_TH_5)
#   Layer 5: Uniformity (0/5 - BLOCKED: requires discrete frame support, task 91)
#   Layer 6: Prior (0/2 - BLOCKED: requires discrete frame support, task 91)
#   Layer 7: Z1 (0/1 - BLOCKED: requires discrete frame support, task 91)
#   Layer 8: Density (0/2 - BLOCKED: requires dense frame support, task 92)
##############################################################################

####################################
### LAYER 1: PROPOSITIONAL AXIOMS ###
####################################

# PROP_K_TH: Propositional K Axiom
# BX name: prop_k
# Formula: (phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))
PROP_K_TH_premises = []
PROP_K_TH_conclusions = ['((A \\rightarrow (B \\rightarrow C)) \\rightarrow ((A \\rightarrow B) \\rightarrow (A \\rightarrow C)))']
PROP_K_TH_settings = {
    'N' : 3,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,
    'expectation' : False,
}
PROP_K_TH_example = [
    PROP_K_TH_premises,
    PROP_K_TH_conclusions,
    PROP_K_TH_settings,
]

# PROP_S_TH: Weakening (Schematic substitution)
# BX name: prop_s
# Formula: phi -> (psi -> phi)
PROP_S_TH_premises = []
PROP_S_TH_conclusions = ['(A \\rightarrow (B \\rightarrow A))']
PROP_S_TH_settings = {
    'N' : 2,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : False,
}
PROP_S_TH_example = [
    PROP_S_TH_premises,
    PROP_S_TH_conclusions,
    PROP_S_TH_settings,
]

# EX_FALSO_TH: Ex Falso Quodlibet
# BX name: ex_falso
# Formula: bot -> phi
EX_FALSO_TH_premises = []
EX_FALSO_TH_conclusions = ['(\\bot \\rightarrow A)']
EX_FALSO_TH_settings = {
    'N' : 1,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : False,
}
EX_FALSO_TH_example = [
    EX_FALSO_TH_premises,
    EX_FALSO_TH_conclusions,
    EX_FALSO_TH_settings,
]

# PEIRCE_TH: Peirce's Law
# BX name: peirce
# Formula: ((phi -> psi) -> phi) -> phi
PEIRCE_TH_premises = []
PEIRCE_TH_conclusions = ['(((A \\rightarrow B) \\rightarrow A) \\rightarrow A)']
PEIRCE_TH_settings = {
    'N' : 2,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,
    'expectation' : False,
}
PEIRCE_TH_example = [
    PEIRCE_TH_premises,
    PEIRCE_TH_conclusions,
    PEIRCE_TH_settings,
]



################################
### LAYER 2: S5 MODAL AXIOMS ###
################################

# MODAL_T_TH: Reflexivity (T axiom)
# BX name: modal_t
# Formula: Box phi -> phi
MODAL_T_TH_premises = []
MODAL_T_TH_conclusions = ['(\\Box A \\rightarrow A)']
MODAL_T_TH_settings = {
    'N' : 1,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : False,
}
MODAL_T_TH_example = [
    MODAL_T_TH_premises,
    MODAL_T_TH_conclusions,
    MODAL_T_TH_settings,
]

# MODAL_4_TH: Transitivity (4 axiom)
# BX name: modal_4
# Formula: Box phi -> Box Box phi
MODAL_4_TH_premises = []
MODAL_4_TH_conclusions = ['(\\Box A \\rightarrow \\Box \\Box A)']
MODAL_4_TH_settings = {
    'N' : 1,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : False,
}
MODAL_4_TH_example = [
    MODAL_4_TH_premises,
    MODAL_4_TH_conclusions,
    MODAL_4_TH_settings,
]

# MODAL_B_TH: Symmetry (B axiom)
# BX name: modal_b
# Formula: phi -> Box Diamond phi
MODAL_B_TH_premises = []
MODAL_B_TH_conclusions = ['(A \\rightarrow \\Box \\Diamond A)']
MODAL_B_TH_settings = {
    'N' : 1,
    'M' : 1,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : False,
}
MODAL_B_TH_example = [
    MODAL_B_TH_premises,
    MODAL_B_TH_conclusions,
    MODAL_B_TH_settings,
]

# MODAL_5_TH: S5 Characteristic (5 axiom / modal_5_collapse)
# BX name: modal_5_collapse
# Formula: Diamond Box phi -> Box phi
MODAL_5_TH_premises = []
MODAL_5_TH_conclusions = ['(\\Diamond \\Box A \\rightarrow \\Box A)']
MODAL_5_TH_settings = {
    'N' : 1,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : False,
}
MODAL_5_TH_example = [
    MODAL_5_TH_premises,
    MODAL_5_TH_conclusions,
    MODAL_5_TH_settings,
]
# NOTE: modal_k_dist (Box(phi->psi) -> (Box phi -> Box psi)) is already
# tested as MD_TH_1 in the Modal Theorems section above.



##############################################
### LAYER 3: BX TEMPORAL AXIOMS (BASIC)  ###
##############################################

# BX1_SERIAL_F_TH: Future Seriality
# BX name: serial_future
# Formula: top -> F(top) [using \neg \bot as explicit expansion of \top]
BX1_SERIAL_F_TH_premises = []
BX1_SERIAL_F_TH_conclusions = ['(\\neg \\bot \\rightarrow \\future \\neg \\bot)']
BX1_SERIAL_F_TH_settings = {
    'N' : 1,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,
    'expectation' : False,
}
BX1_SERIAL_F_TH_example = [
    BX1_SERIAL_F_TH_premises,
    BX1_SERIAL_F_TH_conclusions,
    BX1_SERIAL_F_TH_settings,
]

# BX1P_SERIAL_P_TH: Past Seriality
# BX name: serial_past
# Formula: top -> P(top) [using \neg \bot as explicit expansion of \top]
BX1P_SERIAL_P_TH_premises = []
BX1P_SERIAL_P_TH_conclusions = ['(\\neg \\bot \\rightarrow \\past \\neg \\bot)']
BX1P_SERIAL_P_TH_settings = {
    'N' : 1,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,
    'expectation' : False,
}
BX1P_SERIAL_P_TH_example = [
    BX1P_SERIAL_P_TH_premises,
    BX1P_SERIAL_P_TH_conclusions,
    BX1P_SERIAL_P_TH_settings,
]

# BX2G_MONO_U_TH: Until Guard Monotonicity (under G)
# BX name: left_mono_until_G
# Formula: G(phi -> chi) -> ((psi \Until phi) -> (psi \Until chi))
# Using binary infix: (event \Until guard)
# G(A -> C) -> ((B \Until A) -> (B \Until C))
BX2G_MONO_U_TH_premises = []
BX2G_MONO_U_TH_conclusions = ['(\\Future (A \\rightarrow C) \\rightarrow ((B \\Until A) \\rightarrow (B \\Until C)))']
BX2G_MONO_U_TH_settings = {
    'N' : 3,
    'M' : 4,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 15,
    'expectation' : False,
}
BX2G_MONO_U_TH_example = [
    BX2G_MONO_U_TH_premises,
    BX2G_MONO_U_TH_conclusions,
    BX2G_MONO_U_TH_settings,
]

# BX2H_MONO_S_TH: Since Guard Monotonicity (under H)
# BX name: left_mono_since_H
# Formula: H(phi -> chi) -> ((psi \Since phi) -> (psi \Since chi))
# Using binary infix: (event \Since guard)
# H(A -> C) -> ((B \Since A) -> (B \Since C))
BX2H_MONO_S_TH_premises = []
BX2H_MONO_S_TH_conclusions = ['(\\Past (A \\rightarrow C) \\rightarrow ((B \\Since A) \\rightarrow (B \\Since C)))']
BX2H_MONO_S_TH_settings = {
    'N' : 3,
    'M' : 4,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 15,
    'expectation' : False,
}
BX2H_MONO_S_TH_example = [
    BX2H_MONO_S_TH_premises,
    BX2H_MONO_S_TH_conclusions,
    BX2H_MONO_S_TH_settings,
]

# BX3_MONO_U_TH: Until Event Monotonicity
# BX name: right_mono_until
# Formula: G(phi -> psi) -> ((phi \Until chi) -> (psi \Until chi))
# G(A -> B) -> ((A \Until C) -> (B \Until C))
BX3_MONO_U_TH_premises = []
BX3_MONO_U_TH_conclusions = ['(\\Future (A \\rightarrow B) \\rightarrow ((A \\Until C) \\rightarrow (B \\Until C)))']
BX3_MONO_U_TH_settings = {
    'N' : 3,
    'M' : 4,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 15,
    'expectation' : False,
}
BX3_MONO_U_TH_example = [
    BX3_MONO_U_TH_premises,
    BX3_MONO_U_TH_conclusions,
    BX3_MONO_U_TH_settings,
]

# BX3P_MONO_S_TH: Since Event Monotonicity
# BX name: right_mono_since
# Formula: H(phi -> psi) -> ((phi \Since chi) -> (psi \Since chi))
# H(A -> B) -> ((A \Since C) -> (B \Since C))
BX3P_MONO_S_TH_premises = []
BX3P_MONO_S_TH_conclusions = ['(\\Past (A \\rightarrow B) \\rightarrow ((A \\Since C) \\rightarrow (B \\Since C)))']
BX3P_MONO_S_TH_settings = {
    'N' : 3,
    'M' : 4,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 15,
    'expectation' : False,
}
BX3P_MONO_S_TH_example = [
    BX3P_MONO_S_TH_premises,
    BX3P_MONO_S_TH_conclusions,
    BX3P_MONO_S_TH_settings,
]

# BX4_CONNECT_F_TH: Future Connectedness
# BX name: connect_future
# Formula: phi -> G(P(phi))  i.e. A -> G(P(A))
# NOTE: This is the same pattern as TN_TH_2, adding canonical BX4 name.
BX4_CONNECT_F_TH_premises = []
BX4_CONNECT_F_TH_conclusions = ['(A \\rightarrow \\Future \\past A)']
BX4_CONNECT_F_TH_settings = {
    'N' : 1,
    'M' : 3,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,
    'expectation' : False,
}
BX4_CONNECT_F_TH_example = [
    BX4_CONNECT_F_TH_premises,
    BX4_CONNECT_F_TH_conclusions,
    BX4_CONNECT_F_TH_settings,
]

# BX4P_CONNECT_P_TH: Past Connectedness
# BX name: connect_past
# Formula: phi -> H(F(phi))  i.e. A -> H(F(A))
BX4P_CONNECT_P_TH_premises = []
BX4P_CONNECT_P_TH_conclusions = ['(A \\rightarrow \\Past \\future A)']
BX4P_CONNECT_P_TH_settings = {
    'N' : 1,
    'M' : 3,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,
    'expectation' : False,
}
BX4P_CONNECT_P_TH_example = [
    BX4P_CONNECT_P_TH_premises,
    BX4P_CONNECT_P_TH_conclusions,
    BX4P_CONNECT_P_TH_settings,
]

# BX10_UNTIL_F_TH: Until Eventuality Extraction
# BX name: until_F
# Formula: (psi \Until phi) -> F(psi)  i.e. (B \Until A) -> F(B)
BX10_UNTIL_F_TH_premises = []
BX10_UNTIL_F_TH_conclusions = ['((B \\Until A) \\rightarrow \\future B)']
BX10_UNTIL_F_TH_settings = {
    'N' : 2,
    'M' : 3,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,
    'expectation' : False,
}
BX10_UNTIL_F_TH_example = [
    BX10_UNTIL_F_TH_premises,
    BX10_UNTIL_F_TH_conclusions,
    BX10_UNTIL_F_TH_settings,
]

# BX10P_SINCE_P_TH: Since Eventuality Extraction
# BX name: since_P
# Formula: (psi \Since phi) -> P(psi)  i.e. (B \Since A) -> P(B)
BX10P_SINCE_P_TH_premises = []
BX10P_SINCE_P_TH_conclusions = ['((B \\Since A) \\rightarrow \\past B)']
BX10P_SINCE_P_TH_settings = {
    'N' : 2,
    'M' : 3,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,
    'expectation' : False,
}
BX10P_SINCE_P_TH_example = [
    BX10P_SINCE_P_TH_premises,
    BX10P_SINCE_P_TH_conclusions,
    BX10P_SINCE_P_TH_settings,
]

# BX12_F_UNTIL_TH: F-Until Bridge (F implies Until with top guard)
# BX name: F_until_equiv
# Formula: F(phi) -> (phi \Until top)  i.e. F(A) -> (A \Until \neg\bot)
# Note: \top = \neg \bot (explicit expansion to avoid TopOperator bug)
BX12_F_UNTIL_TH_premises = []
BX12_F_UNTIL_TH_conclusions = ['(\\future A \\rightarrow (A \\Until \\neg \\bot))']
BX12_F_UNTIL_TH_settings = {
    'N' : 1,
    'M' : 3,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,
    'expectation' : False,
}
BX12_F_UNTIL_TH_example = [
    BX12_F_UNTIL_TH_premises,
    BX12_F_UNTIL_TH_conclusions,
    BX12_F_UNTIL_TH_settings,
]

# BX12P_P_SINCE_TH: P-Since Bridge (P implies Since with top guard)
# BX name: P_since_equiv
# Formula: P(phi) -> (phi \Since top)  i.e. P(A) -> (A \Since \neg\bot)
# Note: \top = \neg \bot (explicit expansion to avoid TopOperator bug)
BX12P_P_SINCE_TH_premises = []
BX12P_P_SINCE_TH_conclusions = ['(\\past A \\rightarrow (A \\Since \\neg \\bot))']
BX12P_P_SINCE_TH_settings = {
    'N' : 1,
    'M' : 3,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 10,
    'expectation' : False,
}
BX12P_P_SINCE_TH_example = [
    BX12P_P_SINCE_TH_premises,
    BX12P_P_SINCE_TH_conclusions,
    BX12P_P_SINCE_TH_settings,
]

# MF_MODAL_FUTURE_TH: Modal-Temporal Interaction
# BX name: modal_future (Layer 4)
# Formula: Box phi -> Box(G phi)  i.e. Box A -> Box(Future A)
# NOTE: This is the same pattern as BM_TH_5, adding canonical Layer 4 name.
MF_MODAL_FUTURE_TH_premises = []
MF_MODAL_FUTURE_TH_conclusions = ['(\\Box A \\rightarrow \\Box \\Future A)']
MF_MODAL_FUTURE_TH_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : True,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : False,
}
MF_MODAL_FUTURE_TH_example = [
    MF_MODAL_FUTURE_TH_premises,
    MF_MODAL_FUTURE_TH_conclusions,
    MF_MODAL_FUTURE_TH_settings,
]



###################################################
### LAYER 3: BX TEMPORAL AXIOMS (ADVANCED)      ###
###################################################

# BX5_ACCUM_U_TH: Until Self-Accumulation
# BX name: self_accum_until
# Formula: (psi \Until phi) -> (psi \Until (phi and (psi \Until phi)))
# i.e. (B \Until A) -> (B \Until (A and (B \Until A)))
BX5_ACCUM_U_TH_premises = []
BX5_ACCUM_U_TH_conclusions = ['((B \\Until A) \\rightarrow (B \\Until (A \\wedge (B \\Until A))))']
BX5_ACCUM_U_TH_settings = {
    'N' : 2,
    'M' : 4,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 20,
    'expectation' : False,
}
BX5_ACCUM_U_TH_example = [
    BX5_ACCUM_U_TH_premises,
    BX5_ACCUM_U_TH_conclusions,
    BX5_ACCUM_U_TH_settings,
]

# BX5P_ACCUM_S_TH: Since Self-Accumulation
# BX name: self_accum_since
# Formula: (psi \Since phi) -> (psi \Since (phi and (psi \Since phi)))
# i.e. (B \Since A) -> (B \Since (A and (B \Since A)))
BX5P_ACCUM_S_TH_premises = []
BX5P_ACCUM_S_TH_conclusions = ['((B \\Since A) \\rightarrow (B \\Since (A \\wedge (B \\Since A))))']
BX5P_ACCUM_S_TH_settings = {
    'N' : 2,
    'M' : 4,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 20,
    'expectation' : False,
}
BX5P_ACCUM_S_TH_example = [
    BX5P_ACCUM_S_TH_premises,
    BX5P_ACCUM_S_TH_conclusions,
    BX5P_ACCUM_S_TH_settings,
]

# BX6_ABSORB_U_TH: Until Absorption
# BX name: absorb_until
# Formula: ((phi and (psi \Until phi)) \Until phi) -> (psi \Until phi)
# i.e. ((A and (B \Until A)) \Until A) -> (B \Until A)
BX6_ABSORB_U_TH_premises = []
BX6_ABSORB_U_TH_conclusions = ['(((A \\wedge (B \\Until A)) \\Until A) \\rightarrow (B \\Until A))']
BX6_ABSORB_U_TH_settings = {
    'N' : 2,
    'M' : 4,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 20,
    'expectation' : False,
}
BX6_ABSORB_U_TH_example = [
    BX6_ABSORB_U_TH_premises,
    BX6_ABSORB_U_TH_conclusions,
    BX6_ABSORB_U_TH_settings,
]

# BX6P_ABSORB_S_TH: Since Absorption
# BX name: absorb_since
# Formula: ((phi and (psi \Since phi)) \Since phi) -> (psi \Since phi)
# i.e. ((A and (B \Since A)) \Since A) -> (B \Since A)
BX6P_ABSORB_S_TH_premises = []
BX6P_ABSORB_S_TH_conclusions = ['(((A \\wedge (B \\Since A)) \\Since A) \\rightarrow (B \\Since A))']
BX6P_ABSORB_S_TH_settings = {
    'N' : 2,
    'M' : 4,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 20,
    'expectation' : False,
}
BX6P_ABSORB_S_TH_example = [
    BX6P_ABSORB_S_TH_premises,
    BX6P_ABSORB_S_TH_conclusions,
    BX6P_ABSORB_S_TH_settings,
]

# BX11_LIN_F_TH: Temporal F-Linearity
# BX name: temp_linearity
# Formula: F(phi) and F(psi) -> F(phi and psi) or F(phi and F(psi)) or F(F(phi) and psi)
# Note: unary prefix operators like \future cannot be wrapped in outer parens (parser treats
# outer-paren expressions as binary infix). Use: \future (A \wedge B) not (\future (A \wedge B))
BX11_LIN_F_TH_premises = []
BX11_LIN_F_TH_conclusions = ['((\\future A \\wedge \\future B) \\rightarrow (\\future (A \\wedge B) \\vee (\\future (A \\wedge \\future B) \\vee \\future (\\future A \\wedge B))))']
BX11_LIN_F_TH_settings = {
    'N' : 2,
    'M' : 4,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 20,
    'expectation' : False,
}
BX11_LIN_F_TH_example = [
    BX11_LIN_F_TH_premises,
    BX11_LIN_F_TH_conclusions,
    BX11_LIN_F_TH_settings,
]

# BX11P_LIN_P_TH: Temporal P-Linearity
# BX name: temp_linearity_past
# Formula: P(phi) and P(psi) -> P(phi and psi) or P(phi and P(psi)) or P(P(phi) and psi)
BX11P_LIN_P_TH_premises = []
BX11P_LIN_P_TH_conclusions = ['((\\past A \\wedge \\past B) \\rightarrow (\\past (A \\wedge B) \\vee (\\past (A \\wedge \\past B) \\vee \\past (\\past A \\wedge B))))']
BX11P_LIN_P_TH_settings = {
    'N' : 2,
    'M' : 4,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 20,
    'expectation' : False,
}
BX11P_LIN_P_TH_example = [
    BX11P_LIN_P_TH_premises,
    BX11P_LIN_P_TH_conclusions,
    BX11P_LIN_P_TH_settings,
]

# BX13_ENRICH_U_TH: Until Enrichment
# BX name: enrichment_until
# Formula: p and (psi \Until phi) -> ((psi and (p \Since phi)) \Until phi)
# i.e. C and (B \Until A) -> ((B and (C \Since A)) \Until A)
BX13_ENRICH_U_TH_premises = []
BX13_ENRICH_U_TH_conclusions = ['((C \\wedge (B \\Until A)) \\rightarrow ((B \\wedge (C \\Since A)) \\Until A))']
BX13_ENRICH_U_TH_settings = {
    'N' : 3,
    'M' : 4,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 30,
    'expectation' : False,
}
BX13_ENRICH_U_TH_example = [
    BX13_ENRICH_U_TH_premises,
    BX13_ENRICH_U_TH_conclusions,
    BX13_ENRICH_U_TH_settings,
]

# BX13P_ENRICH_S_TH: Since Enrichment
# BX name: enrichment_since
# Formula: p and (psi \Since phi) -> ((psi and (p \Until phi)) \Since phi)
# i.e. C and (B \Since A) -> ((B and (C \Until A)) \Since A)
BX13P_ENRICH_S_TH_premises = []
BX13P_ENRICH_S_TH_conclusions = ['((C \\wedge (B \\Since A)) \\rightarrow ((B \\wedge (C \\Until A)) \\Since A))']
BX13P_ENRICH_S_TH_settings = {
    'N' : 3,
    'M' : 4,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 30,
    'expectation' : False,
}
BX13P_ENRICH_S_TH_example = [
    BX13P_ENRICH_S_TH_premises,
    BX13P_ENRICH_S_TH_conclusions,
    BX13P_ENRICH_S_TH_settings,
]



#################################################
### LAYER 3: BX7 LINEARITY AXIOMS (COMPLEX)  ###
#################################################

# BX7_LINEAR_U_TH: Until Linearity (4 variables)
# BX name: linear_until
# Formula: (psi \Until phi) and (theta \Until chi) ->
#          ((psi and theta) \Until (phi and chi)) or
#          ((psi and chi) \Until (phi and chi)) or
#          ((phi and theta) \Until (phi and chi))
# Where: psi=B, phi=A, theta=D, chi=C (binary infix form)
BX7_LINEAR_U_TH_premises = []
BX7_LINEAR_U_TH_conclusions = [
    '(((B \\Until A) \\wedge (D \\Until C)) \\rightarrow '
    '(((B \\wedge D) \\Until (A \\wedge C)) \\vee '
    '(((B \\wedge C) \\Until (A \\wedge C)) \\vee '
    '((A \\wedge D) \\Until (A \\wedge C)))))'
]
BX7_LINEAR_U_TH_settings = {
    'N' : 4,
    'M' : 5,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 60,
    'expectation' : False,
}
BX7_LINEAR_U_TH_example = [
    BX7_LINEAR_U_TH_premises,
    BX7_LINEAR_U_TH_conclusions,
    BX7_LINEAR_U_TH_settings,
]

# BX7P_LINEAR_S_TH: Since Linearity (4 variables)
# BX name: linear_since
# Formula: (psi \Since phi) and (theta \Since chi) ->
#          ((psi and theta) \Since (phi and chi)) or
#          ((psi and chi) \Since (phi and chi)) or
#          ((phi and theta) \Since (phi and chi))
BX7P_LINEAR_S_TH_premises = []
BX7P_LINEAR_S_TH_conclusions = [
    '(((B \\Since A) \\wedge (D \\Since C)) \\rightarrow '
    '(((B \\wedge D) \\Since (A \\wedge C)) \\vee '
    '(((B \\wedge C) \\Since (A \\wedge C)) \\vee '
    '((A \\wedge D) \\Since (A \\wedge C)))))'
]
BX7P_LINEAR_S_TH_settings = {
    'N' : 4,
    'M' : 5,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 60,
    'expectation' : False,
}
BX7P_LINEAR_S_TH_example = [
    BX7P_LINEAR_S_TH_premises,
    BX7P_LINEAR_S_TH_conclusions,
    BX7P_LINEAR_S_TH_settings,
]



###############################################
### DEFINE EXAMPLES AND THEORIES TO COMPUTE ###
###############################################

# Organize examples by category
countermodel_examples = {
    # Extensional Countermodels
    "EX_CM_1" : EX_CM_1_example,
    
    # Modal Countermodels
    "MD_CM_1" : MD_CM_1_example,
    "MD_CM_2" : MD_CM_2_example,
    "MD_CM_3" : MD_CM_3_example,
    "MD_CM_4" : MD_CM_4_example,
    "MD_CM_5" : MD_CM_5_example,
    "MD_CM_6" : MD_CM_6_example,

    # Tense Countermodels
    "TN_CM_1" : TN_CM_1_example,
    "TN_CM_2" : TN_CM_2_example,

    # Bimodal Countermodels
    "BM_CM_1" : BM_CM_1_example,
    "BM_CM_2" : BM_CM_2_example,
    "BM_CM_3" : BM_CM_3_example,
    "BM_CM_4" : BM_CM_4_example,
}

theorem_examples = {
    # Extensional Theorems
    "EX_TH_1" : EX_TH_1_example,

    # Modal Theorems
    "MD_TH_1" : MD_TH_1_example,
    "MD_TH_2" : MD_TH_2_example,

    # Tense Theorems
    "TN_TH_2" : TN_TH_2_example,

    # Bimodal Theorems
    "BM_TH_1" : BM_TH_1_example,
    "BM_TH_2" : BM_TH_2_example,
    "BM_TH_3" : BM_TH_3_example,
    "BM_TH_4" : BM_TH_4_example,

    # BX Axiom System - Layer 1: Propositional
    "PROP_K_TH" : PROP_K_TH_example,
    "PROP_S_TH" : PROP_S_TH_example,
    "EX_FALSO_TH" : EX_FALSO_TH_example,
    "PEIRCE_TH" : PEIRCE_TH_example,

    # BX Axiom System - Layer 2: S5 Modal
    "MODAL_T_TH" : MODAL_T_TH_example,
    "MODAL_4_TH" : MODAL_4_TH_example,
    "MODAL_B_TH" : MODAL_B_TH_example,
    "MODAL_5_TH" : MODAL_5_TH_example,

    # BX Axiom System - Layer 3: BX Temporal (Basic)
    "BX1_SERIAL_F_TH" : BX1_SERIAL_F_TH_example,
    "BX1P_SERIAL_P_TH" : BX1P_SERIAL_P_TH_example,
    "BX2G_MONO_U_TH" : BX2G_MONO_U_TH_example,
    "BX2H_MONO_S_TH" : BX2H_MONO_S_TH_example,
    "BX3_MONO_U_TH" : BX3_MONO_U_TH_example,
    "BX3P_MONO_S_TH" : BX3P_MONO_S_TH_example,
    "BX4_CONNECT_F_TH" : BX4_CONNECT_F_TH_example,
    "BX4P_CONNECT_P_TH" : BX4P_CONNECT_P_TH_example,
    "BX10_UNTIL_F_TH" : BX10_UNTIL_F_TH_example,
    "BX10P_SINCE_P_TH" : BX10P_SINCE_P_TH_example,
    "BX12_F_UNTIL_TH" : BX12_F_UNTIL_TH_example,
    "BX12P_P_SINCE_TH" : BX12P_P_SINCE_TH_example,

    # BX Axiom System - Layer 4: Modal-Temporal Interaction
    "MF_MODAL_FUTURE_TH" : MF_MODAL_FUTURE_TH_example,

    # BX Axiom System - Layer 3: BX Temporal (Advanced)
    "BX5_ACCUM_U_TH" : BX5_ACCUM_U_TH_example,
    "BX5P_ACCUM_S_TH" : BX5P_ACCUM_S_TH_example,
    "BX6_ABSORB_U_TH" : BX6_ABSORB_U_TH_example,
    "BX6P_ABSORB_S_TH" : BX6P_ABSORB_S_TH_example,
    "BX11_LIN_F_TH" : BX11_LIN_F_TH_example,
    "BX11P_LIN_P_TH" : BX11P_LIN_P_TH_example,
    "BX13_ENRICH_U_TH" : BX13_ENRICH_U_TH_example,
    "BX13P_ENRICH_S_TH" : BX13P_ENRICH_S_TH_example,

    # BX Axiom System - Layer 3: BX7 Linearity (Complex, 4 variables)
    "BX7_LINEAR_U_TH" : BX7_LINEAR_U_TH_example,
    "BX7P_LINEAR_S_TH" : BX7P_LINEAR_S_TH_example,
}

# Combine for unit_tests (used by test framework)
unit_tests = {**countermodel_examples, **theorem_examples}

# NOTE: at least one theory is required, multiple are permitted for comparison
semantic_theories = {
    "Bimodal" : bimodal_theory,
    # additional theories will require their own translation dictionaries
}

# NOTE: at least one example is required, multiple are permitted for comparison
example_range = {

    ### COUNTERMODELS ###

    # Extensional Countermodels
    "EX_CM_1" : EX_CM_1_example,
    
    # Modal Countermodels
    "MD_CM_1" : MD_CM_1_example,
    "MD_CM_2" : MD_CM_2_example,
    "MD_CM_3" : MD_CM_3_example,
    "MD_CM_4" : MD_CM_4_example,
    "MD_CM_5" : MD_CM_5_example,
    "MD_CM_6" : MD_CM_6_example,

    # Tense Countermodels
    "TN_CM_1" : TN_CM_1_example,
    "TN_CM_2" : TN_CM_2_example, # No countermodel
    
    # Bimodal Countermodel
    "BM_CM_1" : BM_CM_1_example, # No countermodel
    "BM_CM_2" : BM_CM_2_example, # No countermodel
    "BM_CM_3" : BM_CM_3_example, # Doesn't find countermodel if run in isolation
    "BM_CM_4" : BM_CM_4_example, # Countermodel has true conclusion

    ### THEOREMS ###

    # Extensional Theorems
    "EX_TH_1" : EX_TH_1_example,

    # Modal Theorems
    "MD_TH_1" : MD_TH_1_example,
    "MD_TH_2" : MD_TH_2_example,

    # Tense Theorems
    "TN_TH_2" : TN_TH_2_example,

    # Bimodal Theorems
    "BM_TH_1" : BM_TH_1_example, # Has countermodel
    "BM_TH_2" : BM_TH_2_example, # Has countermodel
    "BM_TH_3" : BM_TH_3_example,
    "BM_TH_4" : BM_TH_4_example,
    "BM_TH_5" : BM_TH_5_example,
}


# The report will be printed by ModelRunner after all examples complete
# No atexit registration needed - the runner controls when reports print
