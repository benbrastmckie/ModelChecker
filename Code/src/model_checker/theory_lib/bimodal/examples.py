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

from semantic import (
    BimodalStructure,
    BimodalSemantics,
    BimodalProposition,
)
from operators import bimodal_operators

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
    'N' : 1,
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
    'N' : 1,
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
    'N' : 1,
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
    'N' : 1,
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
    'N' : 1,
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
    'N' : 1,
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
    'N' : 1,
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
    'N' : 1,
    'M' : 3,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
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
    'N' : 1,
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
    'N' : 1,
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
    'N' : 1,
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
    'N' : 1,
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
MD_TH_2_conclusions = []
MD_TH_2_settings = {
    'N' : 1,
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
BM_TH_1_premises = ['\\Box A']
BM_TH_1_conclusions = ['\\Future A']
BM_TH_1_settings = {
    'N' : 1,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : False,
}
BM_TH_1_example = [
    BM_TH_1_premises,
    BM_TH_1_conclusions,
    BM_TH_1_settings,
]

# BM_TH_2: NECESSITY TO ALL PAST (PERPETUITY)
BM_TH_2_premises = ['\\Box A']
BM_TH_2_conclusions = ['\\Past A']
BM_TH_2_settings = {
    'N' : 1,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 2,
    'expectation' : False,
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
    'N' : 1,
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
    'N' : 1,
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
    'N' : 1,
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
    # "MD_CM_1" : MD_CM_1_example,
    # "MD_CM_2" : MD_CM_2_example,
    # "MD_CM_3" : MD_CM_3_example,
    # "MD_CM_4" : MD_CM_4_example,
    # "MD_CM_5" : MD_CM_5_example,
    # "MD_CM_6" : MD_CM_6_example,

    # Tense Countermodels
    # "TN_CM_1" : TN_CM_1_example,
    # "TN_CM_2" : TN_CM_2_example,
    
    # Bimodal Countermodel
    # "BM_CM_1" : BM_CM_1_example,
    # "BM_CM_2" : BM_CM_2_example,
    # "BM_CM_3" : BM_CM_3_example,
    # "BM_CM_4" : BM_CM_4_example,

    ### THEOREMS ###

    # Extensional Theorems
    # "EX_TH_1" : EX_TH_1_example,

    # Modal Theorems
    # "MD_TH_1" : MD_TH_1_example,
    # "MD_TH_2" : MD_TH_2_example,

    # Tense Theorems
    # "TN_TH_2" : TN_TH_2_example,

    # Bimodal Theorems
    # "BM_TH_1" : BM_TH_1_example,
    # "BM_TH_2" : BM_TH_2_example,
    # "BM_TH_3" : BM_TH_3_example,
    # "BM_TH_4" : BM_TH_4_example,
    # "BM_TH_5" : BM_TH_5_example,
}



####################
### RUN EXAMPLES ###
####################

if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)
