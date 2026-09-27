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
- back: Exact cyclic period of a witness-family lasso's repeating back segment, not an
  upper bound on it (default: 2)
- mid: Maximum length of a witness-family lasso's non-repeating mid segment (default: 1)
- fwd: Exact cyclic period of a witness-family lasso's repeating forward segment, not an
  upper bound on it (default: 2)
- max_witnesses: Optional cap on the number of distinct witness lassos searched for
  (default: None, uncapped -- at most one per boxed subformula guessed false)
- max_time: Maximum computation time in seconds
- expectation: True if a countermodel (certificate) is expected to be found, False if the
  premises/conclusions form a theorem (no certificate expected)

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
    # No "align_vertically": BimodalSemantics.ADDITIONAL_GENERAL_SETTINGS is empty -- the
    # certificate printer prints each history as a single line, needing no vertical-alignment
    # display option (see semantic/core.py's own comment on this).
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
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

# BM_CM_1: ALL FUTURE TO NECESSITY
# Future A does not imply Box A: a world can have A true at all future times
# while some other world has A false at the current time.
# HISTORY (superseded by the certificate redesign, Phase 19): this example was previously
# recalibrated to a 60s max_time and marked `unstable` in test_bimodal.py, chasing a
# heavy-tailed Z3 solve distribution (median ~7-8s, one divergent draw at 600s) rooted in
# the retired encoding's `ForAllTime`/`ExistsTime`-quantified all_future operator family
# (see operators.py's old `_fresh_bound_int` discussion, itself retired). The certificate
# encoding has no such quantifier at all (D1-D4), so that whole cost profile cannot recur
# by construction, not merely by observation. Measured under the certificate encoding
# (2026-09-25): decides `match` in ~1ms, confirmed stable across 20 consecutive runs (see
# test_bimodal.py's own note on removing the `unstable` marking). max_time lowered to the
# floor and the `unstable` marking removed.
BM_CM_1_premises = ['\\Future A']
BM_CM_1_conclusions = ['\\Box A']
BM_CM_1_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
    'expectation' : True,
}
BM_CM_1_example = [
    BM_CM_1_premises,
    BM_CM_1_conclusions,
    BM_CM_1_settings,
]

# BM_CM_2: ALL PAST TO NECESSITY
# Past A does not imply Box A: a world can have A true at all past times
# while some other world has A false at the current time.
# Previously timed out; now finds countermodel quickly with corrected semantics.
BM_CM_2_premises = ['\\Past A']
BM_CM_2_conclusions = ['\\Box A']
BM_CM_2_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # ~2s with isolated Z3 context
    'expectation' : True,
}
BM_CM_2_example = [
    BM_CM_2_premises,
    BM_CM_2_conclusions,
    BM_CM_2_settings,
]

# BM_CM_3: POSSIBILITY TO SOME FUTURE
# Diamond A does not imply future A: a world can be possibly A (some world has A now)
# without A being true at any future time in the current world.
# Previously timed out; now finds countermodel quickly with corrected semantics.
BM_CM_3_premises = ['\\Diamond A']
BM_CM_3_conclusions = ['\\future A']
BM_CM_3_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Increased from 2 for reliability across Z3 state variations
    'expectation' : True,
}
BM_CM_3_example = [
    BM_CM_3_premises,
    BM_CM_3_conclusions,
    BM_CM_3_settings,
]

# BM_CM_4: POSSIBILITY TO SOME PAST
# Diamond A does not imply past A: a world can be possibly A (some world has A now)
# without A being true at any past time in the current world.
# HISTORY (superseded by the certificate redesign, Phase 19): this example was previously
# recalibrated to a 120s max_time and marked `unstable` in test_bimodal.py after commit
# f9cc081e's Skolemized Seriality + Interpolation frame axioms regressed it to a heavy-tailed
# solve-cost distribution. Both `build_seriality_constraint` and `build_interpolation_constraint`
# (the axioms responsible) no longer exist anywhere in `semantic/core.py` -- the certificate
# encoding has no frame-axiom machinery at all (D1-D4) -- so that cost profile cannot recur by
# construction. Measured under the certificate encoding (2026-09-25): decides `match` in ~1ms,
# confirmed stable across 20 consecutive runs. max_time lowered to the floor and the `unstable`
# marking removed. NOTE for Phase 21 (oracle cleanup): the retired-encoding-era comment this
# replaces asked to "keep in sync with the inline copy in
# oracle/bimodal_logic/tests/test_boundary_regression.py" -- that oracle-side file is unaffected
# by this bimodal-side change and is Phase 20/21's own scope to update.
BM_CM_4_premises = ['\\Diamond A']
BM_CM_4_conclusions = ['\\past A']
BM_CM_4_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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

# BM_TH_1: NECESSITY TO ALL FUTURE (PERPETUITY, paper's P1 conjunct / the MF+MT+TR
# derivation of "Box phi -> Future phi")
# Audited against the paper (~/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex):
# the paper derives Box(phi) -> Future(phi) directly from MF (Box phi -> Box Future phi)
# and MT (Box psi -> psi) by substituting psi := Future phi, immediately after stating MF
# ("Box phi -> Box Future phi follows from MF... Box phi -> Past phi follows by TR").
# Certified by the Lean formalization's modal_future_valid (Metalogic/Soundness.lean:373)
# over the unrestricted frame class. A countermodel here would refute a landed,
# sorry-free Lean theorem, so `expectation: False` (no countermodel; a genuine theorem) is
# retained. The retired window-and-abundance encoding's countermodel-at-the-boundary
# artifact (which required an M=3 shift-closure workaround, now deleted along with M
# itself) no longer applies: the certificate encoding has no window and no shift-closure
# constraint to size. Segment lengths (back/mid/fwd) left at the class defaults; Phase 17
# measured this example (previously excluded via KNOWN_TIMEOUT_EXAMPLES) at these
# defaults: decides `match` in ~2ms (2026-09-25), ~15000x headroom under the 10s floor, so
# `max_time` is lowered from the retired encoding's 30s exhaustive-search budget to the
# floor.
BM_TH_1_premises = ['\\Box A']
BM_TH_1_conclusions = ['\\Future A']
BM_TH_1_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
    'expectation' : False,  # Valid theorem: no countermodel expected
}
BM_TH_1_example = [
    BM_TH_1_premises,
    BM_TH_1_conclusions,
    BM_TH_1_settings,
]

# BM_TH_2: NECESSITY TO ALL PAST (PERPETUITY, the TR-dual of BM_TH_1: "Box phi -> Past
# phi" follows from MF + MT + TR by the same paper passage cited above)
# Audited against the paper and Lean the same way as BM_TH_1: TR (temporal symmetry, "If
# vdash phi then vdash phi with since/until interchanged") converts the Future direction
# derived from MF+MT into the Past direction stated here; no separate Lean citation beyond
# modal_future_valid plus the same MT instance is needed. `expectation: False` retained.
BM_TH_2_premises = ['\\Box A']
BM_TH_2_conclusions = ['\\Past A']
BM_TH_2_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from 30s: Phase 17 measured ~2ms at these defaults
                      # (2026-09-25), matching BM_TH_1's measurement.
    'expectation' : False,  # Valid theorem: no countermodel expected
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
# blocked pending discrete/dense frame-class support work tracked outside this
# theory (Uniformity/Prior/Z1 need discrete-frame support; Density needs
# dense-frame support, itself out of scope for this Z-time-only redesign).
#
# BX Axiom Coverage after this section:
#   Layer 1: Propositional (4/4 tested)
#   Layer 2: S5 Modal (5/5 tested, modal_k_dist already covered by MD_TH_1)
#   Layer 3: BX Temporal (22/22 tested)
#   Layer 4: Modal-Temporal Interaction (1/1 tested, partially covered by BM_TH_5)
#   Layer 5: Uniformity (0/5 - BLOCKED: requires discrete frame support)
#   Layer 6: Prior (0/2 - BLOCKED: requires discrete frame support)
#   Layer 7: Z1 (0/1 - BLOCKED: requires discrete frame support)
#   Layer 8: Density (0/2 - BLOCKED: requires dense frame support, out of scope for Z-time)
#
# GUARD-FIRST NORMALIZATION (post-audit amendment): ModelChecker's `\Until`/`\Since` are now
# guard-first, matching this file's own paper source and the Lean development exactly, so the
# historical audit paragraph below (which checked every example against the paper's guard-first
# axioms under a since-retired event-first swap) has been superseded: every `\Until`/`\Since`
# operand pair below was re-swapped in lockstep with `operators.py`/`semantic/formula.py`'s
# normalization, one occurrence at a time against its own `# Formula:` comment, so each example
# still encodes exactly the axiom the table below names. The Burgess-convention citation the
# retired event-first order relied on is deliberately dropped in favor of one argument order
# across ModelChecker, the oracle, and Lean (see `docs/ARCHITECTURE.md`).
#
# PAPER-AXIOM AUDIT (semantic-alignment amendment, historical): every BX/MF/perpetuity example
# below was checked directly against ~/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex's
# semantic clauses (until/since, line ~1072-1077) and its BX/MF/perpetuity schemata
# (line ~1247-1330). The paper's `until`/`since` are GUARD-FIRST: `(guard \until event)`.
# ModelChecker's `\Until`/`\Since` operators were EVENT-FIRST at the time of this audit (D2, the
# retired Burgess convention `true_at(event_arg, guard_arg, ...)`): the surface sentence
# `(X \Until Y)` meant event=X, guard=Y -- the OPPOSITE argument order from the paper's own
# `\until`. Every formula below was re-derived from the paper's guard-first axiom under that
# event-first swap and checked character-for-character against the coded sentence; every one
# below was found to already encode its axiom correctly. The one thing NOT reliably correct
# pre-audit was some examples' informal "Formula:" comment lines, which mixed the paper's
# guard-first meta-variable placement with the code's then-event-first values (e.g. BX10's old
# comment claimed the consequent was "F(psi)" using "psi" in the paper's guard position, when
# the axiom -- and the actual coded formula -- puts the future/past operator on the EVENT, i.e.
# the code's first argument at the time). Source of truth chosen: the paper's axiom (guard-first)
# translated through D2's then-event-first swap; where a comment disagreed with that
# translation, the comment was corrected to cite the paper's axiom label directly instead of
# unlabelled psi/phi meta-variables.
#
# | Example                          | Paper axiom(s)          | Verdict                          |
# |-----------------------------------|--------------------------|-----------------------------------|
# | BX1_SERIAL_F_TH / BX1P_SERIAL_P_TH | TS (+ TR for the past dual) | formula correct (top->F top / top->P top; equivalent to bare `future top` since the antecedent is a tautology) |
# | BX2G_MONO_U_TH                     | UG                        | formula correct (guard varies, event fixed) |
# | BX2H_MONO_S_TH                     | UG (Since dual, via TR)   | formula correct |
# | BX3_MONO_U_TH                      | UC                        | formula correct (event varies, guard fixed) |
# | BX3P_MONO_S_TH                     | UC (Since dual, via TR)   | formula correct |
# | BX4_CONNECT_F_TH / BX4P_CONNECT_P_TH | TC (+ TR for the past dual) | formula correct |
# | BX5_ACCUM_U_TH / BX5P_ACCUM_S_TH   | UF                        | formula correct |
# | BX6_ABSORB_U_TH / BX6P_ABSORB_S_TH | UI                        | formula correct |
# | BX7_LINEAR_U_TH / BX7P_LINEAR_S_TH | CN                        | formula correct (3-way disjunction matches exactly, modulo disjunct reordering) |
# | BX10_UNTIL_F_TH / BX10P_SINCE_P_TH | UE                        | formula correct; "Formula:" comment corrected (see audit note above) |
# | BX11_LIN_F_TH / BX11P_LIN_P_TH     | TL (+ TR for the past dual) | formula correct (disjuncts reordered relative to the paper's statement; disjunction is commutative) |
# | BX12_F_UNTIL_TH / BX12P_P_SINCE_TH | UT                        | formula correct |
# | BX13_ENRICH_U_TH / BX13P_ENRICH_S_TH | SU (+ TR for the Since-indexed dual) | formula correct |
# | MF_MODAL_FUTURE_TH                 | MF                        | formula correct; `expectation: False` (no countermodel) was ALREADY the correct value -- see the example's own comment and test_bimodal.py's KNOWN_TIMEOUT_EXAMPLES comment for why the retired encoding still needed to exclude it despite that |
# | BM_TH_1 / BM_TH_2                  | MF + MT + TR (perpetuity) | formula correct; see the examples' own comments |
# | BM_TH_3 / BM_TH_4                  | P2 (special case: future/past A implies "sometimes A" by disjunction introduction, then P2) | formula correct |
# | BM_TH_5                            | TF                        | formula correct |
# | MD_TH_1                            | MK                        | formula correct |
# | MODAL_T_TH / MODAL_4_TH / MODAL_B_TH / MODAL_5_TH | S5 theorems (derivable from MK+MT+M5; the paper does not separately name T/4/B/5 as primitive since S5 already contains M5) | formula correct |
# | PROP_K_TH / PROP_S_TH / EX_FALSO_TH / PEIRCE_TH | standard CPL tautologies (the paper's base logic layer, not independently labelled) | formula correct |
# | TN_TH_2                            | TC                        | formula correct (same instance as BX4_CONNECT_F_TH) |
# | MD_TH_2 / TN_CM_1 / TN_CM_2 / BM_CM_1-4 | genuine countermodel/non-theorem claims, not paper axiom instances | formula and `expectation` correct as coded |
#
# A0 FRAME-CLASS STANDING TEST (amendment, not an examples.py entry): `prior_UZ` and `z1`
# (Prior/Z1 axiom instances, `ProofSystem/Axioms.lean:612-613`) are valid over EVERY temporal
# order but NOT valid specifically over Z-time (`not_validIn_base_prior_UZ`/
# `not_validIn_base_z1`, `Metalogic/Independence/ZTimeSharpness.lean:225,236`), so by (SOUND)
# no witness-family certificate can ever exist for them even though they are not
# unconditionally valid. Their expected verdict is therefore neither `True` nor `False` in
# this file's sense -- it is "no certificate at any configured length, rendered inconclusive,
# never reported as valid" (see docs/ADEQUACY.md sections 7.2 and 7.4's never-report-validity
# rule). Because that verdict shape does not fit this file's boolean `expectation` field, these
# two instances are tested directly in
# `tests/unit/test_structure.py::TestA0FrameClassStandingTest` instead of as `examples.py`
# entries; they are recorded here only so this audit pass is not silently blind to them.
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
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
# Formula: G(phi -> chi) -> ((phi \Until psi) -> (chi \Until psi))
# Using binary infix: (guard \Until event)
# G(A -> C) -> ((A \Until B) -> (C \Until B))
BX2G_MONO_U_TH_premises = []
BX2G_MONO_U_TH_conclusions = ['(\\Future (A \\rightarrow C) \\rightarrow ((A \\Until B) \\rightarrow (C \\Until B)))']
BX2G_MONO_U_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from the retired encoding's budget; measured <50ms under the certificate encoding (Phase 19, 2026-09-25).
    'expectation' : False,
}
BX2G_MONO_U_TH_example = [
    BX2G_MONO_U_TH_premises,
    BX2G_MONO_U_TH_conclusions,
    BX2G_MONO_U_TH_settings,
]

# BX2H_MONO_S_TH: Since Guard Monotonicity (under H)
# BX name: left_mono_since_H
# Formula: H(phi -> chi) -> ((phi \Since psi) -> (chi \Since psi))
# Using binary infix: (guard \Since event)
# H(A -> C) -> ((A \Since B) -> (C \Since B))
BX2H_MONO_S_TH_premises = []
BX2H_MONO_S_TH_conclusions = ['(\\Past (A \\rightarrow C) \\rightarrow ((A \\Since B) \\rightarrow (C \\Since B)))']
BX2H_MONO_S_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from the retired encoding's budget; measured <50ms under the certificate encoding (Phase 19, 2026-09-25).
    'expectation' : False,
}
BX2H_MONO_S_TH_example = [
    BX2H_MONO_S_TH_premises,
    BX2H_MONO_S_TH_conclusions,
    BX2H_MONO_S_TH_settings,
]

# BX3_MONO_U_TH: Until Event Monotonicity
# BX name: right_mono_until
# Formula: G(phi -> psi) -> ((chi \Until phi) -> (chi \Until psi))
# G(A -> B) -> ((C \Until A) -> (C \Until B))
BX3_MONO_U_TH_premises = []
BX3_MONO_U_TH_conclusions = ['(\\Future (A \\rightarrow B) \\rightarrow ((C \\Until A) \\rightarrow (C \\Until B)))']
BX3_MONO_U_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from the retired encoding's budget; measured <50ms under the certificate encoding (Phase 19, 2026-09-25).
    'expectation' : False,
}
BX3_MONO_U_TH_example = [
    BX3_MONO_U_TH_premises,
    BX3_MONO_U_TH_conclusions,
    BX3_MONO_U_TH_settings,
]

# BX3P_MONO_S_TH: Since Event Monotonicity
# BX name: right_mono_since
# Formula: H(phi -> psi) -> ((chi \Since phi) -> (chi \Since psi))
# H(A -> B) -> ((C \Since A) -> (C \Since B))
BX3P_MONO_S_TH_premises = []
BX3P_MONO_S_TH_conclusions = ['(\\Past (A \\rightarrow B) \\rightarrow ((C \\Since A) \\rightarrow (C \\Since B)))']
BX3P_MONO_S_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from the retired encoding's budget; measured <50ms under the certificate encoding (Phase 19, 2026-09-25).
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
    'expectation' : False,
}
BX4P_CONNECT_P_TH_example = [
    BX4P_CONNECT_P_TH_premises,
    BX4P_CONNECT_P_TH_conclusions,
    BX4P_CONNECT_P_TH_settings,
]

# BX10_UNTIL_F_TH: Until Eventuality Extraction
# Paper axiom UE: (guard \until event) -> future(event). ModelChecker's \Until is now
# guard-first too (D2), so "(A \Until B)" is written exactly as the paper's own
# "(guard \until event)" [guard=A, event=B]; the consequent "future(event)" is therefore
# "future B", matching the coded conclusion.
# Formula: (A \Until B) -> future B, instantiating UE with guard=A, event=B.
BX10_UNTIL_F_TH_premises = []
BX10_UNTIL_F_TH_conclusions = ['((A \\Until B) \\rightarrow \\future B)']
BX10_UNTIL_F_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
    'expectation' : False,
}
BX10_UNTIL_F_TH_example = [
    BX10_UNTIL_F_TH_premises,
    BX10_UNTIL_F_TH_conclusions,
    BX10_UNTIL_F_TH_settings,
]

# BX10P_SINCE_P_TH: Since Eventuality Extraction
# Paper axiom UE, Since-indexed dual (via TR): (guard \since event) -> past(event), written
# guard-first as "(A \Since B) -> past B" with guard=A, event=B, mirroring BX10_UNTIL_F_TH.
# Formula: (A \Since B) -> past B, instantiating UE's Since dual with guard=A, event=B.
BX10P_SINCE_P_TH_premises = []
BX10P_SINCE_P_TH_conclusions = ['((A \\Since B) \\rightarrow \\past B)']
BX10P_SINCE_P_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
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
# Formula: F(phi) -> (top \Until phi)  i.e. F(A) -> (\neg\bot \Until A)
# Note: \top = \neg \bot (explicit expansion to avoid TopOperator bug)
BX12_F_UNTIL_TH_premises = []
BX12_F_UNTIL_TH_conclusions = ['(\\future A \\rightarrow (\\neg \\bot \\Until A))']
BX12_F_UNTIL_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
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
# Formula: P(phi) -> (top \Since phi)  i.e. P(A) -> (\neg\bot \Since A)
# Note: \top = \neg \bot (explicit expansion to avoid TopOperator bug)
BX12P_P_SINCE_TH_premises = []
BX12P_P_SINCE_TH_conclusions = ['(\\past A \\rightarrow (\\neg \\bot \\Since A))']
BX12P_P_SINCE_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
    'expectation' : False,
}
BX12P_P_SINCE_TH_example = [
    BX12P_P_SINCE_TH_premises,
    BX12P_P_SINCE_TH_conclusions,
    BX12P_P_SINCE_TH_settings,
]

# MF_MODAL_FUTURE_TH: Modal-Temporal Interaction (paper axiom MF)
# BX name: modal_future (Layer 4)
# Formula: Box phi -> Box(G phi)  i.e. Box A -> Box(Future A)
# NOTE: This is the same pattern as BM_TH_5, adding canonical Layer 4 name.
# Phase 17: previously excluded via KNOWN_TIMEOUT_EXAMPLES (the retired encoding reported a
# spurious countermodel at N=1, M=2 -- see test_bimodal.py's own comment on this entry).
# Under the certificate encoding, decides `match` in ~3ms at these defaults (2026-09-25).
MF_MODAL_FUTURE_TH_premises = []
MF_MODAL_FUTURE_TH_conclusions = ['(\\Box A \\rightarrow \\Box \\Future A)']
MF_MODAL_FUTURE_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
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
# Formula: (phi \Until psi) -> ((phi and (phi \Until psi)) \Until psi)
# i.e. (A \Until B) -> ((A and (A \Until B)) \Until B)
BX5_ACCUM_U_TH_premises = []
BX5_ACCUM_U_TH_conclusions = ['((A \\Until B) \\rightarrow ((A \\wedge (A \\Until B)) \\Until B))']
BX5_ACCUM_U_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from the retired encoding's budget; measured <50ms under the certificate encoding (Phase 19, 2026-09-25).
    'expectation' : False,
}
BX5_ACCUM_U_TH_example = [
    BX5_ACCUM_U_TH_premises,
    BX5_ACCUM_U_TH_conclusions,
    BX5_ACCUM_U_TH_settings,
]

# BX5P_ACCUM_S_TH: Since Self-Accumulation
# BX name: self_accum_since
# Formula: (phi \Since psi) -> ((phi and (phi \Since psi)) \Since psi)
# i.e. (A \Since B) -> ((A and (A \Since B)) \Since B)
BX5P_ACCUM_S_TH_premises = []
BX5P_ACCUM_S_TH_conclusions = ['((A \\Since B) \\rightarrow ((A \\wedge (A \\Since B)) \\Since B))']
BX5P_ACCUM_S_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from the retired encoding's budget; measured <50ms under the certificate encoding (Phase 19, 2026-09-25).
    'expectation' : False,
}
BX5P_ACCUM_S_TH_example = [
    BX5P_ACCUM_S_TH_premises,
    BX5P_ACCUM_S_TH_conclusions,
    BX5P_ACCUM_S_TH_settings,
]

# BX6_ABSORB_U_TH: Until Absorption
# BX name: absorb_until
# Formula: (phi \Until (phi and (phi \Until psi))) -> (phi \Until psi)
# i.e. (A \Until (A and (A \Until B))) -> (A \Until B)
BX6_ABSORB_U_TH_premises = []
BX6_ABSORB_U_TH_conclusions = ['((A \\Until (A \\wedge (A \\Until B))) \\rightarrow (A \\Until B))']
BX6_ABSORB_U_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from the retired encoding's budget; measured <50ms under the certificate encoding (Phase 19, 2026-09-25).
    'expectation' : False,
}
BX6_ABSORB_U_TH_example = [
    BX6_ABSORB_U_TH_premises,
    BX6_ABSORB_U_TH_conclusions,
    BX6_ABSORB_U_TH_settings,
]

# BX6P_ABSORB_S_TH: Since Absorption
# BX name: absorb_since
# Formula: (phi \Since (phi and (phi \Since psi))) -> (phi \Since psi)
# i.e. (A \Since (A and (A \Since B))) -> (A \Since B)
BX6P_ABSORB_S_TH_premises = []
BX6P_ABSORB_S_TH_conclusions = ['((A \\Since (A \\wedge (A \\Since B))) \\rightarrow (A \\Since B))']
BX6P_ABSORB_S_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from the retired encoding's budget; measured <50ms under the certificate encoding (Phase 19, 2026-09-25).
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from the retired encoding's budget; measured <50ms under the certificate encoding (Phase 19, 2026-09-25).
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
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from the retired encoding's budget; measured <50ms under the certificate encoding (Phase 19, 2026-09-25).
    'expectation' : False,
}
BX11P_LIN_P_TH_example = [
    BX11P_LIN_P_TH_premises,
    BX11P_LIN_P_TH_conclusions,
    BX11P_LIN_P_TH_settings,
]

# BX13_ENRICH_U_TH: Until Enrichment
# BX name: enrichment_until
# Formula: p and (phi \Until psi) -> (phi \Until (psi and (phi \Since p)))
# i.e. C and (A \Until B) -> (A \Until (B and (A \Since C)))
BX13_ENRICH_U_TH_premises = []
BX13_ENRICH_U_TH_conclusions = ['((C \\wedge (A \\Until B)) \\rightarrow (A \\Until (B \\wedge (A \\Since C))))']
BX13_ENRICH_U_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from the retired encoding's budget; measured <50ms under the certificate encoding (Phase 19, 2026-09-25).
    'expectation' : False,
}
BX13_ENRICH_U_TH_example = [
    BX13_ENRICH_U_TH_premises,
    BX13_ENRICH_U_TH_conclusions,
    BX13_ENRICH_U_TH_settings,
]

# BX13P_ENRICH_S_TH: Since Enrichment
# BX name: enrichment_since
# Formula: p and (phi \Since psi) -> (phi \Since (psi and (phi \Until p)))
# i.e. C and (A \Since B) -> (A \Since (B and (A \Until C)))
BX13P_ENRICH_S_TH_premises = []
BX13P_ENRICH_S_TH_conclusions = ['((C \\wedge (A \\Since B)) \\rightarrow (A \\Since (B \\wedge (A \\Until C))))']
BX13P_ENRICH_S_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from the retired encoding's budget; measured <50ms under the certificate encoding (Phase 19, 2026-09-25).
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
# Formula: (phi \Until psi) and (chi \Until theta) ->
#          ((phi and chi) \Until (psi and theta)) or
#          ((phi and chi) \Until (psi and chi)) or
#          ((phi and chi) \Until (phi and theta))
# Where: psi=B, phi=A, theta=D, chi=C (binary infix form)
# Phase 17: previously excluded via KNOWN_TIMEOUT_EXAMPLES under the retired encoding's
# N=4/M=5 window cost. Under the certificate encoding, decides `match` in ~5ms at the
# default segment lengths (2026-09-25); max_time lowered from 60s to the floor.
BX7_LINEAR_U_TH_premises = []
BX7_LINEAR_U_TH_conclusions = [
    '(((A \\Until B) \\wedge (C \\Until D)) \\rightarrow '
    '(((A \\wedge C) \\Until (B \\wedge D)) \\vee '
    '(((A \\wedge C) \\Until (B \\wedge C)) \\vee '
    '((A \\wedge C) \\Until (A \\wedge D)))))'
]
BX7_LINEAR_U_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,
    'expectation' : False,
}
BX7_LINEAR_U_TH_example = [
    BX7_LINEAR_U_TH_premises,
    BX7_LINEAR_U_TH_conclusions,
    BX7_LINEAR_U_TH_settings,
]

# BX7P_LINEAR_S_TH: Since Linearity (4 variables)
# BX name: linear_since
# Formula: (phi \Since psi) and (chi \Since theta) ->
#          ((phi and chi) \Since (psi and theta)) or
#          ((phi and chi) \Since (psi and chi)) or
#          ((phi and chi) \Since (phi and theta))
BX7P_LINEAR_S_TH_premises = []
BX7P_LINEAR_S_TH_conclusions = [
    '(((A \\Since B) \\wedge (C \\Since D)) \\rightarrow '
    '(((A \\wedge C) \\Since (B \\wedge D)) \\vee '
    '(((A \\wedge C) \\Since (B \\wedge C)) \\vee '
    '((A \\wedge C) \\Since (A \\wedge D)))))'
]
BX7P_LINEAR_S_TH_settings = {
    'back' : 2,
    'mid' : 1,
    'fwd' : 2,
    'max_time' : 10,  # Lowered from 60s: Phase 17 measured ~5ms at these defaults
                      # (2026-09-25), matching BX7_LINEAR_U_TH's measurement.
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
    "BM_TH_5" : BM_TH_5_example,

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

# Required by theory_lib.get_test_examples('bimodal') -- see THEORY_ARCHITECTURE.md's Examples
# Contract; the other three theories assign this the same way (aliasing unit_tests).
test_example_range = unit_tests

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
    "TN_CM_2" : TN_CM_2_example,

    # Bimodal Countermodel
    "BM_CM_1" : BM_CM_1_example,
    "BM_CM_2" : BM_CM_2_example,
    "BM_CM_3" : BM_CM_3_example,
    "BM_CM_4" : BM_CM_4_example,

    ### THEOREMS ###

    # Extensional Theorems
    "EX_TH_1" : EX_TH_1_example,

    # Modal Theorems
    "MD_TH_1" : MD_TH_1_example,
    "MD_TH_2" : MD_TH_2_example,

    # Tense Theorems
    "TN_TH_2" : TN_TH_2_example,

    # Bimodal Theorems (all five decide correctly under the certificate encoding at the
    # default back=2/mid=1/fwd=2 segment lengths, well under 50ms each -- measured
    # 2026-09-25; no segment lengths needed raising, see Phase 17's plan record)
    "BM_TH_1" : BM_TH_1_example,
    "BM_TH_2" : BM_TH_2_example,
    "BM_TH_3" : BM_TH_3_example,
    "BM_TH_4" : BM_TH_4_example,
    "BM_TH_5" : BM_TH_5_example,

    # BX Axiom System (Layer 3/4): the three examples the retired encoding excluded for
    # solver-cost reasons all decide correctly at the default segment lengths, well under
    # 50ms each, under the certificate encoding -- measured 2026-09-25.
    "MF_MODAL_FUTURE_TH" : MF_MODAL_FUTURE_TH_example,
    "BX7_LINEAR_U_TH" : BX7_LINEAR_U_TH_example,
    "BX7P_LINEAR_S_TH" : BX7P_LINEAR_S_TH_example,
}


# The report will be printed by ModelRunner after all examples complete
# No atexit registration needed - the runner controls when reports print
