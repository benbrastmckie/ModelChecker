#!/usr/bin/env python3
"""Minimal debug script to understand CF_TH_4 discrepancy."""

# Define the example
premises = ['((A \\vee B) \\boxright C)']
conclusions = ['((A \\wedge B) \\boxright C)']
settings = {
    'N': 4,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}

# The issue: 
# Default theory: No countermodel (formula is valid)
# Logos theory: Countermodel found at world b.c

# In the countermodel:
# - (A ∨ B) □→ C is TRUE 
# - (A ∧ B) □→ C is FALSE

# Analysis of the countermodel:
# World b.c makes B and C true
# World a.d makes A true but C false (a.d is a falsifier of C)

# The key question: Why does default theory not find this countermodel?

print("CF_TH_4 Analysis:")
print("=================")
print("Formula: ((A ∨ B) □→ C) ⊢ ((A ∧ B) □→ C)")
print()
print("Countermodel found by logos at world b.c:")
print("- (A ∨ B) has verifiers that include both A-states and B-states")
print("- (A ∧ B) requires both A and B to be verified") 
print("- At world a.d: A is true, B is false, C is false")
print()
print("Key insight: The counterfactual (A ∧ B) □→ C can be false even when")
print("(A ∨ B) □→ C is true, because the conjunction requires both A and B")
print("to hold in the alternative worlds, while the disjunction only requires")
print("one of them.")