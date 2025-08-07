"""Constraint verification script for debugging iterator constraint preservation issue."""

import sys
import os

# Add src directory to path for imports
current_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(current_dir, 'src')
if src_dir not in sys.path:
    sys.path.insert(0, src_dir)

import z3
from model_checker.theory_lib.logos.semantic import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
)
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker import Syntax, ModelConstraints

# Create operator registry
logos_registry = LogosOperatorRegistry()
logos_registry.load_subtheories(['extensional', 'modal'])

# Define theory
logos_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": logos_registry.get_operators(),
}

print("=== Constraint Verification Script ===\n")

# Test 1: Single atomic premise A
print("TEST 1: Premise 'A', no conclusions")
print("-" * 40)

# Build components manually
premises = ['A']
conclusions = []
settings = {
    'N': 2,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 10,
    'iterate': 2,
    'expectation': True,
}

# Create syntax
syntax = Syntax(premises, conclusions, logos_theory["operators"])

# Create semantics
semantics = LogosSemantics(settings)

# Create model constraints
model_constraints = ModelConstraints(
    settings,
    syntax,
    semantics,
    LogosProposition,
)

print(f"Number of constraints:")
print(f"  Frame constraints: {len(model_constraints.frame_constraints)}")
print(f"  Model constraints: {len(model_constraints.model_constraints)}")
print(f"  Premise constraints: {len(model_constraints.premise_constraints)}")
print(f"  Conclusion constraints: {len(model_constraints.conclusion_constraints)}")
print(f"  Total constraints: {len(model_constraints.all_constraints)}")
print()

# Examine premise constraints
print("Premise constraints:")
for i, pc in enumerate(model_constraints.premise_constraints):
    print(f"  {i+1}. {pc}")
    # Try to understand the constraint structure
    if hasattr(pc, 'decl'):
        print(f"     Declaration: {pc.decl()}")
    if hasattr(pc, 'children'):
        print(f"     Children: {pc.children()}")
print()

# Check evaluation world
print(f"Main world variable: {model_constraints.semantics.main_world}")
print(f"Main point: {model_constraints.semantics.main_point}")
print()

print("\n=== Deep Constraint Analysis ===")
print("-" * 40)

# Get the premise sentence
premise_sent = syntax.premises[0]
print(f"Premise sentence: {premise_sent}")
print(f"Premise sentence type: {type(premise_sent)}")

# Call premise_behavior
premise_constraint = semantics.premise_behavior(premise_sent)
print(f"\nPremise behavior constraint: {premise_constraint}")
print(f"Constraint type: {type(premise_constraint)}")

# Try to understand the constraint
if hasattr(premise_constraint, 'decl'):
    print(f"Declaration: {premise_constraint.decl()}")
if hasattr(premise_constraint, 'arg'):
    print(f"Arguments: {[premise_constraint.arg(i) for i in range(premise_constraint.num_args())]}")

# Let's also check what true_at does
print("\n=== Understanding true_at ===")
print("-" * 40)

# The premise is a Sentence object, we need to check its proposition
if hasattr(premise_sent, 'proposition'):
    prop = premise_sent.proposition
    print(f"Premise proposition: {prop}")
    print(f"Proposition type: {type(prop)}")
    
    # Call true_at directly
    main_point = semantics.main_point
    true_at_result = semantics.true_at(premise_sent, main_point)
    print(f"\ntrue_at result type: {type(true_at_result)}")
    print(f"true_at result: {true_at_result}")

print("\n=== Examining Z3 expressions ===")
print("-" * 40)

# Look at the actual Z3 constraint structure
print("Premise constraint breakdown:")
print(f"Full constraint: {premise_constraint}")
print(f"Is it a BoolRef? {isinstance(premise_constraint, z3.BoolRef)}")

# Try to simplify it
simplified = z3.simplify(premise_constraint)
print(f"Simplified: {simplified}")

# Check if it references main_world
main_world_str = str(semantics.main_world)
constraint_str = str(premise_constraint)
print(f"\nDoes constraint reference main_world '{main_world_str}'? {main_world_str in constraint_str}")

print("\n=== Summary ===")
print("The verification script has analyzed constraint generation.")
print("Key findings will help identify why MODEL 2+ violate premise constraints.")