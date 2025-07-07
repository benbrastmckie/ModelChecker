"""Debug witness constraint generation."""

import sys
import os
sys.path.insert(0, os.path.abspath('../../../..'))

import z3
from model_checker.theory_lib.exclusion.attempt6_incremental.semantic import ExclusionSemantics, UnilateralProposition
from model_checker.theory_lib.exclusion.attempt6_incremental.operators import exclusion_operators
from model_checker.theory_lib.exclusion.attempt6_incremental.incremental_model import WitnessStore, IncrementalVerifier
from model_checker.theory_lib.exclusion.attempt6_incremental.truth_cache import TruthCache
from model_checker import syntactic
from model_checker.model import ModelConstraints

# Settings
settings = {
    "N": 2,
    "max_time": 10,
    "expectation": True,
    "contingent": False,
    "non_empty": False,
    "non_null": False,
    "disjoint": False,
    "fusion_closure": False
}

# Create components
semantics = ExclusionSemantics(settings)
solver = z3.Solver()
witness_store = WitnessStore()
truth_cache = TruthCache(semantics)
verifier = IncrementalVerifier(semantics, solver, witness_store, truth_cache)

# Create exclusion formula
syntax = syntactic.Syntax(['\\exclude A'], ['A'], exclusion_operators)
model_constraints = ModelConstraints(settings, syntax, semantics, UnilateralProposition)
sentence = model_constraints.syntax.premises[0]
eval_point = {'world': z3.BitVecVal(2, 2)}

print(f"Sentence: {sentence}")
print(f"Operator: {sentence.operator}")
print(f"Operator name: {sentence.operator.name}")

# Register witnesses for the exclusion operator
verifier._register_sentence_witnesses(sentence)

# Check what was registered
print(f"\nWitness store skolem witnesses: {list(witness_store.skolem_witnesses.keys())}")

# Get the exclusion operator
exclusion_op = sentence.operator
h_name = f"h_sk_{id(exclusion_op)}"
y_name = f"y_sk_{id(exclusion_op)}"

print(f"\nExpected h_name: {h_name}")
print(f"Expected y_name: {y_name}")

# Add some witness mappings to simulate previous solving
if h_name in witness_store.skolem_witnesses:
    witness_store.skolem_witnesses[h_name]['values'] = {0: 1, 1: 2, 2: 3, 3: 0}
    witness_store.skolem_witnesses[h_name]['complete'] = True
    print(f"Added h mappings")
    
if y_name in witness_store.skolem_witnesses:
    witness_store.skolem_witnesses[y_name]['values'] = {0: 0, 1: 1, 2: 0, 3: 1}
    witness_store.skolem_witnesses[y_name]['complete'] = True
    print(f"Added y mappings")

# Generate constraints - should now include witness constraints
print(f"\nGenerating constraints...")
constraints = list(verifier._constraint_generator(sentence, eval_point))

print(f"\nNumber of constraint batches: {len(constraints)}")

# Check each batch
for i, batch in enumerate(constraints):
    print(f"\nBatch {i}:")
    for constraint, label in batch:
        print(f"  Label: {label}")
        if "witness" in label:
            print(f"    -> This is a witness constraint!")