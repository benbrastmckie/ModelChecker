#!/usr/bin/env python3
"""Test script to verify imposition relation printing."""

from model_checker import BuildExample
from model_checker.theory_lib.imposition import get_theory

# Get the imposition theory
theory = get_theory()

# Create a simple example
example = BuildExample(
    "test_imposition",
    theory,
    premises=['A'],
    conclusions=['A \\imposition B'],
    settings={'N': 2, 'expectation': False}
)

# Find and print the countermodel
print("Testing imposition relation printing...")
print("="*60)
example.print_model()