#!/usr/bin/env python3
"""Direct test of imposition relation printing."""

import sys
sys.path.insert(0, '.')

from src.model_checker.theory_lib.imposition import get_theory
from src.model_checker import BuildExample

# Get the imposition theory
theory = get_theory()

# Create a simple example
example = BuildExample("test_imposition", theory,
    premises=['A'],
    conclusions=['A \\imposition B'],  # If A then must B
    settings={'N': 2, 'expectation': False}
)

# Check validity (should find a countermodel)
result = example.check_validity()
print(f"Valid: {result}")

# Print the model if we found a countermodel
if not result:
    example.print_model()