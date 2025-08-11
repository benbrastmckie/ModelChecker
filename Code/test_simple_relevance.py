"""Simple relevance test for iterator debugging."""

import sys
import os

# Add parent directories to path
current_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(current_dir, 'src')
if src_dir not in sys.path:
    sys.path.insert(0, src_dir)

from model_checker.theory_lib.logos.semantic import LogosSemantics
from model_checker.theory_lib.logos.syntax import LogosSyntax  
from model_checker.theory_lib.logos.model_constraints import LogosModelConstraints
from model_checker.builder.build_example import BuildExample
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry

# Create a simple relevance example
premises = []
conclusions = ['(A \\wedge B)']  # Looking for countermodel
settings = {
    'N': 2,  # 2 states
    'iterate': 2,  # Find 2 models
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'expectation': True,  # Expect countermodel
}

example_definition = [premises, conclusions, settings]

# Default settings
general_settings = {
    "print_constraints": False,
    "constraint_engine": "Z3_bitvec_structured",
}

# Unit tests to run
unit_tests = {
    "SIMPLE_TEST": example_definition
}

example_range = unit_tests