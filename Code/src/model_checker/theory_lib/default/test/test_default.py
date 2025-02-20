"""run 'pytest' from the default_theory project directory."""

import pytest

from model_checker.builder import BuildExample, BuildModule
from model_checker.semantic import ModelStructure
from model_checker.syntactic import Syntax

from ..examples import (
    example_range,
    default_theory,
)


module = BuildModule

def test_examples(example_range, default_theory):

    semantics
    proposition
    operators
    dictionary

    for example_name, example_case in example_range.items():

        premises
        conclusions
        example_settings

        example_syntax = Syntax(premises, conclusions, operators)

        # Create model constraints
        model_constraints = ModelConstraints(
            settings,
            example_syntax,
            semantics(self.settings['N']),
            proposition,
        )

        # Create model structure
        model_structure = ModelStructure(
            model_constraints, 
            settings['max_time'],
        )

        return result.check_result

def test_CF_CM1():
# COUNTERFACTUAL ANTECEDENT STRENGTHENING
    premises = ['(A \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }

