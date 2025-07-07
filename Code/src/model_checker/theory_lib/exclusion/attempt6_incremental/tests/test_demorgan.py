"""Test DeMorgan's law: (A ∧ B) ⊢ ¬(¬A ∨ ¬B)"""

from .examples import exclusion_theory, general_settings

# Test the failing case
premises = ['(A \\uniwedge B)']
conclusions = ['\\exclude (\\exclude A \\univee \\exclude B)']

test_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,  # Actually expecting a countermodel based on exclusion semantics
}

test_example = [premises, conclusions, test_settings]

# Run just this example
example_range = {
    "DeMorgan Test": test_example,
}

# Which semantic theories to compare
semantic_theories = {
    "exclusion_theory": exclusion_theory,
}

# Override general settings to print more details
general_settings["print_constraints"] = False
general_settings["print_impossible"] = True

if __name__ == "__main__":
    # This allows the module to be run with dev_cli.py
    pass