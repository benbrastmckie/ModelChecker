"""Test script to run specific examples from the incremental exclusion theory."""

from .examples import DN_ELIM_example, exclusion_theory, general_settings

# Run just the double negation elimination example
example_range = {
    "Double Negation Elimination": DN_ELIM_example,
}

# Which semantic theories to compare
semantic_theories = {
    "exclusion_theory": exclusion_theory,
}

# Override general settings to print more details
general_settings["print_constraints"] = True

if __name__ == "__main__":
    # This allows the module to be run with dev_cli.py
    pass