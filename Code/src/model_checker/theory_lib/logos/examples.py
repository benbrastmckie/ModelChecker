"""
Examples Module for Logos Theory

This module aggregates examples from all logos subtheories and provides
unified access to comprehensive test cases across extensional, modal,
constitutive, and counterfactual logic domains.

The examples follow the pattern established by the default theory examples,
with proper formatting and operator usage for the model-checker framework.
"""

# Standard imports for example modules
import sys
import os

# Add current directory to path for subtheory imports
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Import semantic classes
from .semantic import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
)

# Import operators
from .operators import LogosOperatorRegistry

# Import subtheory examples
try:
    from .subtheories.extensional.examples import extensional_examples
except ImportError:
    extensional_examples = {}

try:
    from .subtheories.modal.examples import modal_examples
except ImportError:
    modal_examples = {}

try:
    from .subtheories.constitutive.examples import constitutive_examples
except ImportError:
    constitutive_examples = {}

try:
    from .subtheories.counterfactual.examples import counterfactual_examples
except ImportError:
    counterfactual_examples = {}

# Basic test examples for logos theory validation
basic_logos_examples = {
    # Quick validation tests
    "LOGOS_BASIC_MODUS_PONENS": [
        ["A", "A \\rightarrow B"],  # premises
        ["B"],                      # conclusions
        {"N": 3, "contingent": False, "max_time": 1, "expectation": False}
    ],
    
    "LOGOS_BASIC_CONJUNCTION": [
        ["A", "B"],
        ["A \\wedge B"],
        {"N": 3, "contingent": False, "max_time": 1, "expectation": False}
    ],
    
    "LOGOS_BASIC_TAUTOLOGY": [
        [],
        ["\\top"],
        {"N": 3, "contingent": False, "max_time": 1, "expectation": False}
    ],
    
    "LOGOS_BASIC_EXCLUDED_MIDDLE": [
        [],
        ["A \\vee \\neg A"],
        {"N": 3, "contingent": False, "max_time": 1, "expectation": False}
    ],
    
    "LOGOS_BASIC_MODAL_K": [
        ["\\Box (A \\rightarrow B)", "\\Box A"],
        ["\\Box B"],
        {"N": 4, "contingent": False, "max_time": 2, "expectation": False}
    ],
    
    "LOGOS_BASIC_IDENTITY_REFLEXIVE": [
        [],
        ["A \\equiv A"],
        {"N": 4, "contingent": False, "max_time": 2, "expectation": False}
    ],
}

# Aggregate all examples from subtheories
all_logos_examples = {}
all_logos_examples.update(basic_logos_examples)
all_logos_examples.update(extensional_examples)
all_logos_examples.update(modal_examples)
all_logos_examples.update(constitutive_examples)
all_logos_examples.update(counterfactual_examples)

# Create collections by type
logos_cm_examples = {}
logos_th_examples = {}

# Separate countermodels and theorems
for name, example in all_logos_examples.items():
    if "_CM_" in name:
        logos_cm_examples[name] = example
    elif "_TH_" in name or "LOGOS_BASIC_" in name:
        logos_th_examples[name] = example
    else:
        # Default to theorem if unclear
        logos_th_examples[name] = example

# Combined collection (for compatibility)
logos_examples = all_logos_examples

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Create operator registry for full logos theory
logos_registry = LogosOperatorRegistry()
logos_registry.load_subtheories(['extensional', 'modal', 'constitutive', 'counterfactual'])

# Define the semantic theory
logos_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": logos_registry.get_operators(),
}

# Specify which theories to use
semantic_theories = {
    "Logos-Full": logos_theory,
}

# Quick test range for basic validation
test_example_range = {
    "LOGOS_BASIC_MODUS_PONENS": basic_logos_examples["LOGOS_BASIC_MODUS_PONENS"],
    "LOGOS_BASIC_TAUTOLOGY": basic_logos_examples["LOGOS_BASIC_TAUTOLOGY"],
    "LOGOS_BASIC_EXCLUDED_MIDDLE": basic_logos_examples["LOGOS_BASIC_EXCLUDED_MIDDLE"],
}

# Default example range (for compatibility with existing framework)
example_range = test_example_range

# Examples by subtheory for selective testing
extensional_only_examples = {}
modal_only_examples = {}
constitutive_only_examples = {}
counterfactual_only_examples = {}

# Populate subtheory-specific collections
for name, example in all_logos_examples.items():
    if name.startswith("EXT_"):
        extensional_only_examples[name] = example
    elif name.startswith("MOD_"):
        modal_only_examples[name] = example
    elif name.startswith("CON_"):
        constitutive_only_examples[name] = example
    elif name.startswith("CF_"):
        counterfactual_only_examples[name] = example

# Helper functions for accessing examples
def get_examples_by_subtheory(subtheory_name):
    """Get examples for a specific subtheory."""
    if subtheory_name == "extensional":
        return extensional_only_examples
    elif subtheory_name == "modal":
        return modal_only_examples
    elif subtheory_name == "constitutive":
        return constitutive_only_examples
    elif subtheory_name == "counterfactual":
        return counterfactual_only_examples
    else:
        return {}

def get_examples_by_type(example_type):
    """Get examples by type (countermodel or theorem)."""
    if example_type == "countermodel" or example_type == "cm":
        return logos_cm_examples
    elif example_type == "theorem" or example_type == "th":
        return logos_th_examples
    else:
        return all_logos_examples

def get_basic_examples():
    """Get basic validation examples."""
    return basic_logos_examples

def get_all_examples():
    """Get all logos examples."""
    return all_logos_examples

# Statistics
def print_example_statistics():
    """Print statistics about available examples."""
    total = len(all_logos_examples)
    theorems = len(logos_th_examples)
    countermodels = len(logos_cm_examples)
    
    by_subtheory = {
        "extensional": len(extensional_only_examples),
        "modal": len(modal_only_examples),
        "constitutive": len(constitutive_only_examples),
        "counterfactual": len(counterfactual_only_examples),
        "basic": len(basic_logos_examples)
    }
    
    print(f"Logos Theory Examples Statistics:")
    print(f"  Total examples: {total}")
    print(f"  Theorems: {theorems}")
    print(f"  Countermodels: {countermodels}")
    print(f"  By subtheory:")
    for subtheory, count in by_subtheory.items():
        print(f"    {subtheory}: {count}")

# Make this module runnable from the command line
if __name__ == '__main__':
    print_example_statistics()
    
    # Run a quick test
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)