"""
Unified Examples Module for Logos Theory

This module aggregates examples from all logos subtheories into a unified 
`test_example_range` dictionary that can be used by test_theories.py.

The logos theory is modular, with examples distributed across subtheories:
- Extensional: Truth-functional operators (¬,∧,∨,→,↔,⊤,⊥)
- Modal: Necessity and possibility operators (□,◇,CFBox,CFDiamond)
- Constitutive: Ground, essence, and identity operators (≡,≤,⊑,≼,⊓)
- Counterfactual: Counterfactual conditional operators (□→,◇→,⊙,♦)
- Relevance: Content-sensitive relevance operators (≺)

This module imports and combines all subtheory examples with prefixed names
to avoid conflicts and maintain traceability back to the originating subtheory.

Usage:
------
This module provides the examples needed for test_theories.py integration:

```bash
# Run all logos theory tests  
./test_theories.py --theories logos -v

# Access examples programmatically
from model_checker.theory_lib.logos.examples import test_example_range
```

Example Name Prefixes:
- EXT_*: Extensional examples  
- MOD_*: Modal examples
- CON_*: Constitutive examples (Note: renamed from CL_* to CON_* for consistency)
- CF_*: Counterfactual examples
- REL_*: Relevance examples
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

try:
    from .subtheories.relevance.examples import relevance_examples
except ImportError:
    relevance_examples = {}

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

# Aggregate all examples (subtheories already have prefixes)
# Note: Constitutive examples use CL_* prefix in their files but we convert to CON_* for consistency
test_example_range = {
    **extensional_examples,  # Already has EXT_ prefix
    **modal_examples,        # Already has MOD_ prefix
    **{k.replace('CL_', 'CON_'): v for k, v in constitutive_examples.items()},  # Convert CL_* to CON_*
    **counterfactual_examples,  # Already has CF_ prefix
    **relevance_examples,       # Already has REL_ prefix
}

# Also include basic examples for validation
test_example_range.update(basic_logos_examples)

# For backward compatibility
all_logos_examples = test_example_range

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
logos_registry.load_subtheories(['extensional', 'modal', 'constitutive', 'counterfactual', 'relevance'])

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

# Default example range (for compatibility with existing framework)
example_range = test_example_range

# Provide access to individual subtheory example collections
subtheory_examples = {
    'extensional': extensional_examples,
    'modal': modal_examples,
    'constitutive': constitutive_examples,
    'counterfactual': counterfactual_examples,
    'relevance': relevance_examples,
}

# Helper function to get examples by subtheory
def get_examples_by_subtheory(subtheory_name):
    """
    Get examples from a specific subtheory.
    
    Args:
        subtheory_name (str): Name of the subtheory ('extensional', 'modal', etc.)
        
    Returns:
        dict: Examples from the specified subtheory
        
    Raises:
        ValueError: If subtheory_name is not valid
    """
    if subtheory_name not in subtheory_examples:
        valid_names = list(subtheory_examples.keys())
        raise ValueError(f"Invalid subtheory '{subtheory_name}'. Valid options: {valid_names}")
    
    return subtheory_examples[subtheory_name]

# Helper function to get examples by type (countermodel vs theorem)
def get_examples_by_type(example_type='all'):
    """
    Get examples filtered by type.
    
    Args:
        example_type (str): 'countermodel' (CM), 'theorem' (TH), or 'all'
        
    Returns:
        dict: Filtered examples
    """
    if example_type == 'all':
        return test_example_range
    elif example_type == 'countermodel':
        return {k: v for k, v in test_example_range.items() if '_CM_' in k}
    elif example_type == 'theorem':  
        return {k: v for k, v in test_example_range.items() if '_TH_' in k or '_DEF_' in k or 'LOGOS_BASIC_' in k}
    else:
        raise ValueError("example_type must be 'countermodel', 'theorem', or 'all'")

# Statistics about the examples
def get_example_stats():
    """
    Get statistics about the example distribution across subtheories.
    
    Returns:
        dict: Statistics including counts per subtheory and total examples
    """
    stats = {
        'extensional': len(extensional_examples),
        'modal': len(modal_examples),
        'constitutive': len(constitutive_examples),
        'counterfactual': len(counterfactual_examples),
        'relevance': len(relevance_examples),
        'basic': len(basic_logos_examples),
        'total': len(test_example_range)
    }
    return stats

# Make this module runnable from the command line for testing
if __name__ == '__main__':
    # Print example statistics
    stats = get_example_stats()
    print("Logos Theory Example Statistics:")
    print("=" * 40)
    for subtheory, count in stats.items():
        if subtheory != 'total':
            print(f"{subtheory.capitalize()}: {count} examples")
    print(f"Total: {stats['total']} examples")
    
    # Optionally run the unified examples through model-checker
    file_name = os.path.basename(__file__)
    parent_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    print(f"\nTo test examples, run: ./dev_cli.py {file_name}")