"""
Unified Examples Module for Logos Theory

This module aggregates examples from all logos subtheories into a unified 
`test_example_range` dictionary that can be used by test_theories.py.

The logos theory is modular, with examples distributed across subtheories:
- Extensional: Extensional operators (¬,∧,∨,→,↔,⊤,⊥)
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

# Import subtheory examples from their example_range (selected examples to run)
import os

# Store example metadata for reporting
example_metadata = {}

try:
    from .subtheories.extensional.examples import example_range as extensional_examples
    from .subtheories.extensional import examples as ext_module
    for key in extensional_examples:
        example_metadata[key] = {
            'subtheory': 'extensional',
            'path': os.path.abspath(ext_module.__file__)
        }
except ImportError:
    extensional_examples = {}

try:
    from .subtheories.modal.examples import example_range as modal_examples
    from .subtheories.modal import examples as mod_module
    for key in modal_examples:
        example_metadata[key] = {
            'subtheory': 'modal',
            'path': os.path.abspath(mod_module.__file__)
        }
except ImportError:
    modal_examples = {}

try:
    from .subtheories.constitutive.examples import example_range as constitutive_examples
    from .subtheories.constitutive import examples as con_module
    for key in constitutive_examples:
        example_metadata[key] = {
            'subtheory': 'constitutive',
            'path': os.path.abspath(con_module.__file__)
        }
except ImportError:
    constitutive_examples = {}

try:
    from .subtheories.counterfactual.examples import example_range as counterfactual_examples
    from .subtheories.counterfactual import examples as cf_module
    for key in counterfactual_examples:
        example_metadata[key] = {
            'subtheory': 'counterfactual',
            'path': os.path.abspath(cf_module.__file__)
        }
except ImportError:
    counterfactual_examples = {}

try:
    from .subtheories.relevance.examples import example_range as relevance_examples
    from .subtheories.relevance import examples as rel_module
    for key in relevance_examples:
        example_metadata[key] = {
            'subtheory': 'relevance',
            'path': os.path.abspath(rel_module.__file__)
        }
except ImportError:
    relevance_examples = {}

# Note: Basic examples removed as they are redundant with subtheory examples
# Modus ponens -> EXT_TH_1, Conjunction -> EXT_TH_3, etc.
# Modal logic K -> MOD_TH_*, Identity reflexive -> CON_TH_*

# Aggregate all examples (subtheories already have prefixes)
# Note: Constitutive examples use CL_* prefix in their files but we convert to CON_* for consistency
unit_tests = {
    **extensional_examples,  # Already has EXT_ prefix
    **modal_examples,        # Already has MOD_ prefix
    **{k.replace('CL_', 'CON_'): v for k, v in constitutive_examples.items()},  # Convert CL_* to CON_*
    **counterfactual_examples,  # Already has CF_ prefix
    **relevance_examples,       # Already has REL_ prefix
}

# Basic examples removed - see subtheory examples instead

# Aliases for main dictionary
test_example_range = unit_tests
all_logos_examples = unit_tests
example_range = unit_tests  # Required by get_examples() in theory_lib/__init__.py

# Organize examples by category
countermodel_examples = {}
theorem_examples = {}

# Separate countermodels and theorems
for name, example in all_logos_examples.items():
    if "_CM_" in name:
        countermodel_examples[name] = example
    elif "_TH_" in name:
        theorem_examples[name] = example
    else:
        # Default to theorem if unclear
        theorem_examples[name] = example

# Aliases for backward compatibility
logos_cm_examples = countermodel_examples
logos_th_examples = theorem_examples
logos_examples = all_logos_examples

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
    "sequential": False,
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
    "Primary": logos_theory,  # Logos hyperintensional semantics
}

# Default example range (for compatibility with existing framework)
example_range = unit_tests

# Provide access to individual subtheory example collections  
# Also import unit_tests for full access when needed
try:
    from .subtheories.extensional.examples import unit_tests as extensional_all_examples
except ImportError:
    extensional_all_examples = {}

try:
    from .subtheories.modal.examples import unit_tests as modal_all_examples
except ImportError:
    modal_all_examples = {}

try:
    from .subtheories.constitutive.examples import unit_tests as constitutive_all_examples
except ImportError:
    constitutive_all_examples = {}

try:
    from .subtheories.counterfactual.examples import unit_tests as counterfactual_all_examples
except ImportError:
    counterfactual_all_examples = {}

try:
    from .subtheories.relevance.examples import unit_tests as relevance_all_examples
except ImportError:
    relevance_all_examples = {}

subtheory_examples = {
    'extensional': extensional_examples,
    'modal': modal_examples,
    'constitutive': constitutive_examples,
    'counterfactual': counterfactual_examples,
    'relevance': relevance_examples,
}

# All examples from all subtheories (for testing frameworks that need full access)
all_subtheory_examples = {
    'extensional': extensional_all_examples,
    'modal': modal_all_examples,
    'constitutive': constitutive_all_examples,
    'counterfactual': counterfactual_all_examples,
    'relevance': relevance_all_examples,
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
        return unit_tests
    elif example_type == 'countermodel':
        return {k: v for k, v in unit_tests.items() if '_CM_' in k}
    elif example_type == 'theorem':  
        return {k: v for k, v in unit_tests.items() if '_TH_' in k or '_DEF_' in k}
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
        'basic': 0,
        'total': len(unit_tests)
    }
    return stats

def print_example_report():
    """
    Print a detailed report of all examples being run, organized by subtheory.
    Shows example names, their subtheory source, and file paths.
    """
    print("\n" + "=" * 80)
    print("LOGOS THEORY EXAMPLE REPORT")
    print("=" * 80)
    
    # Count active examples
    active_examples = len(example_range)
    total_available = len(unit_tests)
    
    print(f"\nActive Examples: {active_examples} of {total_available} available")
    
    # Group examples by subtheory
    by_subtheory = {}
    for example_name in example_range:
        if example_name in example_metadata:
            subtheory = example_metadata[example_name]['subtheory']
            if subtheory not in by_subtheory:
                by_subtheory[subtheory] = []
            by_subtheory[subtheory].append(example_name)
    
    # Print by subtheory
    if by_subtheory:
        print("\nExamples by Subtheory:")
        print("-" * 40)
        for subtheory in sorted(by_subtheory.keys()):
            examples = sorted(by_subtheory[subtheory])
            print(f"\n{subtheory.upper()} SUBTHEORY ({len(examples)} examples)")
            
            # Separate countermodels and theorems
            cms = [e for e in examples if '_CM_' in e]
            ths = [e for e in examples if '_TH_' in e]
            defs = [e for e in examples if '_DEF_' in e]
            
            if cms:
                print(f"  Countermodels: {', '.join(cms)}")
            if ths:
                print(f"  Theorems: {', '.join(ths)}")
            if defs:
                print(f"  Definitions: {', '.join(defs)}")
    
    # Print summary
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("-" * 40)
    
    total_cm = sum(1 for name in example_range if '_CM_' in name)
    total_th = sum(1 for name in example_range if '_TH_' in name)
    total_def = sum(1 for name in example_range if '_DEF_' in name)
    
    print(f"Total Examples: {active_examples}")
    print(f"  - Countermodels: {total_cm}")
    print(f"  - Theorems: {total_th}")
    if total_def > 0:
        print(f"  - Definitions: {total_def}")
    if by_subtheory:
        print(f"Subtheories Active: {len(by_subtheory)}")
    
    print("\n" + "-" * 80)
    print("Theory: Logos (Hyperintensional Bilateral Semantics)")
    print("Author: Benjamin Brast-McKie")
    print("Implementation: Benjamin Brast-McKie, Miguel Buitrago")
    print("-" * 80)
    
    print("\nThe examples above have been aggregated from the various subtheories that")
    print("comprise the Logos theory. Each subtheory's examples can also be run directly.")
    print()
    print("For more information, see:")
    print("  - Logos documentation: src/model_checker/theory_lib/logos/README.md")
    print("  - Subtheories documentation: src/model_checker/theory_lib/logos/subtheories/README.md")
    print("  - General usage guide: Docs/usage/README.md")
    print("=" * 80)

# Register the report to be printed at exit whenever this module is loaded
# Note: This will show whenever logos examples are run, even as dependencies
import atexit

# Ensure we only register once, even if module is imported multiple times
# Check if we've already registered by looking for our marker
if not hasattr(print_example_report, '_atexit_registered'):
    atexit.register(print_example_report)
    print_example_report._atexit_registered = True

# Make this module runnable from the command line for testing
if __name__ == '__main__':
    import sys
    
    # Check if we should just print the report without running examples
    if '--report-only' in sys.argv:
        print_example_report()
        sys.exit(0)
    
    stats = get_example_stats()
    print("Logos Theory Example Statistics:")
    print("=" * 40)
    for subtheory, count in stats.items():
        if subtheory != 'total':
            print(f"{subtheory.capitalize()}: {count} examples")
    print(f"Total: {stats['total']} examples")
    
    # Note: The report will be printed automatically at exit when examples finish
