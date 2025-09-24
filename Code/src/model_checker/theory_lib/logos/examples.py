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

import os
import sys

from .operators import LogosOperatorRegistry
from .semantic import LogosSemantics, LogosProposition, LogosModelStructure
from .subtheories.constitutive import examples as con_module
from .subtheories.constitutive.examples import example_range as constitutive_examples
from .subtheories.constitutive.examples import unit_tests as constitutive_all_examples
from .subtheories.counterfactual import examples as cf_module
from .subtheories.counterfactual.examples import example_range as counterfactual_examples
from .subtheories.counterfactual.examples import unit_tests as counterfactual_all_examples
from .subtheories.extensional import examples as ext_module
from .subtheories.extensional.examples import example_range as extensional_examples
from .subtheories.extensional.examples import unit_tests as extensional_all_examples
from .subtheories.modal import examples as mod_module
from .subtheories.modal.examples import example_range as modal_examples
from .subtheories.modal.examples import unit_tests as modal_all_examples
from .subtheories.relevance import examples as rel_module
from .subtheories.relevance.examples import example_range as relevance_examples
from .subtheories.relevance.examples import unit_tests as relevance_all_examples





# Standard imports for example modules

# Add current directory to path for subtheory imports
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Import semantic classes - already imported above from .semantic

# Import operators

# Import subtheory examples from their example_range (selected examples to run)

# Store example metadata for reporting
example_metadata = {}

try:
    for key in extensional_examples:
        example_metadata[key] = {
            'subtheory': 'extensional',
            'path': os.path.abspath(ext_module.__file__)
        }
except ImportError:
    extensional_examples = {}

try:
    for key in modal_examples:
        example_metadata[key] = {
            'subtheory': 'modal',
            'path': os.path.abspath(mod_module.__file__)
        }
except ImportError:
    modal_examples = {}

try:
    for key in constitutive_examples:
        example_metadata[key] = {
            'subtheory': 'constitutive',
            'path': os.path.abspath(con_module.__file__)
        }
except ImportError:
    constitutive_examples = {}

try:
    for key in counterfactual_examples:
        example_metadata[key] = {
            'subtheory': 'counterfactual',
            'path': os.path.abspath(cf_module.__file__)
        }
except ImportError:
    counterfactual_examples = {}

try:
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
# All subtheory imports are already loaded above - no need for try/except blocks

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

# The report will be printed by ModelRunner after all examples complete
# No atexit registration needed - the runner controls when reports print
