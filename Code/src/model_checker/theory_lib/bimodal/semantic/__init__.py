"""Bimodal semantic components for witness predicates.

This package provides witness predicate infrastructure as a submodule.
It re-exports the main semantic classes from the parent module for backward compatibility.
"""

# Re-export main semantic classes from parent semantic.py module
# This maintains backward compatibility when semantic/ directory shadows semantic.py
import sys
import importlib.util
from pathlib import Path

# Load the parent semantic.py module directly
parent_dir = Path(__file__).parent.parent
semantic_py_path = parent_dir / "semantic.py"

spec = importlib.util.spec_from_file_location("bimodal_semantic_module", semantic_py_path)
semantic_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(semantic_module)

# Export the classes from semantic.py
BimodalSemantics = semantic_module.BimodalSemantics
BimodalProposition = semantic_module.BimodalProposition
BimodalStructure = semantic_module.BimodalStructure

__all__ = ['BimodalSemantics', 'BimodalProposition', 'BimodalStructure']
