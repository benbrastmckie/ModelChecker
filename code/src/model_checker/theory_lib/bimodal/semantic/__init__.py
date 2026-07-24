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
# Register in sys.modules BEFORE exec_module. Without this, the module is
# fully usable in-process (classes defined here have __module__ ==
# "bimodal_semantic_module" and work fine for normal attribute access), but
# it does not exist as an importable name anywhere. That breaks pickling
# under ProcessPoolExecutor (used by --maximize theory comparison): pickle
# serializes an instance's class by module name + qualname and the
# unpickling worker process looks up "bimodal_semantic_module" in
# sys.modules to resolve it, raising
# `ModuleNotFoundError: No module named 'bimodal_semantic_module'` and
# silently failing the whole example (reported as "Maximum N = 0").
sys.modules[spec.name] = semantic_module
spec.loader.exec_module(semantic_module)

# Export the classes from semantic.py
BimodalSemantics = semantic_module.BimodalSemantics
BimodalProposition = semantic_module.BimodalProposition
BimodalStructure = semantic_module.BimodalStructure

__all__ = ['BimodalSemantics', 'BimodalProposition', 'BimodalStructure']
