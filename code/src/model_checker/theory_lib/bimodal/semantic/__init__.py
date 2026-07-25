"""Bimodal semantic package.

Re-exports the semantic classes implemented in `core.py`. This package
previously shadowed a sibling `semantic.py` and loaded it a second time
under a synthetic module identity (`bimodal_semantic_module`) via
`importlib.util.spec_from_file_location`, purely to work around the
`semantic/` directory name colliding with `semantic.py`. That flat file has
been moved into `core.py` (verbatim), so `BimodalSemantics`,
`BimodalProposition`, and `BimodalStructure` now have exactly one class
identity, importable and picklable via this package's real module path --
no dynamic loader or `sys.modules` registration required.
"""

from .core import BimodalSemantics, BimodalProposition, BimodalStructure

__all__ = ['BimodalSemantics', 'BimodalProposition', 'BimodalStructure']
