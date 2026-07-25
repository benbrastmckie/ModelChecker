"""Bimodal semantic package.

This package implements the semantic framework for bimodal logic (combined
modal and temporal operators), split into focused modules matching the
layout used by the exclusion, imposition, and logos theories.

Re-export-only per docs/THEORY_ARCHITECTURE.md's Theory Contract: the actual class bodies
live in core.py (BimodalSemantics), proposition.py (BimodalProposition), and model.py
(BimodalStructure).

This package previously shadowed a sibling `semantic.py` and loaded it a second time
under a synthetic module identity (`bimodal_semantic_module`) via
`importlib.util.spec_from_file_location`, purely to work around the `semantic/`
directory name colliding with `semantic.py`. That flat file was moved into this
package (first verbatim into `core.py`, then split into the three files above), so
`BimodalSemantics`, `BimodalProposition`, and `BimodalStructure` now have exactly one
class identity, importable and picklable via this package's real module path -- no
dynamic loader or `sys.modules` registration required.
"""

from .core import BimodalSemantics
from .proposition import BimodalProposition
from .model import BimodalStructure

__all__ = ['BimodalSemantics', 'BimodalProposition', 'BimodalStructure']
