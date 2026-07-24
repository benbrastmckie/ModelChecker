"""Upper-layer theory-aware API surface.

Per `theory_lib/docs/THEORY_ARCHITECTURE.md`'s Layering section, the upper layer
(`model_checker/__init__.py`, `model_checker/__main__.py`, `jupyter/`, and this module) is
the one place outside `theory_lib` itself that is permitted to import `theory_lib`. This
module exists specifically to hold theory-aware helpers that need that permission, so that
`utils/` -- which is core and must never import `theory_lib` -- doesn't have to.

`get_theory()` here is the theory-aware entry point: called with just a theory name, it
auto-loads that theory's `semantic_theories` mapping from `theory_lib` and then delegates
the actual by-name lookup to `utils.api.get_theory()`, which is the pure (theory-unaware)
version operating on an already-supplied mapping.
"""

from typing import Any, Dict, Optional

from .utils.api import get_theory as _lookup_theory

__all__ = ["get_theory"]


def get_theory(name: str, semantic_theories: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """Get a specific semantic theory by name.

    This function can be called in two ways:
    1. With just the theory name (e.g., 'default') - will automatically load the semantic
       theories from `theory_lib`.
    2. With both name and semantic_theories - useful when the caller already has the
       semantic theories loaded; delegates straight to the pure lookup.

    Args:
        name (str): Name of the theory to retrieve (e.g., 'default', 'exclusion')
        semantic_theories (dict, optional): Dictionary containing semantic theories.
                                           If None, will be loaded automatically.

    Returns:
        dict: Dictionary containing semantics, proposition, model, and operators

    Raises:
        ValueError: If the theory name is not found or the theory_lib module can't be loaded
        KeyError: If the specific theory is not found in the semantic_theories
    """
    if semantic_theories is None:
        try:
            # Import here (function-local, not module-level) so that merely importing
            # model_checker.api does not force theory_lib to load; this is the one call site
            # that needs the auto-load fallback.
            from .theory_lib import get_semantic_theories
            semantic_theories = get_semantic_theories(name)
        except ImportError as e:
            available_theories = []
            try:
                from .theory_lib import AVAILABLE_THEORIES
                available_theories = AVAILABLE_THEORIES
            except ImportError:
                pass

            raise ValueError(f"Could not load theory_lib module. Available theories: {available_theories}") from e
        except ValueError as e:
            raise ValueError(f"Theory '{name}' not found in theory_lib") from e

    return _lookup_theory(name, semantic_theories)
