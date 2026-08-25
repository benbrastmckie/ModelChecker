"""Shared guarded-import helper for the optional, developer-local
``bimodal_harness`` package.

``bimodal_harness`` lives in a sibling checkout
(``/home/benjamin/Projects/BimodalHarness/src``) that is never installed in
CI and is not a dependency of this repository. Any test file in this tree
that needs symbols from it MUST import them from this module rather than
importing ``bimodal_harness`` directly at module scope -- a bare, unguarded,
module-level ``bimodal_harness`` import crashes pytest *collection* on any
machine (including every CI runner) where the sibling checkout does not
exist, before marker-based test deselection ever gets a chance to run. See
``test_bimodal_harness_guard.py`` for the regression tests enforcing this.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Any


def _try_import_bimodal_harness() -> tuple[bool, Any]:
    """Attempt to import BimodalHarness without raising.

    Returns:
        Tuple (available, module_or_none). If the import succeeds, available=True
        and the second element is the top-level bimodal_harness module.
        If unavailable, available=False and the second element is None.
    """
    bh_src = Path("/home/benjamin/Projects/BimodalHarness/src")
    if bh_src.exists() and str(bh_src) not in sys.path:
        sys.path.insert(0, str(bh_src))
    try:
        import bimodal_harness  # noqa: F401
        return True, bimodal_harness
    except ImportError:
        return False, None


# Try importing at module level to set a flag
BH_AVAILABLE, BH_MODULE = _try_import_bimodal_harness()

BH_SKIP_REASON = "BimodalHarness not available at /home/benjamin/Projects/BimodalHarness/src"
