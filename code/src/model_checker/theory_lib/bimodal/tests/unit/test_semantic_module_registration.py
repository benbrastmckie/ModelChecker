"""Regression tests for the bimodal semantic module's single class identity.

`bimodal/semantic/__init__.py` used to shadow a sibling `semantic.py` file
and load it a *second* time via `importlib.util.spec_from_file_location`
under the synthetic module name "bimodal_semantic_module", purely to work
around the `semantic/` package directory colliding with `semantic.py`.
`BimodalSemantics`, `BimodalProposition`, and `BimodalStructure` therefore
existed as two distinct class objects: one under the real package path
(reachable via any other module's plain `import`), and one under the
synthetic dynamic-loader identity. Cross-path `isinstance` checks silently
failed, and pickle could only resolve the synthetic identity because it was
manually registered in `sys.modules` -- without that registration,
`ProcessPoolExecutor` workers used by `--maximize` theory comparison
(`model_checker.builder.comparison`) failed with
`ModuleNotFoundError: No module named 'bimodal_semantic_module'`, silently
reported upstream as "Maximum N = 0" for every bimodal example.

The flat `semantic.py` has been moved into `semantic/core.py` verbatim and
`semantic/__init__.py` reduced to a plain re-export. There is now exactly
one class identity, reachable at the real module path
`model_checker.theory_lib.bimodal.semantic.core`, and pickling works
through the normal import mechanism with no dynamic loader or `sys.modules`
registration required.
"""

import pickle
import sys
import unittest
from concurrent.futures import ProcessPoolExecutor

from model_checker.theory_lib.bimodal.semantic import (
    BimodalSemantics,
    BimodalProposition,
    BimodalStructure,
)
from model_checker.theory_lib.bimodal.semantic import core as bimodal_semantic_core


def _echo_class_name(cls: type) -> str:
    """Module-level (picklable) helper run inside a worker process.

    Unpickling `cls` in the worker is the step that used to fail with
    ModuleNotFoundError when the synthetic module name was not registered
    in sys.modules -- the exact failure mode `--maximize` hit.
    """
    return cls.__name__


class TestBimodalSemanticSingleClassIdentity(unittest.TestCase):
    """Direct root-cause coverage: exactly one class identity, no dynamic loader."""

    def test_no_synthetic_module_identity_remains(self):
        """The old dynamic-loader synthetic module name must not exist anywhere."""
        self.assertNotIn(
            'bimodal_semantic_module', sys.modules,
            "bimodal/semantic/__init__.py must not register a synthetic "
            "'bimodal_semantic_module' entry in sys.modules; the dual "
            "module identity this guarded against has been eliminated by "
            "moving semantic.py into semantic/core.py."
        )

    def test_classes_report_the_real_package_module_path(self):
        """__module__ resolves to the real, importable package path."""
        self.assertEqual(
            BimodalSemantics.__module__,
            'model_checker.theory_lib.bimodal.semantic.core',
        )
        self.assertEqual(
            BimodalProposition.__module__,
            'model_checker.theory_lib.bimodal.semantic.core',
        )
        self.assertEqual(
            BimodalStructure.__module__,
            'model_checker.theory_lib.bimodal.semantic.core',
        )

    def test_single_class_identity_across_import_paths(self):
        """Importing via the package and via the submodule yield the identical object."""
        self.assertIs(bimodal_semantic_core.BimodalSemantics, BimodalSemantics)
        self.assertIs(bimodal_semantic_core.BimodalProposition, BimodalProposition)
        self.assertIs(bimodal_semantic_core.BimodalStructure, BimodalStructure)
        self.assertIsInstance(BimodalSemantics, type)
        # A trivial isinstance check across both paths must succeed -- this
        # is the exact failure mode the dual identity produced (an instance
        # constructed from one path's class object would silently fail
        # isinstance checks against the other path's class object).
        self.assertTrue(issubclass(BimodalSemantics, bimodal_semantic_core.BimodalSemantics))

    def test_bimodal_semantics_class_pickles_and_unpickles(self):
        """A bare in-process pickle round-trip of the class reference works."""
        blob = pickle.dumps(BimodalSemantics)
        restored = pickle.loads(blob)
        self.assertIs(restored, BimodalSemantics)

    def test_bimodal_semantics_class_survives_process_pool_round_trip(self):
        """Send the class reference to a worker process and back.

        This is the exact code path --maximize exercises through
        comparison.py's ProcessPoolExecutor usage. Before the semantic.py ->
        semantic/core.py move this depended on a manual sys.modules
        registration under a synthetic name; now it resolves through the
        real, importable module path with no special-casing required.
        """
        with ProcessPoolExecutor(max_workers=1) as executor:
            future = executor.submit(_echo_class_name, BimodalSemantics)
            result = future.result(timeout=30)
        self.assertEqual(result, 'BimodalSemantics')


if __name__ == '__main__':
    unittest.main()
