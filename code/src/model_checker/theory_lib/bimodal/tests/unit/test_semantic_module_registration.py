"""Regression tests for the bimodal semantic dynamic-loader sys.modules registration.

`bimodal/semantic/__init__.py` loads the sibling `semantic.py` module via
`importlib.util` under the synthetic module name "bimodal_semantic_module"
(to work around the `semantic/` package directory shadowing `semantic.py`).
Classes defined there -- `BimodalSemantics`, `BimodalProposition`,
`BimodalStructure` -- therefore report `__module__ == "bimodal_semantic_module"`.

Unless that synthetic name is registered in `sys.modules`, pickle cannot
resolve a class reference back to it by module + qualname. This is exactly
what `ProcessPoolExecutor` needs when `--maximize` theory comparison
(`model_checker.builder.comparison`) sends a semantic theory configuration
containing a `BimodalSemantics` reference to worker processes: the worker
fails with `ModuleNotFoundError: No module named 'bimodal_semantic_module'`,
which was silently swallowed and reported upstream as "Maximum N = 0" for
every bimodal example.
"""

import pickle
import sys
import unittest
from concurrent.futures import ProcessPoolExecutor

from model_checker.theory_lib.bimodal.semantic import BimodalSemantics


def _echo_class_name(cls: type) -> str:
    """Module-level (picklable) helper run inside a worker process.

    Unpickling `cls` in the worker is the step that fails with
    ModuleNotFoundError when "bimodal_semantic_module" is not registered
    in sys.modules -- the exact failure mode `--maximize` hit.
    """
    return cls.__name__


class TestBimodalSemanticModuleRegistration(unittest.TestCase):
    """Direct root-cause coverage for the sys.modules registration fix."""

    def test_dynamic_loader_registers_synthetic_module_name(self):
        """"bimodal_semantic_module" must be resolvable via sys.modules."""
        self.assertIn(
            'bimodal_semantic_module', sys.modules,
            "bimodal/semantic/__init__.py must register the dynamically "
            "loaded module in sys.modules (before exec_module()) so pickle "
            "can resolve BimodalSemantics by module name + qualname."
        )
        self.assertIs(
            sys.modules['bimodal_semantic_module'].BimodalSemantics,
            BimodalSemantics,
        )

    def test_bimodal_semantics_class_pickles_and_unpickles(self):
        """A bare in-process pickle round-trip of the class reference works."""
        blob = pickle.dumps(BimodalSemantics)
        restored = pickle.loads(blob)
        self.assertIs(restored, BimodalSemantics)

    def test_bimodal_semantics_class_survives_process_pool_round_trip(self):
        """Send the class reference to a worker process and back.

        This is the exact code path --maximize exercises through
        comparison.py's ProcessPoolExecutor usage. Before the sys.modules
        registration fix this raised
        `ModuleNotFoundError: No module named 'bimodal_semantic_module'`
        in the worker, silently reported upstream as "Maximum N = 0".
        """
        with ProcessPoolExecutor(max_workers=1) as executor:
            future = executor.submit(_echo_class_name, BimodalSemantics)
            result = future.result(timeout=30)
        self.assertEqual(result, 'BimodalSemantics')


if __name__ == '__main__':
    unittest.main()
