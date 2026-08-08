"""Integration tests for builder package end-to-end behaviour.

This module exercises the builder package end to end: loading a module,
running its examples, comparison mode, and serialization.

Most of the wall-clock budgets this module used to assert have been removed.
Measurement showed they were not measuring the builder's cost at all: the
bimodal theory's default `max_time` is 1 second, so every model construction
here measured `min(real_solve_time, max_time) + overhead` and pinned at ~1.2s
regardless of the example. A 500ms budget was arithmetically unreachable, and
the multi-second budgets were satisfied by a quantity that physically could
not exceed the cap. The two timing assertions that remain
(`test_module_loading_performance`, `test_serialization_performance`) are
Z3-free and are documented individually.
"""

import unittest
import time
import tempfile
import os
from unittest.mock import Mock, patch

# Import test fixtures
from model_checker.builder.tests.fixtures.test_data import (
    TestTheories, TestExamples, TestModules, TestConstants
)
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory

# Import components to test
from model_checker.builder.module import BuildModule
from model_checker.builder.runner import ModelRunner


class TestBuilderPerformance(unittest.TestCase):
    """Test builder performance characteristics."""
    
    def setUp(self):
        """Set up performance testing environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.addCleanup(lambda: self._cleanup_temp_dir())
    
    def _cleanup_temp_dir(self):
        """Clean up temporary directory."""
        import shutil
        if os.path.exists(self.temp_dir):
            shutil.rmtree(self.temp_dir)
    
    def test_small_model_runs_end_to_end(self):
        """Test a small (N=2) example loads and runs to completion.

        This used to assert the run finished in <500ms. That budget was
        unreachable: the example's real solve time exceeds the theory's
        1-second `max_time`, so the run always spends the full timeout wall
        plus module-loading overhead (measured floor ~1.20s). What is worth
        pinning is that the load-and-run path completes without raising.
        """
        # Arrange
        test_file = self._create_test_file("""
from model_checker.theory_lib.bimodal import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {"SMALL": [["A"], ["B"], {"N": 2}]}
general_settings = {}
""")
        
        flags = Mock(
            file_path=test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            output=None,
            save=None,  # No saving
            sequential=False,  # Matches real --sequential/-q argparse default;
                                # a bare Mock() auto-creates a truthy attribute
                                # otherwise (see output/config.py sequential logic).
            _parsed_args=[]
        )
        
        # Act
        build_module = BuildModule(flags)
        build_module.runner.run_examples()

        # Assert
        self.assertEqual(list(build_module.example_range), ["SMALL"])
        self.assertIn("Test", build_module.semantic_theories)

    def test_medium_model_runs_end_to_end(self):
        """Test a medium (N=5) example loads and runs to completion.

        This used to assert the run finished in <2s. The measured cost is
        pinned at ~1.2s by the theory's 1-second `max_time` cap regardless of
        N, so the budget described the cap rather than the builder.
        """
        # Arrange
        test_file = self._create_test_file("""
from model_checker.theory_lib.bimodal import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {"MEDIUM": [["A", "B"], ["C"], {"N": 5}]}
general_settings = {}
""")
        
        flags = Mock(
            file_path=test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            output=None,
            save=None,  # No saving
            sequential=False,  # Matches real --sequential/-q argparse default;
                                # a bare Mock() auto-creates a truthy attribute
                                # otherwise (see output/config.py sequential logic).
            _parsed_args=[]
        )
        
        # Act
        build_module = BuildModule(flags)
        build_module.runner.run_examples()

        # Assert
        self.assertEqual(list(build_module.example_range), ["MEDIUM"])
        self.assertIn("Test", build_module.semantic_theories)

    # A "large model" test used to live here. It was a copy-paste duplicate of
    # the medium test -- identical premises, conclusions and N=5 settings, with
    # only the example key and the (now removed) budget differing.

    def test_multiple_examples_run_end_to_end(self):
        """Test a module holding five examples loads and runs all of them.

        This used to assert an average of <500ms per example and <2s total.
        Both were unreachable: each of the five examples spends the theory's
        full 1-second `max_time` plus overhead, for a measured ~6.1s total.
        """
        # Arrange
        test_file = self._create_test_file("""
from model_checker.theory_lib.bimodal import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {
    "EX1": [["A"], ["B"], {"N": 2}],
    "EX2": [["C"], ["D"], {"N": 2}],
    "EX3": [["E"], ["F"], {"N": 2}],
    "EX4": [["G"], ["H"], {"N": 2}],
    "EX5": [["I"], ["J"], {"N": 2}]
}
general_settings = {}
""")
        
        flags = Mock(
            file_path=test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            output=None,
            save=None,  # No saving
            sequential=False,  # Matches real --sequential/-q argparse default;
                                # a bare Mock() auto-creates a truthy attribute
                                # otherwise (see output/config.py sequential logic).
            _parsed_args=[]
        )
        
        # Act
        build_module = BuildModule(flags)
        build_module.runner.run_examples()

        # Assert - all five examples were loaded and processed without raising
        self.assertEqual(
            list(build_module.example_range),
            ["EX1", "EX2", "EX3", "EX4", "EX5"],
        )

    def test_comparison_mode_runs_end_to_end(self):
        """Test comparison mode runs to completion over two theory entries.

        This used to assert a <2s budget, which was vacuous: the measured cost
        is ~0.13s. Note also that the two entries are not actually different
        theories -- `bimodal.get_theory(['extensional'])` and
        `get_theory(['counterfactual'])` return the identical object (the
        subtheory argument is ignored), so this compares bimodal against
        itself. That is a defect in `get_theory`, not in this test, and is not
        addressed here; the test is kept as a smoke test of the comparison
        code path.
        """
        # Arrange
        test_file = self._create_test_file("""
from model_checker.theory_lib.bimodal import get_theory

theory1 = get_theory(['extensional'])
theory2 = get_theory(['counterfactual'])
semantic_theories = {"Ext": theory1, "CF": theory2}
example_range = {"TEST": [["A"], ["B"], {"N": 3}]}
general_settings = {}
""")
        
        flags = Mock(
            file_path=test_file,
            comparison=True,
            interactive=False,
            iterations=False,
            quiet=True,
            output=None,
            save=None,  # No saving
            sequential=False,  # Matches real --sequential/-q argparse default;
                                # a bare Mock() auto-creates a truthy attribute
                                # otherwise (see output/config.py sequential logic).
            _parsed_args=[]
        )
        
        # Act
        build_module = BuildModule(flags)
        build_module.comparison.run_comparison()

        # Assert
        self.assertEqual(
            sorted(build_module.semantic_theories), ["CF", "Ext"]
        )

    def test_module_loading_performance(self):
        """Test module loading completes quickly.

        This verifies that loading and parsing module files
        doesn't have excessive overhead.
        """
        # The 100ms budget below is a hang guard, not a performance budget:
        # this path is Z3-free and measures at <5ms, so the assertion means
        # "module loading did not hang", with 20x headroom.
        # Arrange
        test_file = self._create_test_file(TestModules.WITH_EXAMPLES)
        
        flags = Mock(
            file_path=test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            output=None,
            save=None,  # No saving
            sequential=False,  # Matches real --sequential/-q argparse default;
                                # a bare Mock() auto-creates a truthy attribute
                                # otherwise (see output/config.py sequential logic).
            _parsed_args=[]
        )
        
        # Act - Time just the loading phase
        start_time = time.time()
        build_module = BuildModule(flags)
        # Access loader to ensure it's initialized
        _ = build_module.loader
        loading_time = time.time() - start_time
        
        # Assert
        self.assertLess(loading_time, 0.1,
                       f"Module loading should complete in <100ms, took {loading_time:.3f}s")
    
    def test_serialization_performance(self):
        """Test serialization of results completes quickly.
        
        This ensures that converting model structures to output format
        doesn't become a bottleneck.
        """
        # Arrange
        from model_checker.builder.serialize import serialize_semantic_theory, deserialize_operators
        
        # Create a complex theory structure
        complex_theory = TestTheories.COMPLEX.copy()
        
        # Act - Time serialization
        start_time = time.time()
        for _ in range(100):  # Serialize 100 times to get measurable time
            serialized = serialize_semantic_theory("test", complex_theory)
        serialization_time = (time.time() - start_time) / 100
        
        # Assert
        self.assertLess(serialization_time, 0.001,
                       f"Single serialization should take <1ms, took {serialization_time*1000:.3f}ms")
    
    # A `test_constraint_generation_scales_linearly` test used to live here. It
    # timed four formula sizes and asserted the elapsed-time ratio grew no more
    # than quadratically. All four cases hit the theory's 1-second `max_time`
    # cap, so every ratio was ~1.0 against thresholds of 4, 9 and 16 -- stable
    # precisely because it measured nothing, and unable to detect a genuine
    # blowup because the cap truncates the signal before the assertion sees it.
    # Counting generated constraints instead of seconds would be a different
    # test; it was not written here.

    def _create_test_file(self, content):
        """Create a temporary test file with given content.
        
        Args:
            content: Python code content for the test file
            
        Returns:
            Path to the created test file
        """
        test_file = os.path.join(self.temp_dir, "test_module.py")
        with open(test_file, 'w') as f:
            f.write(content)
        return test_file


# A `TestMemoryUsage` class used to live here with two tests whose entire
# bodies were `self.assertTrue(True, "placeholder")`. They asserted nothing and
# were deleted rather than left claiming coverage they did not provide.


if __name__ == '__main__':
    unittest.main()