"""Simplified unit tests for BuildExample functionality.

This module provides focused unit tests for the BuildExample class using
minimal mocking and real components where appropriate.
"""

import unittest
import sys
import tempfile
import os
from io import StringIO
from unittest.mock import Mock, patch

import pytest

from model_checker.builder.example import BuildExample
from model_checker.builder.module import BuildModule
from model_checker.builder.error_types import ValidationError


class TestBuildExampleBasic(unittest.TestCase):
    """Test BuildExample basic functionality with real components."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.test_file = self._create_test_module()
        
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        if os.path.exists(self.temp_dir):
            shutil.rmtree(self.temp_dir)
    
    def _create_test_module(self):
        """Create a simple test module file.

        Uses logos rather than bimodal: these tests assert only generic
        BuildExample/BuildModule wiring (attribute presence, result-dict
        shape, comparison-mode plumbing) -- nothing bimodal-specific -- and
        N=2 is cheap under either theory. See TESTING_GUIDE.md section 8.14
        and this task's audit report for the cost-decoupling rationale.
        """
        content = """
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {"SIMPLE": [["A"], ["B"], {"N": 2}]}
general_settings = {}
"""
        test_file = os.path.join(self.temp_dir, "test_module.py")
        with open(test_file, 'w') as f:
            f.write(content)
        return test_file
    
    def test_build_example_initialization(self):
        """Test that BuildExample can be initialized with valid inputs."""
        # Create a real BuildModule
        flags = Mock(
            file_path=self.test_file,
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
        
        build_module = BuildModule(flags)
        
        # Get the theory and example
        theory = build_module.semantic_theories["Test"]
        example = list(build_module.example_range.values())[0]
        
        # Create BuildExample
        build_example = BuildExample(build_module, theory, example, "Test")
        
        # Verify it was created
        self.assertIsNotNone(build_example)
        self.assertEqual(build_example.build_module, build_module)
        self.assertEqual(build_example.premises, ["A"])
        self.assertEqual(build_example.conclusions, ["B"])
    
    def test_build_example_get_result(self):
        """Test that BuildExample can get results after model checking."""
        # Create a real BuildModule
        flags = Mock(
            file_path=self.test_file,
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
        
        build_module = BuildModule(flags)
        
        # Get the theory and example
        theory = build_module.semantic_theories["Test"]
        example = list(build_module.example_range.values())[0]
        
        # Create BuildExample
        build_example = BuildExample(build_module, theory, example, "Test")
        
        # Get result
        result = build_example.get_result()
        
        # Verify result structure
        self.assertIsInstance(result, dict)
        self.assertIn("model_found", result)
        self.assertIn("runtime", result)
        self.assertIn("model_structure", result)
        self.assertIsInstance(result["model_found"], bool)
        self.assertIsInstance(result["runtime"], (int, float))
    
    def test_build_example_print_model(self):
        """Test that BuildExample can print model output."""
        # Create a real BuildModule
        flags = Mock(
            file_path=self.test_file,
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
        
        build_module = BuildModule(flags)
        
        # Get the theory and example
        theory = build_module.semantic_theories["Test"]
        example = list(build_module.example_range.values())[0]
        
        # Create BuildExample
        build_example = BuildExample(build_module, theory, example, "Test")
        
        # Capture output
        output = StringIO()
        
        # Print model
        build_example.print_model(
            example_name="TEST",
            theory_name="Test",
            output=output
        )
        
        # Verify something was printed
        output_text = output.getvalue()
        self.assertTrue(len(output_text) > 0,
                       "Should print some output")
    
    def test_build_example_with_no_model(self):
        """Test BuildExample when no model is found."""
        # Create a module with unsatisfiable example. Uses logos rather than
        # bimodal (see _create_test_module's docstring): this test asserts
        # only that no model is found for a contradiction, not any
        # bimodal-specific semantics.
        content = """
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
# Contradiction: A and not A
example_range = {"UNSAT": [["A", "\\\\neg A"], ["B"], {"N": 2}]}
general_settings = {}
"""
        test_file = os.path.join(self.temp_dir, "unsat_module.py")
        with open(test_file, 'w') as f:
            f.write(content)
        
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
        
        build_module = BuildModule(flags)
        
        # Get the theory and example
        theory = build_module.semantic_theories["Test"]
        example = list(build_module.example_range.values())[0]
        
        # Create BuildExample
        build_example = BuildExample(build_module, theory, example, "Test")
        
        # Get result
        result = build_example.get_result()
        
        # Should find no model due to contradiction
        self.assertFalse(result["model_found"],
                        "Should not find model for contradictory premises")
    
    def test_build_example_comparison_mode(self):
        """Test BuildExample in comparison mode."""
        # Create a module with multiple theories. Uses logos rather than
        # bimodal (see _create_test_module's docstring): this test asserts
        # only comparison-mode wiring (theory count, settings_manager
        # presence), not any bimodal-specific semantics.
        content = """
from model_checker.theory_lib.logos import get_theory

theory1 = get_theory(['extensional'])
theory2 = get_theory(['modal'])
semantic_theories = {"Ext": theory1, "Modal": theory2}
example_range = {"TEST": [["A"], ["B"], {"N": 2}]}
general_settings = {}
"""
        test_file = os.path.join(self.temp_dir, "comparison_module.py")
        with open(test_file, 'w') as f:
            f.write(content)
        
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
        
        build_module = BuildModule(flags)
        
        # Build module should have multiple theories
        self.assertEqual(len(build_module.semantic_theories), 2)
        
        # Get first theory and example
        theory = build_module.semantic_theories["Ext"]
        example = list(build_module.example_range.values())[0]
        
        # Create BuildExample in comparison mode
        build_example = BuildExample(build_module, theory, example, "Ext")
        
        # Verify it was created
        self.assertIsNotNone(build_example)
        
        # Settings manager should know it's in comparison mode
        self.assertTrue(hasattr(build_example, 'settings_manager'))


class TestTimeoutSurfacing(unittest.TestCase):
    """Test that a Z3 UNKNOWN is never reported as model_found=False without
    an accompanying, readable timeout signal.

    models/structure.py's solve()/re_solve() already classify every Z3
    UNKNOWN as is_timeout=True and populate ModelStructure.timeout -- the
    break was entirely in builder/example.py, which never read it. These
    tests pin the fix: get_result() and _get_model_structure_data() must
    both surface a "timeout" key alongside "model_found".
    """

    def _build_example_with_mock_structure(self, timeout, z3_model_status):
        """Construct a BuildExample with a minimal mock model_structure,
        mirroring test_get_result_without_model_check's __new__ pattern to
        avoid a real solve."""
        example = BuildExample.__new__(BuildExample)
        mock_structure = Mock()
        mock_structure.timeout = timeout
        mock_structure.z3_model_status = z3_model_status
        mock_structure.z3_model_runtime = 1.23
        mock_structure.z3_model = None
        example.model_structure = mock_structure
        example.settings = {}
        return example

    def test_get_result_contains_timeout_key(self):
        """get_result() always carries a 'timeout' key."""
        example = self._build_example_with_mock_structure(
            timeout=False, z3_model_status=True
        )
        result = example.get_result()
        self.assertIn("timeout", result)

    def test_get_result_timeout_true_on_unknown(self):
        """A timed-out solve yields model_found=False and timeout=True,
        independently readable rather than conflated."""
        example = self._build_example_with_mock_structure(
            timeout=True, z3_model_status=False
        )
        result = example.get_result()
        self.assertFalse(result["model_found"])
        self.assertTrue(result["timeout"])

    def test_get_model_structure_data_contains_timeout_key(self):
        """_get_model_structure_data() always carries a 'timeout' key."""
        example = self._build_example_with_mock_structure(
            timeout=False, z3_model_status=True
        )
        data = example._get_model_structure_data()
        self.assertIn("timeout", data)

    def test_get_model_structure_data_timeout_true_on_unknown(self):
        """A timed-out solve's structure data reports model_found=False and
        timeout=True, independently readable rather than conflated."""
        example = self._build_example_with_mock_structure(
            timeout=True, z3_model_status=False
        )
        data = example._get_model_structure_data()
        self.assertFalse(data["model_found"])
        self.assertTrue(data["timeout"])


class TestThreeWayCheckResult(unittest.TestCase):
    """Test that BuildExample.check_result() returns one of three explicit
    string values -- "match", "mismatch", "inconclusive" -- instead of a
    boolean that structurally cannot express "the solver timed out".

    check_result()'s signature was already annotated `-> str` while its body
    returned a bool; this fixes that long-standing annotation/behavior
    mismatch. "inconclusive" is checked before the expectation comparison,
    mirroring oracle/bimodal_logic/tests/test_cross_oracle_differential.py's
    timeout-checked-first ordering, so a timed-out solve is never reported
    as a semantic mismatch.
    """

    def _build_example_with_mock_structure(self, timeout, z3_model_status, settings=None):
        example = BuildExample.__new__(BuildExample)
        mock_structure = Mock()
        mock_structure.timeout = timeout
        mock_structure.z3_model_status = z3_model_status
        example.model_structure = mock_structure
        example.settings = settings if settings is not None else {}
        return example

    def test_check_result_match(self):
        """model_findings equal to the expectation returns 'match'."""
        example = self._build_example_with_mock_structure(
            timeout=False, z3_model_status=True, settings={"model": True}
        )
        self.assertEqual(example.check_result(), "match")

    def test_check_result_mismatch(self):
        """model_findings unequal to the expectation returns 'mismatch'."""
        example = self._build_example_with_mock_structure(
            timeout=False, z3_model_status=False, settings={"model": True}
        )
        self.assertEqual(example.check_result(), "mismatch")

    def test_check_result_inconclusive_on_timeout(self):
        """A timed-out solve returns 'inconclusive', checked before the
        expectation comparison -- even when z3_model_status happens to
        equal the expectation (which would otherwise read as a 'match')."""
        example = self._build_example_with_mock_structure(
            timeout=True, z3_model_status=True, settings={"model": True}
        )
        self.assertEqual(example.check_result(), "inconclusive")


class TestBuildExampleErrorHandling(unittest.TestCase):
    """Test BuildExample error handling."""

    def test_get_result_without_model_check(self):
        """Test get_result raises error when called before model checking."""
        # Create a BuildExample without proper initialization
        example = BuildExample.__new__(BuildExample)
        
        # Should raise RuntimeError
        with self.assertRaises(RuntimeError) as context:
            example.get_result()
        
        self.assertIn("no model check", str(context.exception).lower(),
                     "Should indicate model check not performed")
    
    def test_invalid_theory_structure(self):
        """Test BuildExample handles invalid theory structure."""
        from model_checker.builder.validation import validate_semantic_theory
        
        # Test with invalid theory structure
        invalid_theory = {"invalid": "structure"}
        
        with self.assertRaises(ValidationError) as context:
            validate_semantic_theory(invalid_theory)
        
        # Check for either "invalid" or "missing" in error message
        error_msg = str(context.exception).lower()
        self.assertTrue("missing" in error_msg or "invalid" in error_msg,
                       f"Should indicate invalid or missing component: {error_msg}")
    
    def test_invalid_example_structure(self):
        """Test BuildExample handles invalid example structure."""
        from model_checker.builder.validation import validate_example_case
        
        # Test with invalid example structure
        invalid_example = ["not", "enough"]  # Missing settings
        
        with self.assertRaises((ValueError, ValidationError)) as context:
            validate_example_case(invalid_example)
        
        # Check that error mentions the issue
        error_msg = str(context.exception).lower()
        self.assertTrue("must be" in error_msg or "exactly 3" in error_msg,
                       f"Should indicate structure issue: {error_msg}")


class TestBuildExampleIntegration(unittest.TestCase):
    """Test BuildExample integration with real theories."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        if os.path.exists(self.temp_dir):
            shutil.rmtree(self.temp_dir)
    
    @pytest.mark.development
    def test_build_example_bimodal_theory_countermodel(self):
        """Test BuildExample with the bimodal theory, asserting a countermodel is found.

        `get_theory(config=None)` in the bimodal theory accepts but entirely ignores its
        `config` argument, so it always returns the full bimodal theory regardless of the
        value supplied -- no operator-restricted fragment is being loaded here.

        Marked `development` per TESTING_GUIDE.md section 8.14 and this task's audit report
        (`specs/181_.../reports/01_gating-tests-coupled-to-bimodal.md`): the subject is
        BuildExample/countermodel-finding, which is not bimodal-specific plumbing, but the claim
        is one of completeness ("bimodal finds a countermodel within budget") rather than
        soundness, of exactly the kind the `development` marker exists to quarantine while
        bimodal's frame-axiom cost is unsettled. Applied per-test (not a new blanket), stays
        runnable via `-m development`. Its existing timeout-vs-unsat discriminator below and its
        `max_time: 30` are both preserved unchanged.
        """
        content = """
from model_checker.theory_lib.bimodal import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Bimodal": theory}
# Simple premise/conclusion pair over the full bimodal operator set
# max_time is explicit: the bimodal default is 1s, but the real solve takes ~1.7-2s in
# isolation and was observed to take just over 10s under full-builder-suite load (Z3
# state/CPU contention from preceding tests in the same process), so max_time: 10 still
# flaked. 30s matches the headroom sibling bimodal examples use for CI variance
# (theory_lib/bimodal/examples.py) and comfortably covers the observed worst case.
example_range = {"SIMPLE": [["A"], ["B"], {"N": 2, "max_time": 30}]}
general_settings = {}
"""
        test_file = os.path.join(self.temp_dir, "bimodal_test.py")
        with open(test_file, 'w') as f:
            f.write(content)
        
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
        
        build_module = BuildModule(flags)

        # Run the example
        theory = build_module.semantic_theories["Bimodal"]
        example = list(build_module.example_range.values())[0]

        build_example = BuildExample(build_module, theory, example, "Bimodal")
        result = build_example.get_result()

        # A TIMEOUT IS NOT AN UNSAT. get_result()'s own docstring states that "model_found" is
        # False both when Z3 proved unsatisfiability and when it returned UNKNOWN, and that
        # "timeout" is the flag that disambiguates the two. Asserting on "model_found" alone
        # therefore cannot tell "the solver ran out of budget under CI contention" from "no
        # countermodel exists", and an exhausted budget inverts into a false negative claiming
        # bimodal validates A |= B. This is the third site carrying that flaw; the other two
        # are guarded by _skip_if_solver_timed_out() in
        # theory_lib/bimodal/tests/integration/test_iterate.py, whose docstring records why no
        # max_time value closes the hole (this example's budget was already widened once, to
        # 30s, and the failure recurred anyway -- CI run 33500582816, the Python 3.10 leg,
        # where 3.11 and 3.12 passed on the identical selection).
        #
        # Deliberately a skip, not an xfail: the outcome is budget-dependent, so xfail would
        # report a spurious XPASS on every run where the solve does finish in time.
        #
        # The assertion below is NOT weakened. A genuine unsat still has timeout=False and
        # still fails; only the inconclusive case is routed to a skip, where it belongs.
        if result["timeout"]:
            budget = result["model_structure"]["settings"].get("max_time")
            self.skipTest(
                "Z3 returned UNKNOWN (budget exhausted under load), not a decided result; "
                "an inconclusive solve is not evidence about satisfiability in either "
                f"direction. max_time={budget}s, runtime={result['runtime']}s"
            )

        # Simple example: A as premise, B as conclusion over the full bimodal theory -
        # should find a countermodel (A does not entail B under bimodal semantics)
        self.assertTrue(result["model_found"],
                       "Should find countermodel where A is true but B is false "
                       f"(solver decided, not timed out; runtime={result['runtime']}s)")
    
    def test_iteration_via_iterate_api(self):
        """Test that further models are found through the iterate API.

        Renamed from test_find_next_model_basic: it called
        BuildExample.find_next_model(), a method BuildExample does not have
        and, per iterate/__init__.py, never should -- next-model search is
        the iterate package's responsibility, entered through each theory's
        own iterate_example.

        Uses logos rather than bimodal: this test's own docstring already
        states it asserts the generic BuildExample/iterate-API contract, not
        bimodal semantics ("asserts the contract, not the model count"), and
        it was the file's clearest near-miss under bimodal (measured 31.78s
        against its own explicit max_time=30 -- see this task's audit
        report). logos's iterate path is exercised elsewhere in the theory's
        own test tree, so this is not a coverage loss for the generic
        contract this test targets. The explicit `max_time: 30` override
        that existed solely to buy headroom against bimodal's cost is
        removed (not raised) -- N=2 under logos measures well under a
        second, so the theory's own default max_time is ample.
        """
        content = """
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
# Simple satisfiable example - just A as premise, no conclusions
example_range = {"SAT": [["A"], [], {"N": 2}]}
general_settings = {}
"""
        test_file = os.path.join(self.temp_dir, "next_model_test.py")
        with open(test_file, 'w') as f:
            f.write(content)
        
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
        
        build_module = BuildModule(flags)
        
        theory = build_module.semantic_theories["Test"]
        example = list(build_module.example_range.values())[0]
        
        build_example = BuildExample(build_module, theory, example, "Test")

        # Should find initial model -- branch on timeout first, since an
        # inconclusive Z3 UNKNOWN (solver ran out of budget) is not the
        # same as "no model exists" and must never be reported as a test
        # failure. Motivating case: this solve was observed taking 30.62s
        # against this example's own explicit max_time=30 under load, which
        # a plain `assertTrue(result["model_found"])` could not distinguish
        # from a genuine absence of a model.
        result = build_example.get_result()
        if result["timeout"]:
            self.skipTest(
                "Solver timed out (inconclusive) rather than deciding "
                "satisfiability -- not a test failure. See the 30.62s-vs-"
                "max_time=30 observation this branch guards against."
            )
        self.assertTrue(result["model_found"],
                       "Should find initial model for A")

        # Finding further models is the iterate package's job, not
        # BuildExample's: BuildExample exposes no find_next_model method,
        # and each theory supplies its own iterate_example entry point (see
        # iterate/__init__.py's module docstring). Drive that API rather
        # than an attribute BuildExample has never had.
        self.assertFalse(hasattr(build_example, 'find_next_model'),
                         "next-model search belongs to the iterate API, "
                         "not to BuildExample")

        from model_checker.theory_lib.logos.iterate import iterate_example

        model_structures = iterate_example(build_example, max_iterations=2)

        # The initial model is always included, so a satisfiable example
        # yields at least one structure. Whether a second, semantically
        # distinct model exists is a solver outcome this test does not
        # constrain -- it asserts the contract, not the model count.
        self.assertIsInstance(model_structures, list)
        self.assertGreaterEqual(len(model_structures), 1,
                                "iteration should return at least the "
                                "initial model")
        self.assertLessEqual(len(model_structures), 2,
                             "iteration should respect max_iterations")


if __name__ == '__main__':
    unittest.main()