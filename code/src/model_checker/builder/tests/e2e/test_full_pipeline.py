"""
Full pipeline integration tests that catch runtime errors.

These tests run without mocks to ensure the complete system works together.
They're slower than unit tests but catch integration issues that mocks miss.
"""
import os
import sys
import subprocess
import tempfile
import unittest
from pathlib import Path


class TestFullPipeline(unittest.TestCase):
    """Test complete execution paths without mocking."""
    
    def setUp(self):
        """Find the dev_cli.py script."""
        # Navigate to the project root (directory containing pyproject.toml)
        current = Path(__file__)
        while not (current / 'pyproject.toml').exists() and current.parent != current:
            current = current.parent
        
        self.dev_cli = current / 'dev_cli.py'
        if not self.dev_cli.exists():
            self.skipTest(f"dev_cli.py not found at {self.dev_cli}")
    
    def run_dev_cli(self, args, check=True):
        """Run dev_cli.py with given arguments.
        
        Args:
            args: List of command line arguments
            check: Whether to check return code
            
        Returns:
            subprocess.CompletedProcess
        """
        cmd = [sys.executable, str(self.dev_cli)] + args
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            # Outer guard must stay comfortably ahead of the largest inner
            # max_time among run_dev_cli callers, plus interpreter
            # startup/import overhead, or a raised max_time silently becomes
            # a new subprocess-timeout failure instead of a real result.
            timeout=30
        )
        
        if check and result.returncode != 0:
            self.fail(f"dev_cli.py failed: {result.stderr}")
            
        return result
    
    def test_theory_library_execution(self):
        """Test running theory library examples end-to-end.

        This catches issues like the discover_theory_module method signature
        mismatch that unit tests with mocks missed.

        Deliberately, audited retention on bimodal: this is the one test in this file (and the
        one exception in this task's whole audit) whose assertion genuinely needs bimodal --
        the "World Histories" string below is bimodal's own model-rendering label, not
        reproducible under any other theory. A future sweep must not "finish the job" by
        swapping this fixture to logos too; see TESTING_GUIDE.md section 8.14 and this task's
        audit report for the full reasoning. Its existing `max_time=10` is unchanged.
        """
        # Create a simple test module instead of running full examples
        # to avoid timeouts while still testing the discover_theory_module path
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            f.write('''
from model_checker.theory_lib.bimodal import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {
    "TEST": [[], ["A"], {"N": 2, "max_time": 10}]
}
general_settings = {}
''')
            test_file = f.name

        try:
            result = self.run_dev_cli([test_file])
            
            # Should produce model output. Bimodal renders its model as a
            # "World Histories" table rather than the generic "State Space"
            # section used by state-based theories.
            self.assertIn("EXAMPLE", result.stdout)
            self.assertIn("World Histories", result.stdout)
            
            # Should not have Python errors
            self.assertNotIn("Traceback", result.stderr)
            self.assertNotIn("TypeError", result.stderr)
            
        finally:
            os.unlink(test_file)
    
    def test_print_impossible_flag_includes_impossible_states(self):
        """Test -i/--print_impossible with discover_theory_module calls.

        Renamed from the misnamed `test_iteration_workflow`: that test believed `-i` requested
        N model iterations and fed `input="2\\n\\n"` to satisfy a prompt it assumed existed.
        `-i` is actually `--print_impossible`, a `store_true` boolean flag
        (`__main__.py`'s debug_group) with no prompt and nothing that consumes stdin -- the
        `input=` kwarg was silently discarded. There is no CLI iteration mechanism in the
        registered flag table (`ParseFileFlags._create_parser()`), so this test now honestly
        covers `--print_impossible`'s actual, documented effect: including impossible states in
        the model display, exercising the same `discover_theory_module` code path the original
        test intended to stress.

        Uses logos rather than bimodal: only generic flag-plumbing is asserted (that `-i`
        changes output relative to the no-flag baseline), nothing bimodal-specific. Same
        remedy, same rationale as this file's other logos swaps in this task.
        """
        # Create a simple test module
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            f.write('''
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {
    "TEST": [[], ["A"], {"N": 2}]
}
general_settings = {}
''')
            test_file = f.name

        try:
            baseline = subprocess.run(
                [sys.executable, str(self.dev_cli), test_file],
                capture_output=True,
                text=True,
                timeout=10
            )
            self.assertEqual(baseline.returncode, 0, f"Baseline run failed: {baseline.stderr}")

            result = subprocess.run(
                [sys.executable, str(self.dev_cli), '-i', test_file],
                capture_output=True,
                text=True,
                timeout=10
            )

            self.assertEqual(result.returncode, 0, f"-i run failed: {result.stderr}")
            self.assertIn("EXAMPLE", result.stdout)
            self.assertNotIn("Traceback", result.stderr)
            # -i must actually change output relative to the no-flag baseline, or this test
            # would pass vacuously for a no-op flag.
            self.assertNotEqual(
                result.stdout, baseline.stdout,
                "-i/--print_impossible produced identical output to the no-flag baseline"
            )

        finally:
            os.unlink(test_file)
    
    def test_error_handling(self):
        """Test that errors are handled gracefully."""
        # Non-existent file
        result = self.run_dev_cli(['/tmp/does_not_exist.py'], check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("error", result.stderr.lower())
        
        # File with syntax error
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            f.write("this is not valid python syntax !")
            bad_file = f.name
            
        try:
            result = self.run_dev_cli([bad_file], check=False)
            self.assertNotEqual(result.returncode, 0)
            # Should have error message, not uncaught exception
            self.assertTrue(
                "SyntaxError" in result.stderr or 
                "Failed to import" in result.stderr
            )
        finally:
            os.unlink(bad_file)


if __name__ == '__main__':
    unittest.main()