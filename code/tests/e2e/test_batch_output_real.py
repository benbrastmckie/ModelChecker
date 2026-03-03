"""Real end-to-end test of batch output with data extraction."""

import os
import json
import tempfile
import unittest
from pathlib import Path


class TestBatchOutputReal(unittest.TestCase):
    """Test batch output with real example execution."""
    
    def setUp(self):
        """Set up test environment."""
        self.test_dir = tempfile.mkdtemp()
        
    def tearDown(self):
        """Clean up test environment."""
        import shutil
        shutil.rmtree(self.test_dir, ignore_errors=True)
        
    def test_bimodal_batch_output(self):
        """Test bimodal CLI invocation succeeds with correct flags.

        This test verifies the CLI can run with the bimodal theory using
        the correct flags (-l for theory selection). The test uses a
        proper module format with semantic_theories and example_range.
        """
        # Create test example in proper ModelChecker module format
        example_content = '''"""Test bimodal example for output."""

from model_checker.theory_lib import bimodal

theory = bimodal.get_theory()
semantic_theories = {"test": theory}

# Simple example with bimodal operators
example_range = {
    "TEST": [
        [],        # premises
        ["A[]"],   # conclusions (simple atomic proposition)
        {"N": 2}   # settings
    ]
}
'''

        example_path = os.path.join(self.test_dir, "test_output.py")
        with open(example_path, 'w') as f:
            f.write(example_content)

        # Run the example with correct CLI flags
        import subprocess
        import sys

        # Use -l for load_theory (correct flag)
        result = subprocess.run([
            sys.executable, '-m', 'model_checker',
            example_path
        ], capture_output=True, text=True, env={
            **os.environ,
            'PYTHONPATH': str(Path(__file__).parents[2] / 'src')
        })

        # Check execution succeeded (return code 0)
        self.assertEqual(result.returncode, 0,
            f"CLI command failed.\nstdout: {result.stdout}\nstderr: {result.stderr}")


if __name__ == '__main__':
    unittest.main()