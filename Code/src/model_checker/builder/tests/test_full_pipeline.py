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
        # Navigate to the Code directory
        current = Path(__file__)
        while current.name != 'Code' and current.parent != current:
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
            timeout=30  # Prevent hanging
        )
        
        if check and result.returncode != 0:
            self.fail(f"dev_cli.py failed: {result.stderr}")
            
        return result
    
    def test_theory_library_execution(self):
        """Test running theory library examples end-to-end.
        
        This catches issues like the discover_theory_module method signature
        mismatch that unit tests with mocks missed.
        """
        # Find theory lib examples
        theory_lib = self.dev_cli.parent / 'src' / 'model_checker' / 'theory_lib'
        
        test_cases = [
            theory_lib / 'logos' / 'examples.py',
            theory_lib / 'logos' / 'subtheories' / 'modal' / 'examples.py',
            theory_lib / 'exclusion' / 'examples.py',
        ]
        
        for example_path in test_cases:
            if not example_path.exists():
                self.skipTest(f"Example not found: {example_path}")
                
            with self.subTest(example=example_path.name):
                result = self.run_dev_cli([str(example_path)])
                
                # Should produce model output
                self.assertIn("EXAMPLE", result.stdout)
                self.assertIn("State Space", result.stdout)
                
                # Should not have Python errors
                self.assertNotIn("Traceback", result.stderr)
                self.assertNotIn("TypeError", result.stderr)
    
    def test_iteration_workflow(self):
        """Test iteration with discover_theory_module calls.
        
        This specifically tests the code path that had the method
        signature issue.
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
            # Run with iteration
            result = subprocess.run(
                [sys.executable, str(self.dev_cli), '-i', test_file],
                input="2\n\n",  # Request 2 iterations then continue
                capture_output=True,
                text=True,
                timeout=10
            )
            
            # Should complete successfully
            self.assertEqual(result.returncode, 0, 
                           f"Iteration failed: {result.stderr}")
            
            # Should show iteration output
            self.assertIn("ITERATION", result.stdout)
            
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