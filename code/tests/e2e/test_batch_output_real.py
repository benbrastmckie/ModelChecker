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
        """Test bimodal example produces correct JSON and markdown."""
        # Create test example
        example_content = '''
"""Test bimodal example for output."""

# Settings
N = 3
contingent = True
max_time = 1
expectation = "SAT"

# Premises
premise = (p \\wedge \\Box p)

# Conclusion  
conclusion = p

# Comments
# Simple test to verify output
'''
        
        example_path = os.path.join(self.test_dir, "test_output.py")
        with open(example_path, 'w') as f:
            f.write(example_content)
            
        output_dir = os.path.join(self.test_dir, "output")
        
        # Run the example with batch output
        import subprocess
        result = subprocess.run([
            'python', '-m', 'model_checker',
            example_path,
            '--theory', 'bimodal',
            '--save-output',
            '--output-dir', output_dir
        ], capture_output=True, text=True)
        
        # Check execution succeeded
        self.assertEqual(result.returncode, 0, f"Command failed: {result.stderr}")
        
        # Verify files created
        json_path = os.path.join(output_dir, "models.json")
        markdown_path = os.path.join(output_dir, "README.md")
        
        self.assertTrue(os.path.exists(json_path), "JSON file should be created")
        self.assertTrue(os.path.exists(markdown_path), "Markdown file should be created")
        
        # Load and verify JSON
        with open(json_path, 'r') as f:
            data = json.load(f)
            
        self.assertIn("examples", data)
        self.assertEqual(len(data["examples"]), 1)
        
        example = data["examples"][0]
        self.assertEqual(example["example"], "test_output")
        self.assertEqual(example["theory"], "bimodal")
        self.assertTrue(example["has_model"])
        
        # Check data was extracted
        self.assertIn("states", example)
        self.assertIn("worlds", example["states"])
        self.assertTrue(len(example["states"]["worlds"]) > 0)
        
        # Verify markdown
        with open(markdown_path, 'r') as f:
            markdown = f.read()
            
        self.assertIn("## Example: test_output", markdown)
        self.assertIn("Model Found: Yes", markdown)
        self.assertIn("### States", markdown)
        
        # Check batch mode showed directory instructions
        self.assertIn(f"cd {output_dir}", result.stdout)


if __name__ == '__main__':
    unittest.main()