"""Integration test for batch output enhancement.

This test verifies that the complete output system works correctly,
including data extraction from model structures, JSON/markdown generation,
and proper formatting of all relation types.
"""

import os
import json
import tempfile
import unittest
from pathlib import Path

from model_checker.builder.module import BuildModule
from model_checker.builder.project import BuildProject
from model_checker.output.manager import OutputManager
from model_checker.output.collectors import ModelDataCollector
from model_checker.output.formatters import MarkdownFormatter


class TestBatchOutputIntegration(unittest.TestCase):
    """Test complete batch output system integration."""
    
    def setUp(self):
        """Set up test environment."""
        self.test_dir = tempfile.mkdtemp()
        self.example_content = '''
"""Test example for batch output integration."""

# Settings
N = 3
contingent = True
expectation = "SAT"

# Premises
premise = p

# Conclusion  
conclusion = p

# Comments
# Simple tautology to test output
'''
        
    def tearDown(self):
        """Clean up test environment."""
        import shutil
        shutil.rmtree(self.test_dir, ignore_errors=True)
        
    def test_bimodal_output_integration(self):
        """Test bimodal theory output with time shift relations."""
        # Create test example file
        example_path = os.path.join(self.test_dir, "test_bimodal.py")
        with open(example_path, 'w') as f:
            f.write(self.example_content)
            
        # Create output directory
        output_dir = os.path.join(self.test_dir, "output")
        
        # Create project and module
        project = BuildProject.from_example(example_path, theory_name="bimodal")
        module = BuildModule(project)
        
        # Configure for batch output
        module.output_manager = OutputManager(
            save_output=True,
            output_dir=output_dir
        )
        
        # Run the example
        module.run_examples()
        
        # Verify output files created
        json_path = os.path.join(output_dir, "models.json")
        markdown_path = os.path.join(output_dir, "README.md")
        
        self.assertTrue(os.path.exists(json_path), "JSON file should be created")
        self.assertTrue(os.path.exists(markdown_path), "Markdown file should be created")
        
        # Load and verify JSON content
        with open(json_path, 'r') as f:
            json_data = json.load(f)
            
        self.assertIn("examples", json_data)
        self.assertEqual(len(json_data["examples"]), 1)
        
        example_data = json_data["examples"][0]
        self.assertEqual(example_data["example"], "test_bimodal")
        self.assertEqual(example_data["theory"], "bimodal")
        self.assertTrue(example_data["has_model"])
        
        # Verify model data structure
        self.assertIn("states", example_data)
        self.assertIn("relations", example_data)
        self.assertIn("propositions", example_data)
        
        # Check states are populated
        states = example_data["states"]
        self.assertIn("worlds", states)
        self.assertIn("possible", states)
        self.assertIn("impossible", states)
        
        # Should have some world states
        self.assertTrue(len(states["worlds"]) > 0)
        
        # Check propositions
        if "p" in example_data["propositions"]:
            prop_values = example_data["propositions"]["p"]
            # Should have truth values at worlds
            self.assertTrue(len(prop_values) > 0)
            
        # Verify markdown content
        with open(markdown_path, 'r') as f:
            markdown_content = f.read()
            
        # Check key sections exist
        self.assertIn("## Example: test_bimodal", markdown_content)
        self.assertIn("Theory: bimodal", markdown_content)
        self.assertIn("Model Found: Yes", markdown_content)
        
        # Check for states section if present
        if states["worlds"]:
            self.assertIn("### States", markdown_content)
            
    def test_logos_output_integration(self):
        """Test logos theory output with possible/impossible states."""
        # Create test example
        example_path = os.path.join(self.test_dir, "test_logos.py")
        with open(example_path, 'w') as f:
            f.write(self.example_content)
            
        output_dir = os.path.join(self.test_dir, "output_logos")
        
        # Create and run
        project = BuildProject.from_example(example_path, theory_name="logos")
        module = BuildModule(project)
        module.output_manager = OutputManager(
            save_output=True,
            output_dir=output_dir
        )
        
        module.run_examples()
        
        # Load JSON
        json_path = os.path.join(output_dir, "models.json")
        with open(json_path, 'r') as f:
            json_data = json.load(f)
            
        example_data = json_data["examples"][0]
        
        # Logos should categorize states as possible/impossible
        states = example_data["states"]
        all_states = (states.get("worlds", []) + 
                     states.get("possible", []) + 
                     states.get("impossible", []))
        
        # Should have categorized some states
        self.assertTrue(len(all_states) > 0)
        
    def test_no_model_output(self):
        """Test output when no model is found."""
        # Create unsatisfiable example
        unsat_content = '''
"""Unsatisfiable example."""
N = 2
expectation = "UNSAT"
premise = p
conclusion = -p
'''
        
        example_path = os.path.join(self.test_dir, "test_unsat.py")
        with open(example_path, 'w') as f:
            f.write(unsat_content)
            
        output_dir = os.path.join(self.test_dir, "output_unsat")
        
        # Run example
        project = BuildProject.from_example(example_path, theory_name="bimodal")
        module = BuildModule(project)
        module.output_manager = OutputManager(
            save_output=True,
            output_dir=output_dir
        )
        
        module.run_examples()
        
        # Check JSON
        json_path = os.path.join(output_dir, "models.json")
        with open(json_path, 'r') as f:
            json_data = json.load(f)
            
        example_data = json_data["examples"][0]
        
        # Should indicate no model
        self.assertFalse(example_data["has_model"])
        self.assertIsNone(example_data["evaluation_world"])
        
        # Empty state collections
        states = example_data["states"]
        self.assertEqual(states["worlds"], [])
        self.assertEqual(states["possible"], [])
        self.assertEqual(states["impossible"], [])
        self.assertEqual(example_data["relations"], {})
        self.assertEqual(example_data["propositions"], {})
        
        # Check markdown
        markdown_path = os.path.join(output_dir, "README.md")
        with open(markdown_path, 'r') as f:
            markdown_content = f.read()
            
        self.assertIn("Model Found: No", markdown_content)


if __name__ == '__main__':
    unittest.main()