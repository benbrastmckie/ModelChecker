"""
Tests for execution of bimodal examples through the CLI.

This test module simulates running examples through the CLI (dev_cli.py) to catch
API mismatches that only appear when running examples with the standard CLI.
"""

import os
import sys
import pytest
import subprocess
from pathlib import Path

# Get the absolute path to the project root
PROJECT_ROOT = Path(__file__).parents[5]  # Five levels up from this file


def test_cli_execution_of_examples():
    """Test running examples through dev_cli.py with the fixed API."""
    
    # Path to the examples.py file
    examples_path = PROJECT_ROOT / "src" / "model_checker" / "theory_lib" / "bimodal" / "examples.py"
    
    # Edit the examples.py file to uncomment some examples
    with open(examples_path, 'r') as f:
        content = f.read()
    
    # Store the original content to restore it later
    original_content = content
    
    try:
        # Uncomment a basic example (EX_CM_1) in the example_range
        modified_content = content.replace(
            '    # "EX_CM_1" : EX_CM_1_example,', 
            '    "EX_CM_1" : EX_CM_1_example,'
        )
        
        # Save the modified file
        with open(examples_path, 'w') as f:
            f.write(modified_content)
        
        # Run the example file through dev_cli.py
        dev_cli_path = PROJECT_ROOT / "dev_cli.py"
        result = subprocess.run(
            [str(dev_cli_path), str(examples_path)],
            capture_output=True,
            text=True,
            cwd=PROJECT_ROOT
        )
        
        # With the fixed API, CLI execution should succeed
        if "No module named 'z3'" not in result.stdout:  # If z3 is available
            assert "there is a countermodel" in result.stdout, "Example should run and find a countermodel"
            assert result.returncode == 0, "CLI execution should succeed with the fixed API"
        # If z3 module is not available, we'll still pass the test
        
    finally:
        # Restore the original content
        with open(examples_path, 'w') as f:
            f.write(original_content)