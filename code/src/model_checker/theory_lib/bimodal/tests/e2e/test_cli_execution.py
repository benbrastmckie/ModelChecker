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
PROJECT_ROOT = Path(__file__).parents[6]  # Six levels up from this file


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
        # Replace example_range with just EX_CM_1 so the CLI runs one fast example
        import re
        modified_content = re.sub(
            r'(example_range\s*=\s*\{)[^}]*(})',
            r'\1\n    "EX_CM_1" : EX_CM_1_example,\n\2',
            content,
            count=1,
            flags=re.DOTALL,
        )

        with open(examples_path, 'w') as f:
            f.write(modified_content)

        dev_cli_path = PROJECT_ROOT / "dev_cli.py"
        result = subprocess.run(
            [str(dev_cli_path), str(examples_path)],
            capture_output=True,
            text=True,
            cwd=PROJECT_ROOT,
            timeout=30,
        )

        if "No module named 'z3'" not in result.stdout:
            assert "there is a countermodel" in result.stdout, "Example should run and find a countermodel"
            assert result.returncode == 0, "CLI execution should succeed with the fixed API"

    finally:
        with open(examples_path, 'w') as f:
            f.write(original_content)