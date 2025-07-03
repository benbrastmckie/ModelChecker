#!/usr/bin/env python3
"""
Run a single example to understand the structure and evaluate models.
"""

import sys
import os
from pathlib import Path

# Add parent directories to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

# Import the example module
import importlib.spec
spec = importlib.spec.spec_from_file_location(
    "examples", 
    Path(__file__).parent.parent / "examples.py"
)
examples = importlib.spec.module_from_spec(spec)
spec.loader.exec_module(examples)

# Get semantic theories and example range
semantic_theories = examples.semantic_theories
example_range = examples.example_range

# Run the first example
example_name = list(example_range.keys())[0]
example_settings = example_range[example_name]

print(f"Running example: {example_name}")
print(f"Settings: {example_settings}")

# Try running directly as in examples.py
if __name__ == "__main__":
    # Set the file path to the examples module
    original_file = sys.argv[0]
    sys.argv[0] = str(Path(__file__).parent.parent / "examples.py")
    
    # Import and run the main function
    from model_checker.__main__ import main
    main()