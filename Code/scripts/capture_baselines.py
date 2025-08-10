#!/usr/bin/env python3
"""Capture baseline outputs for iterator refactoring."""

import subprocess
import os
import sys

# Ensure we're in the correct directory
os.chdir('/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code')

# Create baseline directory
baseline_dir = 'docs/specs/baselines/iterator_refactor'
os.makedirs(baseline_dir, exist_ok=True)

# List of test files to capture
test_files = [
    ('exclusion', 'src/model_checker/theory_lib/exclusion/examples.py'),
    ('imposition', 'src/model_checker/theory_lib/imposition/examples.py'),
    ('constitutive', 'src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py'),
    ('counterfactual', 'src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py'),
    ('modal', 'src/model_checker/theory_lib/logos/subtheories/modal/examples.py'),
    ('relevance', 'src/model_checker/theory_lib/logos/subtheories/relevance/examples.py'),
    ('extensional', 'src/model_checker/theory_lib/logos/subtheories/extensional/examples.py'),
]

print("Capturing baselines for iterator refactoring...")

for name, file_path in test_files:
    output_file = os.path.join(baseline_dir, f'{name}_baseline.txt')
    print(f"Capturing {name}...")
    
    # Run dev_cli.py and capture output
    try:
        result = subprocess.run(
            [sys.executable, 'dev_cli.py', file_path],
            capture_output=True,
            text=True
        )
        
        # Write both stdout and stderr to capture complete output
        with open(output_file, 'w') as f:
            f.write(result.stdout)
            if result.stderr:
                f.write("\n=== STDERR ===\n")
                f.write(result.stderr)
        
        print(f"  ✓ Captured {name} to {output_file}")
        
        # Check for MODEL 2 in output (for iterate=2 examples)
        if 'MODEL 2' in result.stdout:
            print(f"  ✓ MODEL 2 found in {name}")
        
    except Exception as e:
        print(f"  ✗ Error capturing {name}: {e}")

print("\nBaseline capture complete!")