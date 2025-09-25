#!/usr/bin/env python3
"""Test all theories for import and functionality."""

import sys
import subprocess
import os

sys.path.insert(0, '/Users/nicky/Documents/ModelChecker/Code/src')

theories = ['logos', 'exclusion', 'imposition', 'bimodal']
results = {}

print("=== Testing all theories ===\n")

for theory in theories:
    print(f"Testing {theory}...")

    # Test 1: Can we import the theory?
    try:
        theory_module = __import__(f'model_checker.theory_lib.{theory}', fromlist=['get_theory'])

        # Test 2: Can we get the theory configuration?
        if hasattr(theory_module, 'get_theory'):
            theory_config = theory_module.get_theory()
            operators = theory_config.get('operators', {})
            # OperatorCollection doesn't have len(), check if it has operator_dictionary
            if hasattr(operators, 'operator_dictionary'):
                op_count = len(operators.operator_dictionary)
            elif hasattr(operators, '__len__'):
                op_count = len(operators)
            else:
                op_count = "unknown number of"
            print(f"  ✓ Theory loaded, {op_count} operators defined")

            # Test 3: Can we get examples without circular import?
            if hasattr(theory_module, 'get_examples'):
                examples = theory_module.get_examples()
                if isinstance(examples, dict):
                    if 'all' in examples:
                        example_count = len(examples['all'])
                    else:
                        example_count = len(examples)
                    print(f"  ✓ Examples loaded: {example_count} examples")
                else:
                    print(f"  ✓ Examples loaded")

            results[theory] = "PASS"
        else:
            print(f"  ✗ No get_theory function")
            results[theory] = "FAIL - no get_theory"

    except ImportError as e:
        print(f"  ✗ Import failed: {e}")
        results[theory] = f"FAIL - {str(e)[:50]}"
    except Exception as e:
        print(f"  ✗ Error: {e}")
        results[theory] = f"FAIL - {str(e)[:50]}"

print("\n=== Testing example files ===\n")

# Test running actual example files for logos subtheories
logos_subtheories = ['extensional', 'modal', 'constitutive', 'counterfactual', 'relevance']

for subtheory in logos_subtheories:
    print(f"Testing logos/{subtheory} examples...")
    example_path = f"/Users/nicky/Documents/ModelChecker/Code/src/model_checker/theory_lib/logos/subtheories/{subtheory}/examples.py"

    if os.path.exists(example_path):
        # Just test that we can load it without errors
        result = subprocess.run(
            ["python3", "-c",
             f"import sys; sys.path.insert(0, '/Users/nicky/Documents/ModelChecker/Code/src'); "
             f"from model_checker.builder.loader import ModuleLoader; "
             f"loader = ModuleLoader('examples', '{example_path}'); "
             f"module = loader.load_module(); "
             f"print('OK')"],
            capture_output=True,
            text=True,
            timeout=5
        )

        if result.returncode == 0 and 'OK' in result.stdout:
            print(f"  ✓ Examples file loads correctly")
        else:
            print(f"  ✗ Failed to load: {result.stderr[:100]}")
    else:
        print(f"  ✗ File not found")

print("\n=== Summary ===")
for theory, result in results.items():
    status = "✓" if result == "PASS" else "✗"
    print(f"{status} {theory}: {result}")