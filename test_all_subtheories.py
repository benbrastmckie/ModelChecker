#!/usr/bin/env python3
"""Test all subtheories for import and operator loading."""

import sys
import subprocess

sys.path.insert(0, '/Users/nicky/Documents/ModelChecker/Code/src')

subtheories = ['extensional', 'modal', 'constitutive', 'counterfactual', 'relevance']
results = {}

print("=== Testing all subtheories ===\n")

for subtheory in subtheories:
    print(f"Testing {subtheory}...")

    # Test 1: Can we import the subtheory module?
    try:
        sys.path.insert(0, '/Users/nicky/Documents/project_eleven')
        module = __import__(f'subtheories.{subtheory}', fromlist=['get_operators'])

        # Test 2: Can we get operators?
        if hasattr(module, 'get_operators'):
            ops = module.get_operators()
            op_count = len(ops) if ops else 0
            print(f"  ✓ Module imported, {op_count} operators defined")

            # Test 3: Can we run an example file?
            example_path = f"/Users/nicky/Documents/project_eleven/subtheories/{subtheory}/examples.py"
            result = subprocess.run(
                ["python3", "-c",
                 f"import sys; sys.path.insert(0, '/Users/nicky/Documents/ModelChecker/Code/src'); "
                 f"from model_checker.builder.loader import ModuleLoader; "
                 f"loader = ModuleLoader('examples', '{example_path}'); "
                 f"module = loader.load_module(); "
                 f"print('Loaded successfully')"],
                capture_output=True,
                text=True,
                timeout=5
            )

            if result.returncode == 0:
                print(f"  ✓ Examples file loads correctly")
                results[subtheory] = "PASS"
            else:
                print(f"  ✗ Examples file failed: {result.stderr[:100]}")
                results[subtheory] = "FAIL - examples"
        else:
            print(f"  ✗ No get_operators function")
            results[subtheory] = "FAIL - no operators"

    except Exception as e:
        print(f"  ✗ Import failed: {e}")
        results[subtheory] = "FAIL - import"

print("\n=== Summary ===")
for subtheory, result in results.items():
    status = "✓" if result == "PASS" else "✗"
    print(f"{status} {subtheory}: {result}")