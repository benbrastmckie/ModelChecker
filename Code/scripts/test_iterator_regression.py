#!/usr/bin/env python3
"""Iterator regression test script."""

import subprocess
import os
import sys
import re

# Ensure we're in the correct directory
os.chdir('/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code')

# Test files with iterate=2 examples
TEST_FILES = [
    ("exclusion", "src/model_checker/theory_lib/exclusion/examples.py"),
    ("imposition", "src/model_checker/theory_lib/imposition/examples.py"),
    ("constitutive", "src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py"),
    ("counterfactual", "src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py"),
    ("modal", "src/model_checker/theory_lib/logos/subtheories/modal/examples.py"),
    ("relevance", "src/model_checker/theory_lib/logos/subtheories/relevance/examples.py"),
    ("extensional", "src/model_checker/theory_lib/logos/subtheories/extensional/examples.py"),
]

def run_test(name, file_path):
    """Run a single test and check for errors."""
    print(f"Testing {name}...")
    
    try:
        result = subprocess.run(
            [sys.executable, 'dev_cli.py', file_path],
            capture_output=True,
            text=True,
            timeout=60  # 60 second timeout
        )
        
        # Check for errors
        error_patterns = [
            r"AttributeError",
            r"Error:",
            r"Warning:",
            r"cannot cast to concrete Boolean",
            r"Traceback",
            r"Exception"
        ]
        
        errors_found = []
        for pattern in error_patterns:
            if re.search(pattern, result.stdout, re.IGNORECASE) or re.search(pattern, result.stderr, re.IGNORECASE):
                errors_found.append(pattern)
        
        # Check for MODEL 2 in iterate examples
        has_iterate = False
        with open(file_path, 'r') as f:
            content = f.read()
            if "'iterate': 2" in content or '"iterate": 2' in content:
                has_iterate = True
        
        model2_found = 'MODEL 2' in result.stdout
        
        # Report results
        if errors_found:
            print(f"  ❌ ERRORS FOUND in {name}: {', '.join(errors_found)}")
            print(f"     Check output for details")
            return False
        elif has_iterate and not model2_found:
            print(f"  ❌ MODEL 2 NOT FOUND in {name}")
            return False
        else:
            if has_iterate:
                print(f"  ✅ {name} passed (MODEL 2 found)")
            else:
                print(f"  ✅ {name} passed")
            return True
            
    except subprocess.TimeoutExpired:
        print(f"  ❌ TIMEOUT in {name}")
        return False
    except Exception as e:
        print(f"  ❌ EXCEPTION in {name}: {e}")
        return False

def main():
    """Run all regression tests."""
    print("Running iterator regression tests...")
    print("=" * 50)
    
    all_passed = True
    
    for name, file_path in TEST_FILES:
        if not run_test(name, file_path):
            all_passed = False
    
    print("=" * 50)
    
    if all_passed:
        print("✅ All regression tests passed!")
        return 0
    else:
        print("❌ Some tests failed!")
        return 1

if __name__ == "__main__":
    sys.exit(main())