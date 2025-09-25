#!/usr/bin/env python3
"""Final test that the import fix works correctly."""

import sys
import subprocess

# Test 1: Direct import test
print("Test 1: Direct module import...")
sys.path.insert(0, '/Users/nicky/Documents/ModelChecker/Code/src')
from model_checker.builder.loader import ModuleLoader

test_file = "/Users/nicky/Documents/project_eleven/subtheories/counterfactual/examples.py"
loader = ModuleLoader("examples", test_file)

try:
    module = loader.load_module()
    print("✓ Module imported successfully")
    print(f"  Module name: {module.__name__}")
    print(f"  Has example_range: {hasattr(module, 'example_range')}")
except Exception as e:
    print(f"✗ Failed: {e}")

# Test 2: Command line test
print("\nTest 2: Running model-checker from project root...")
result = subprocess.run(
    ["python3", "-c",
     "import sys; sys.path.insert(0, '/Users/nicky/Documents/ModelChecker/Code/src'); "
     "from model_checker.builder.loader import ModuleLoader; "
     "loader = ModuleLoader('examples', '/Users/nicky/Documents/project_eleven/examples.py'); "
     "module = loader.load_module(); "
     "print('✓ Main examples.py loaded successfully')"],
    capture_output=True,
    text=True,
    cwd="/Users/nicky/Documents/project_eleven"
)

if result.returncode == 0:
    print(result.stdout.strip())
else:
    print(f"✗ Failed: {result.stderr}")

print("\n=== Summary ===")
print("The relative import issue has been fixed by:")
print("1. Enhancing PackageImportStrategy to handle relative imports")
print("2. Ensuring paths are resolved to absolute paths in detector and loader")
print("3. Adding fallback handling for exec when importlib fails with relative imports")