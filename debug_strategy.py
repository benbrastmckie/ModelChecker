#!/usr/bin/env python3
"""Debug which strategy is being selected for the file."""

import sys
from pathlib import Path

# Add src to path
src_dir = Path(__file__).parent / 'Code' / 'src'
sys.path.insert(0, str(src_dir))

from model_checker.builder.loader import ModuleLoader
from model_checker.builder.detector import ProjectDetector, ProjectType

test_file = "/Users/nicky/Documents/project_eleven/subtheories/counterfactual/examples.py"

loader = ModuleLoader("examples", test_file)

print(f"Module path: {test_file}")
print(f"Resolved path: {Path(test_file).resolve()}")
print(f"_is_theory_lib_file(): {loader._is_theory_lib_file()}")
print(f"_is_package(): {loader._is_package()}")

# Check detector directly
detector = ProjectDetector(test_file)
project_type = detector.detect_project_type()
print(f"ProjectType: {project_type}")
print(f"Package root: {detector.get_package_root()}")

# Check what's in the path
module_path = Path(test_file).resolve()
print(f"\nPath check:")
print(f"  'model_checker/theory_lib' in str: {'model_checker/theory_lib' in str(module_path)}")
print(f"  'model_checker\\theory_lib' in str: {'model_checker\\theory_lib' in str(module_path)}")