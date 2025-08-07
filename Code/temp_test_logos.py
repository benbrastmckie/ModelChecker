#!/usr/bin/env python3
"""Test runner for logos theory with iterations."""

from model_checker.builder.module import BuildModule
import sys

class ModuleFlags:
    def __init__(self):
        self.file_path = "src/model_checker/theory_lib/logos/examples.py"
        self.print_constraints = False
        self.print_z3 = False
        self.print_impossible = False
        self.save_output = False
        self.maximize = False
        self.contingent = False
        self.non_empty = False
        self.disjoint = False
        self.non_null = False
        self.align_vertically = False
        self.interactive = False
        self.load_theory = "logos"

# Run iterations
flags = ModuleFlags()
for i in range(3):
    print(f"\n{'='*60}")
    print(f"ITERATION {i+1} of 3")
    print(f"{'='*60}\n")
    
    try:
        module = BuildModule(flags)
        module.run()
    except Exception as e:
        print(f"Error during iteration {i+1}: {e}")
        import traceback
        traceback.print_exc()
