#!/usr/bin/env python3
"""Test script to compare monolithic vs modular iterator implementations."""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from model_checker.builder import BuildModule
from model_checker.iterate.debug import DebugModelIterator, ConstraintComparator
import subprocess
import json


def run_with_monolithic():
    """Run relevance example with monolithic core.py."""
    print("=== TESTING WITH MONOLITHIC IMPLEMENTATION ===")
    
    # First, ensure we're using monolithic version
    core_path = "src/model_checker/iterate/core.py"
    monolithic_path = "src/model_checker/iterate/core_monolithic.py"
    
    # Save current core.py if different from monolithic
    subprocess.run(["cp", core_path, "src/model_checker/iterate/core_current.py"])
    subprocess.run(["cp", monolithic_path, core_path])
    
    try:
        # Run relevance example
        result = subprocess.run(
            ["./dev_cli.py", "src/model_checker/theory_lib/logos/subtheories/relevance/examples.py"],
            capture_output=True,
            text=True
        )
        
        # Check for MODEL 2
        has_model_2 = "MODEL 2" in result.stdout
        model_count = result.stdout.count("MODEL ")
        
        print(f"Monolithic: Found {model_count} models, has MODEL 2: {has_model_2}")
        
        return {
            "success": has_model_2,
            "model_count": model_count,
            "output": result.stdout,
            "errors": result.stderr
        }
        
    finally:
        # Don't restore yet - we'll do that after modular test
        pass


def run_with_modular():
    """Run relevance example with modular implementation."""
    print("\n=== TESTING WITH MODULAR IMPLEMENTATION ===")
    
    # This will be called after core.py has been updated to modular version
    
    try:
        # Run relevance example
        result = subprocess.run(
            ["./dev_cli.py", "src/model_checker/theory_lib/logos/subtheories/relevance/examples.py"],
            capture_output=True,
            text=True
        )
        
        # Check for MODEL 2
        has_model_2 = "MODEL 2" in result.stdout
        model_count = result.stdout.count("MODEL ")
        
        print(f"Modular: Found {model_count} models, has MODEL 2: {has_model_2}")
        
        return {
            "success": has_model_2,
            "model_count": model_count,
            "output": result.stdout,
            "errors": result.stderr
        }
        
    finally:
        # Restore original core.py
        subprocess.run(["cp", "src/model_checker/iterate/core_current.py", "src/model_checker/iterate/core.py"])
        subprocess.run(["rm", "src/model_checker/iterate/core_current.py"])


def compare_results(mono_result, mod_result):
    """Compare results from both implementations."""
    print("\n=== COMPARISON ===")
    
    print(f"\nMonolithic:")
    print(f"  Success: {mono_result['success']}")
    print(f"  Models: {mono_result['model_count']}")
    if mono_result['errors']:
        print(f"  Errors: {mono_result['errors'][:200]}...")
    
    print(f"\nModular:")
    print(f"  Success: {mod_result['success']}")
    print(f"  Models: {mod_result['model_count']}")
    if mod_result['errors']:
        print(f"  Errors: {mod_result['errors'][:200]}...")
    
    if mono_result['success'] == mod_result['success'] and mono_result['model_count'] == mod_result['model_count']:
        print("\n✓ BOTH IMPLEMENTATIONS PRODUCE SAME RESULTS")
        return True
    else:
        print("\n✗ IMPLEMENTATIONS DIFFER!")
        
        # Show differences in output
        if mono_result['success'] and not mod_result['success']:
            print("\nModular implementation failed to find MODEL 2")
            
            # Look for escape attempts in modular output
            if "escape attempts" in mod_result['output']:
                print("Found escape attempts message - iterator stuck in isomorphic loop")
        
        return False


def main():
    """Main test function."""
    # First run with monolithic
    mono_result = run_with_monolithic()
    
    # Wait for user to update core.py to modular version
    print("\n" + "="*60)
    print("MANUAL STEP REQUIRED:")
    print("Please update src/model_checker/iterate/core.py to use the modular implementation")
    print("Then press Enter to continue...")
    print("="*60)
    input()
    
    # Run with modular
    mod_result = run_with_modular()
    
    # Compare
    success = compare_results(mono_result, mod_result)
    
    if not success:
        print("\nDEBUGGING HINTS:")
        print("1. Check if constraints are being properly passed between modules")
        print("2. Verify Z3 context is consistent across modules")
        print("3. Look for missing state transfers in model building")
        print("4. Check if theory-specific methods are being called correctly")
    
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())