#!/usr/bin/env python3
"""Simple test for logos theory with iterate=2"""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

# Test with the dev_cli approach
import subprocess

try:
    print("Testing logos theory with iterate=2...")
    
    # Create a simple logos example file with iterate=2
    test_content = '''# Simple logos test with iterate=2
from model_checker.theory_lib.logos import LogosSemantics, LogosModelStructure, LogosProposition

# Example case: simple countermodel
premises = ['~A']
conclusions = ['A']

settings = {
    'N': 3,
    'iterate': 2,  # Test iteration
    'max_time': 5,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

# Export for module runner
theory = {
    'semantics': LogosSemantics,
    'model_structure': LogosModelStructure, 
    'proposition': LogosProposition,
}

unit_tests = {
    'TEST_LOGOS': [premises, conclusions, settings]
}
'''
    
    with open('test_logos_temp.py', 'w') as f:
        f.write(test_content)
    
    # Run it with dev_cli
    result = subprocess.run(['./dev_cli.py', 'test_logos_temp.py'], 
                          capture_output=True, text=True, timeout=30)
    
    print("STDOUT:")
    print(result.stdout)
    if result.stderr:
        print("STDERR:")
        print(result.stderr)
        
    print(f"Return code: {result.returncode}")
    
    # Clean up
    if os.path.exists('test_logos_temp.py'):
        os.remove('test_logos_temp.py')
        
except Exception as e:
    print(f"Error: {e}")
    import traceback
    traceback.print_exc()