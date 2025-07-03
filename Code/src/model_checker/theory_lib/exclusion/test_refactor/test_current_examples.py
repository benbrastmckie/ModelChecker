#!/usr/bin/env python3
"""
Test current behavior by running examples.py directly and capturing output.
"""

import subprocess
import json
import time
import re
from pathlib import Path

def run_examples():
    """Run the examples.py file and capture output."""
    examples_path = Path(__file__).parent.parent / "examples.py"
    
    # Run the examples file
    cmd = [sys.executable, str(examples_path)]
    
    print("Running exclusion examples...")
    start_time = time.time()
    
    result = subprocess.run(cmd, capture_output=True, text=True)
    
    execution_time = time.time() - start_time
    
    return {
        'stdout': result.stdout,
        'stderr': result.stderr,
        'returncode': result.returncode,
        'execution_time': execution_time
    }

def analyze_output(output):
    """Analyze the output to find problematic examples."""
    lines = output.split('\n')
    
    current_example = None
    problematic_examples = []
    
    for line in lines:
        # Detect example names
        if "Running example:" in line:
            match = re.search(r"Running example:\s+(.+)", line)
            if match:
                current_example = match.group(1).strip()
        
        # Detect false premises or true conclusions
        if current_example and ("FALSE PREMISE" in line or "TRUE CONCLUSION" in line):
            if current_example not in problematic_examples:
                problematic_examples.append(current_example)
    
    return problematic_examples

if __name__ == "__main__":
    import sys
    
    # Run examples
    result = run_examples()
    
    if result['returncode'] != 0:
        print("Error running examples:")
        print(result['stderr'])
        sys.exit(1)
    
    # Analyze output
    problematic = analyze_output(result['stdout'])
    
    # Save results
    summary = {
        'execution_time': result['execution_time'],
        'total_output_lines': len(result['stdout'].split('\n')),
        'problematic_examples': problematic,
        'problematic_count': len(problematic)
    }
    
    with open('test_output_analysis.json', 'w') as f:
        json.dump(summary, f, indent=2)
    
    # Also save full output
    with open('test_output_full.txt', 'w') as f:
        f.write(result['stdout'])
    
    print(f"\nAnalysis complete:")
    print(f"Total execution time: {result['execution_time']:.2f}s")
    print(f"Problematic examples found: {len(problematic)}")
    if problematic:
        print(f"Problematic examples: {', '.join(problematic)}")
    print("\nResults saved to test_output_analysis.json and test_output_full.txt")