#!/usr/bin/env python3
"""
Error capturing script to diagnose Jupyter integration issues.
Run this script to capture detailed error information when running the simple_test notebook.
"""

import os
import sys
import traceback
import importlib
import io
from contextlib import redirect_stdout, redirect_stderr

def print_separator(title):
    print("\n" + "="*80)
    print(f" {title}")
    print("="*80)

def run_with_error_capture(code_block, block_name):
    """Run a code block and capture any errors and output."""
    print_separator(f"RUNNING BLOCK: {block_name}")
    
    # Capture stdout and stderr
    stdout_buffer = io.StringIO()
    stderr_buffer = io.StringIO()
    
    try:
        # First print the code we're about to execute
        print("CODE:")
        print("-----")
        print(code_block)
        print("\nOUTPUT:")
        print("-------")
        
        # Execute with output capturing
        with redirect_stdout(stdout_buffer), redirect_stderr(stderr_buffer):
            exec(code_block)
        
        # Print captured output
        stdout = stdout_buffer.getvalue()
        stderr = stderr_buffer.getvalue()
        
        if stdout:
            print(stdout)
        if stderr:
            print("STDERR:")
            print(stderr)
            
        print("\nResult: SUCCESS")
        return True
    except Exception as e:
        # Print captured output before showing the error
        stdout = stdout_buffer.getvalue()
        stderr = stderr_buffer.getvalue()
        
        if stdout:
            print(stdout)
        if stderr:
            print("STDERR:")
            print(stderr)
        
        print("\nERROR:")
        print(f"{type(e).__name__}: {e}")
        traceback.print_exc()
        
        # Get detailed information about the exception
        print("\nDETAILED ERROR INFO:")
        print(f"Exception type: {type(e).__name__}")
        print(f"Exception message: {str(e)}")
        print(f"Exception args: {e.args}")
        
        # Try to get more context if possible
        if hasattr(e, '__traceback__'):
            tb = e.__traceback__
            while tb:
                frame = tb.tb_frame
                print(f"\nFrame: {frame.f_code.co_name} in {frame.f_code.co_filename}:{tb.tb_lineno}")
                print("Local variables:")
                for key, value in frame.f_locals.items():
                    try:
                        print(f"  {key}: {repr(value)[:100]}")
                    except:
                        print(f"  {key}: <cannot display value>")
                tb = tb.tb_next
        
        print("\nResult: FAILED")
        return False

def main():
    """Run all the code blocks from simple_test.ipynb"""
    print_separator("ENVIRONMENT INFORMATION")
    print(f"Python version: {sys.version}")
    print(f"Current directory: {os.getcwd()}")
    print(f"sys.path:")
    for p in sys.path:
        print(f"  {p}")

    # Block 1: Set up the environment
    block1 = """
import sys
import os

# Get current directory
current_dir = os.getcwd()
print(f"Current directory: {current_dir}")

# Add src to path if needed
src_dir = os.path.join(current_dir, 'src')
if os.path.exists(src_dir) and src_dir not in sys.path:
    sys.path.insert(0, src_dir)
    print(f"Added to path: {src_dir}")

# Print system path for diagnostics
print("\\nSystem path:")
for p in sys.path:
    print(f"  {p}")
"""
    success_block1 = run_with_error_capture(block1, "Environment Setup")

    # Block 2: Basic imports
    block2 = """
# Basic imports
try:
    import model_checker
    print(f"ModelChecker version: {model_checker.__version__}")
    print(f"ModelChecker path: {model_checker.__file__}")
except Exception as e:
    print(f"Error importing model_checker: {str(e)}")
"""
    success_block2 = run_with_error_capture(block2, "Basic Imports")

    # Block 3: Import the Jupyter integration
    block3 = """
# Import the Jupyter integration
try:
    from model_checker.jupyter import check_formula, find_countermodel, ModelExplorer
    print("Successfully imported Jupyter integration components")
except Exception as e:
    print(f"Error importing Jupyter components: {str(e)}")
"""
    success_block3 = run_with_error_capture(block3, "Jupyter Integration Imports")

    # Block 4: Test environment setup
    block4 = """
# Test environment setup
try:
    from model_checker.jupyter.environment import setup_environment, get_diagnostic_info
    
    # Run environment setup
    env_info = setup_environment()
    print(f"Environment setup result: {env_info}")
    
    # Get diagnostic info
    diag_info = get_diagnostic_info()
    print(f"\\nDiagnostic info:")
    print(f"- Python version: {diag_info.get('python_version', 'unknown')}")
    print(f"- ModelChecker path: {diag_info.get('model_checker', {}).get('path', 'unknown')}")
    print(f"- Available theories: {diag_info.get('model_checker', {}).get('theories', [])}")
except Exception as e:
    print(f"Error running environment setup: {str(e)}")
"""
    success_block4 = run_with_error_capture(block4, "Environment Setup Test")

    # Block 5: Test formula checking
    block5 = """
# Test formula checking
try:
    # Simple formula
    print("Checking formula: p → (q → p)")
    
    # Additional diagnostic to track down issues
    print("Importing check_formula...")
    from model_checker.jupyter import check_formula
    
    print("Importing display modules...")
    import importlib
    if 'IPython.display' in sys.modules:
        importlib.reload(sys.modules['IPython.display'])
    from IPython.display import display, HTML
    
    print("Running check_formula...")
    result = check_formula("p → (q → p)")
    
    print("Result type:", type(result))
    print("Result content:", result)
    
    # Display result - this should generate visual output in the notebook
    print("Displaying result...")
    # In a script context, we can't actually display the result, so just print it
    print(result)
except Exception as e:
    print(f"Error checking formula: {str(e)}")
    import traceback
    traceback.print_exc()
"""
    success_block5 = run_with_error_capture(block5, "Formula Checking Test")

    # Block 6: Test with premises
    block6 = """
# Test with premises
try:
    print("Checking formula with premises: q with premises [p, p → q]")
    from model_checker.jupyter import check_formula
    from IPython.display import display
    
    result = check_formula("q", premises=["p", "p → q"])
    
    # Display result
    print("Result type:", type(result))
    print("Result content:", result)
    print(result)
except Exception as e:
    print(f"Error checking formula with premises: {str(e)}")
    import traceback
    traceback.print_exc()
"""
    success_block6 = run_with_error_capture(block6, "Formula With Premises Test")

    # Block 7: Test interactive explorer
    block7 = """
# Test interactive explorer
try:
    print("Creating interactive explorer...")
    from model_checker.jupyter import ModelExplorer
    
    # Additional diagnostic information
    print("Importing ipywidgets...")
    import ipywidgets
    print(f"ipywidgets version: {ipywidgets.__version__}")
    
    print("Creating ModelExplorer instance...")
    explorer = ModelExplorer()
    
    print("ModelExplorer instance created successfully")
    print("ModelExplorer type:", type(explorer))
    print("ModelExplorer attributes:", dir(explorer)[:10], "...")
    
    # In a script context, we can't actually display the widget
    print("explorer.display() would be called in notebook")
except Exception as e:
    print(f"Error creating interactive explorer: {str(e)}")
    import traceback
    traceback.print_exc()
"""
    success_block7 = run_with_error_capture(block7, "Interactive Explorer Test")

    # Summary
    print_separator("TEST SUMMARY")
    blocks = [
        ("Environment Setup", success_block1),
        ("Basic Imports", success_block2),
        ("Jupyter Integration Imports", success_block3),
        ("Environment Setup Test", success_block4),
        ("Formula Checking Test", success_block5),
        ("Formula With Premises Test", success_block6),
        ("Interactive Explorer Test", success_block7)
    ]
    
    for name, success in blocks:
        status = "✓ PASS" if success else "✗ FAIL"
        print(f"{status} - {name}")
    
    all_passed = all(success for _, success in blocks)
    print(f"\nOverall result: {'SUCCESS' if all_passed else 'FAILED'}")
    
    print("\nTo fix issues, consider:")
    print("1. Ensure you're running in a nix-shell (./run_jupyter.sh)")
    print("2. Check that all dependencies are installed (ipywidgets, matplotlib, networkx)")
    print("3. Make sure the MODEL_CHECKER_DIR environment variable is set correctly")
    print("4. Try running with fresh Python session (restart the kernel)")

if __name__ == "__main__":
    main()