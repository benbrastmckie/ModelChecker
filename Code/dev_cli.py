#!/usr/bin/env python3
"""Development CLI entry point that ensures local code is used."""

import os
import sys

# Ensure local src is prioritized
src_path = os.path.abspath(os.path.join(os.path.dirname(__file__), 'src'))
sys.path.insert(0, src_path)

# Import all necessary modules explicitly from local source
try:
    # Try to import the main function from local source
    from src.model_checker.__main__ import main
except ImportError as e:
    print(f"Error importing from local source: {e}")
    print(f"Current sys.path: {sys.path}")
    sys.exit(1)

if __name__ == "__main__":
    # Get command line arguments
    if len(sys.argv) > 1:
        args = sys.argv[1:]
    else:
        # If no arguments provided, use the default example
        args = [os.path.join(src_path, "model_checker", "theory_lib", "default", "examples.py")]
    
    # Set sys.argv for the main function
    sys.argv = [sys.argv[0]] + args
    
    # Call the main function
    main()
