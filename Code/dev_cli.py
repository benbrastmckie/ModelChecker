#!/usr/bin/env python3
"""Development CLI entry point that ensures local code is used."""

import os
import sys
import logging

# Configure root logger to show debug messages
logging.basicConfig(
    level=logging.INFO,
    format='%(message)s',
    stream=sys.stdout
)

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
    # Check for isomorphism debug flag
    if "--iso-debug" in sys.argv:
        # Set logging level to debug for isomorphism checks
        logging.getLogger("model_checker.builder.iterate").setLevel(logging.DEBUG)
        logging.getLogger("model_checker.builder.graph_utils").setLevel(logging.DEBUG)
        sys.argv.remove("--iso-debug")
        print("Enabled isomorphism debugging")
    
    # Get command line arguments
    if len(sys.argv) > 1:
        # Fix common command variations
        
        # Fix the -load/-l argument to correctly handle load_theory flag
        if "-load" in sys.argv:
            load_index = sys.argv.index("-load")
            sys.argv[load_index] = "-l"
            
        # Handle variations like --load
        if "--load" in sys.argv:
            load_index = sys.argv.index("--load")
            sys.argv[load_index] = "-l"
        
        args = sys.argv[1:]
    else:
        # If no arguments provided, use the logos example
        args = [os.path.join(src_path, "model_checker", "theory_lib", "logos", "examples.py")]
    
    # Set sys.argv for the main function
    sys.argv = [sys.argv[0]] + args
    
    # Call the main function
    main()
