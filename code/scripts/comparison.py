#!/usr/bin/env python3
"""Wrapper to run the z3 vs cvc5 comparison benchmark.

Usage:
    ./comparison.py                          # Run all examples
    ./comparison.py --curated                # Run curated 24 examples (4 per subtheory)
    ./comparison.py --curated --table        # ASCII table output
    ./comparison.py --curated --format timing  # Timing-focused JSON
    ./comparison.py --output results.json    # Custom output file
    ./comparison.py --subtheory modal        # Run only modal examples
    ./comparison.py --verbose                # Show per-example output
    ./comparison.py --timeout 60             # Custom timeout per example

For full documentation, see: model_checker.theory_lib.logos.comparison
"""

import os
import sys

# Ensure local src is prioritized
src_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'src'))
sys.path.insert(0, src_path)

from model_checker.theory_lib.logos.comparison import main

if __name__ == "__main__":
    sys.exit(main())
