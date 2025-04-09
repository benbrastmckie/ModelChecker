#!/usr/bin/env bash
# Quick script to start Jupyter with ModelChecker support

# Get the directory of this script
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Enter the nix-shell and run the jupyter link script with --launch option
# Note: Removed automatic creation of example notebook
cd "$SCRIPT_DIR" && nix-shell --run "./jupyter_link.py --launch"

# If you want to create an example notebook, uncomment the line below instead:
# cd "$SCRIPT_DIR" && nix-shell --run "./jupyter_link.py --launch --example"