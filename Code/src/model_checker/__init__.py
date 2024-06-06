"""
test docstring
"""
import sys
import os
# Get the directory path of the current file
current_dir = os.path.dirname(__file__)
# Construct the full path to your project root
project_root = os.path.abspath(os.path.join(current_dir, ".."))
project_root = project_root[:-4] # bandaid fix to remove "/src" from the root
# Add the project root to the Python path
sys.path.append(project_root) # do we need to remove project_root from sys.path after 

from src.model_checker.model_structure import (
    StateSpace,
    Proposition,
    make_model_for,
)

__version__ = "0.3.24"
