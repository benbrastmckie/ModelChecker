#!/usr/bin/env python3
"""
Test script to diagnose Jupyter integration issues in ModelChecker.
"""

import os
import sys
import importlib
import traceback

def print_sep(title):
    """Print a section separator."""
    print("\n" + "=" * 80)
    print(f" {title}")
    print("=" * 80)

def check_environment():
    """Check basic environment information."""
    print_sep("ENVIRONMENT")
    print(f"Python version: {sys.version}")
    print(f"Current directory: {os.getcwd()}")
    print("\nPYTHONPATH:")
    for p in sys.path:
        print(f"  {p}")

def setup_paths():
    """Set up paths for local development."""
    print_sep("SETTING UP PATHS")
    current_dir = os.getcwd()
    src_dir = os.path.join(current_dir, 'src')
    
    # Add paths if they're not already in sys.path
    paths_to_add = [current_dir, src_dir]
    for path in paths_to_add:
        if os.path.exists(path) and path not in sys.path:
            sys.path.insert(0, path)
            print(f"Added to PYTHONPATH: {path}")
    
    return current_dir, src_dir

def check_import(module_name):
    """Try to import a module and report results."""
    try:
        module = importlib.import_module(module_name)
        if hasattr(module, '__file__'):
            print(f"✓ Successfully imported {module_name} from {module.__file__}")
            return True, module
        else:
            print(f"✓ Successfully imported {module_name} (built-in module)")
            return True, module
    except Exception as e:
        print(f"✗ Failed to import {module_name}: {str(e)}")
        traceback.print_exc(limit=1)
        return False, None

def check_jupyter_integration():
    """Test the Jupyter integration components."""
    print_sep("TESTING JUPYTER INTEGRATION")
    
    # Main package import
    success, model_checker = check_import("model_checker")
    if not success:
        return False
    
    # Check version
    print(f"ModelChecker version: {getattr(model_checker, '__version__', 'unknown')}")
    
    # Check jupyter module
    success, jupyter = check_import("model_checker.jupyter")
    if not success:
        return False
    
    # Check components within jupyter
    components = [
        "model_checker.jupyter.environment",
        "model_checker.jupyter.unicode",
        "model_checker.jupyter.utils",
        "model_checker.jupyter.adapters",
        "model_checker.jupyter.display",
        "model_checker.jupyter.interactive"
    ]
    
    for component in components:
        success, _ = check_import(component)
        if not success:
            return False
    
    # Try accessing key functions
    print_sep("TESTING API FUNCTIONS")
    try:
        check_formula = getattr(model_checker, "check_formula", None)
        if check_formula:
            print(f"✓ check_formula function exists: {check_formula}")
        else:
            print(f"✗ check_formula function not found in model_checker")
            
        model_explorer = getattr(model_checker, "ModelExplorer", None)
        if model_explorer:
            print(f"✓ ModelExplorer class exists: {model_explorer}")
        else:
            print(f"✗ ModelExplorer class not found in model_checker")
    except Exception as e:
        print(f"Error testing API functions: {str(e)}")
        traceback.print_exc()
        return False
    
    return True

def check_dependencies():
    """Check if required dependencies are installed."""
    print_sep("CHECKING DEPENDENCIES")
    dependencies = [
        "ipywidgets",
        "matplotlib",
        "networkx",
        "z3"
    ]
    
    all_success = True
    for dep in dependencies:
        success, module = check_import(dep)
        if not success:
            all_success = False
            if dep in ["ipywidgets", "matplotlib", "networkx"]:
                print(f"Required for Jupyter integration: pip install {dep}")
    
    return all_success

def main():
    """Main entry point."""
    check_environment()
    current_dir, src_dir = setup_paths()
    
    # Check dependencies first
    deps_ok = check_dependencies()
    if not deps_ok:
        print("\nWarning: Some dependencies are missing!")
    
    # Check jupyter integration
    integration_ok = check_jupyter_integration()
    
    # Summary
    print_sep("SUMMARY")
    if integration_ok:
        print("✓ Jupyter integration checks passed!")
    else:
        print("✗ Jupyter integration checks failed!")
        
    # Suggestions
    print_sep("SUGGESTIONS")
    if not integration_ok:
        print("1. Make sure you're running from the ModelChecker/Code directory")
        print("2. Try entering a nix-shell first if you're on NixOS")
        print("3. Check that the model_checker package is properly installed or in PYTHONPATH")
        print(f"4. Create a demo notebook with the following code to debug:")
        print("""
import sys
import os

# Add paths manually if needed
current_dir = os.getcwd()
# Adjust these paths to point to your ModelChecker/Code directory
project_root = os.path.abspath(os.path.join(current_dir, "../../.."))  
src_dir = os.path.join(project_root, "src")

if os.path.exists(src_dir):
    sys.path.insert(0, project_root)
    sys.path.insert(0, src_dir)
    print(f"Added to path: {project_root} and {src_dir}")

# Try imports
try:
    import model_checker
    print(f"Successfully imported model_checker from {model_checker.__file__}")
    from model_checker.jupyter import check_formula
    print("Successfully imported check_formula")
except Exception as e:
    print(f"Error importing: {str(e)}")
    import traceback
    traceback.print_exc()
    
# Print system path
print("\\nSystem path:")
for p in sys.path:
    print(f"  {p}")
""")

if __name__ == "__main__":
    main()
