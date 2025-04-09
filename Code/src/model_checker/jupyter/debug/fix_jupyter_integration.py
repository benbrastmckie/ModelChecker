#!/usr/bin/env python3
"""
Fix script for ModelChecker Jupyter integration issues.
This script identifies and fixes common issues with the Jupyter integration.
"""

import os
import sys
import importlib
import site
import glob
import shutil
from pathlib import Path

def print_separator(title):
    print("\n" + "="*80)
    print(f" {title}")
    print("="*80)

def check_environment():
    """Check the environment configuration."""
    print_separator("ENVIRONMENT CHECK")
    print(f"Python version: {sys.version}")
    print(f"Current directory: {os.getcwd()}")
    
    # Check sys.path
    print("\nPython path:")
    project_in_path = False
    for p in sys.path:
        print(f"  {p}")
        if os.path.exists(os.path.join(p, 'src', 'model_checker')) or \
           os.path.exists(os.path.join(p, 'model_checker')):
            project_in_path = True
    
    if not project_in_path:
        print("\nWARNING: ModelChecker not found in Python path!")
    
    # Check user site-packages
    user_site = site.getusersitepackages()
    print(f"\nUser site-packages: {user_site}")
    if os.path.exists(os.path.join(user_site, 'model_checker')):
        print("ModelChecker found in user site-packages!")
    else:
        print("ModelChecker NOT found in user site-packages!")
    
    return project_in_path

def fix_paths():
    """Fix Python paths for ModelChecker."""
    print_separator("FIXING PATHS")
    
    # Get the project root
    current_dir = os.getcwd()
    if os.path.basename(current_dir) == 'debug':
        project_root = os.path.dirname(current_dir)
    else:
        project_root = current_dir
    
    # Validate project root
    if not os.path.exists(os.path.join(project_root, 'src', 'model_checker')):
        # Try parent directory
        parent_dir = os.path.dirname(project_root)
        if os.path.exists(os.path.join(parent_dir, 'src', 'model_checker')):
            project_root = parent_dir
        else:
            print(f"ERROR: Cannot find ModelChecker source in {project_root} or parent directory.")
            return False
    
    print(f"Project root identified as: {project_root}")
    
    # Add to Python path
    src_dir = os.path.join(project_root, 'src')
    paths_to_add = [project_root, src_dir]
    
    for path in paths_to_add:
        if path not in sys.path:
            sys.path.insert(0, path)
            print(f"Added to Python path: {path}")
    
    # Create symlinks in user site-packages
    user_site = site.getusersitepackages()
    os.makedirs(user_site, exist_ok=True)
    
    # Create symlink for model_checker
    target_dir = os.path.join(user_site, 'model_checker')
    source_dir = os.path.join(src_dir, 'model_checker')
    
    print(f"\nCreating symlinks in {user_site}:")
    
    # Remove existing directory or symlink
    if os.path.exists(target_dir):
        if os.path.islink(target_dir):
            os.unlink(target_dir)
            print(f"Removed existing symlink: {target_dir}")
        else:
            shutil.rmtree(target_dir)
            print(f"Removed existing directory: {target_dir}")
    
    # Create new symlink
    try:
        os.symlink(source_dir, target_dir, target_is_directory=True)
        print(f"Created symlink: {source_dir} -> {target_dir}")
    except OSError as e:
        print(f"Error creating symlink: {e}")
        
        # Alternative: copy files instead
        try:
            shutil.copytree(source_dir, target_dir)
            print(f"Copied directory (symlink failed): {source_dir} -> {target_dir}")
        except Exception as e:
            print(f"Error copying directory: {e}")
            return False
    
    return True

def check_dependencies():
    """Check and report on dependency status."""
    print_separator("CHECKING DEPENDENCIES")
    dependencies = {
        "ipywidgets": "Interactive widgets",
        "matplotlib": "Visualization",
        "networkx": "Graph visualization",
        "z3": "SMT solver (core)"
    }
    
    all_ok = True
    for dep, desc in dependencies.items():
        try:
            module = importlib.import_module(dep)
            version = getattr(module, "__version__", "unknown")
            print(f"✓ {dep}: v{version} - {desc}")
        except ImportError:
            print(f"✗ {dep}: MISSING - {desc}")
            all_ok = False
    
    if not all_ok:
        print("\nMissing dependencies! Please install them:")
        print("In nix-shell, these should be provided automatically.")
        print("Make sure you're running in a nix-shell using ./run_jupyter.sh")
    
    return all_ok

def verify_model_checker():
    """Verify ModelChecker can be imported and works correctly."""
    print_separator("VERIFYING MODEL_CHECKER")
    
    try:
        # First try to import the module
        if "model_checker" in sys.modules:
            importlib.reload(sys.modules["model_checker"])
        import model_checker
        
        print(f"✓ ModelChecker imported successfully from: {model_checker.__file__}")
        print(f"  Version: {model_checker.__version__}")
        
        # Try importing Jupyter integration
        from model_checker.jupyter import check_formula, ModelExplorer
        print(f"✓ Jupyter integration imported successfully")
        
        # Try accessing a theory
        from model_checker.jupyter.environment import get_available_theories
        theories = get_available_theories()
        print(f"✓ Available theories: {theories}")
        
        return True
    except Exception as e:
        print(f"✗ Error importing ModelChecker: {e}")
        import traceback
        traceback.print_exc()
        return False

def fix_jupyter_integration():
    """Fix common issues with the Jupyter integration."""
    print_separator("FIXING JUPYTER INTEGRATION")
    
    # Check if model_checker.jupyter module exists and is properly structured
    try:
        import model_checker
        jupyter_dir = os.path.join(os.path.dirname(model_checker.__file__), 'jupyter')
        
        if not os.path.exists(jupyter_dir):
            print(f"✗ Jupyter directory not found at: {jupyter_dir}")
            return False
        
        # Check for required files
        required_files = [
            '__init__.py', 'environment.py', 'operators.py', 
            'utils.py', 'display.py', 'interactive.py', 'adapters.py'
        ]
        
        missing_files = []
        for file in required_files:
            file_path = os.path.join(jupyter_dir, file)
            if not os.path.exists(file_path):
                missing_files.append(file)
        
        if missing_files:
            print(f"✗ Missing required files in jupyter directory: {missing_files}")
            return False
        
        print(f"✓ Jupyter integration structure looks correct")
        
        # Make sure the __init__.py exports the required functions
        from model_checker.jupyter import check_formula, ModelExplorer
        print(f"✓ Jupyter API functions are properly exported")
        
        return True
    except Exception as e:
        print(f"✗ Error checking Jupyter integration: {e}")
        import traceback
        traceback.print_exc()
        return False

def fix_notebook_compatibility():
    """Fix compatibility issues with the notebooks."""
    print_separator("FIXING NOTEBOOK COMPATIBILITY")
    
    # Path to simple_test.ipynb
    current_dir = os.getcwd()
    if os.path.basename(current_dir) != 'debug':
        notebook_path = os.path.join(current_dir, 'debug', 'simple_test.ipynb')
    else:
        notebook_path = os.path.join(current_dir, 'simple_test.ipynb')
    
    print(f"Looking for notebook at: {notebook_path}")
    
    if not os.path.exists(notebook_path):
        print(f"✗ Notebook not found at: {notebook_path}")
        return False
    
    print(f"✓ Notebook found at: {notebook_path}")
    
    # Create an enhanced version of the notebook
    enhanced_path = os.path.join(os.path.dirname(notebook_path), 'simple_test_enhanced.ipynb')
    
    try:
        import json
        
        # Read the original notebook
        with open(notebook_path, 'r') as f:
            notebook = json.load(f)
        
        # Modify the first cell to include robust path setup
        robust_setup = {
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "source": [
                "# Enhanced setup cell with robust path handling\n",
                "import os\n",
                "import sys\n",
                "import importlib\n",
                "\n",
                "# Get current directory and find project root\n",
                "current_dir = os.getcwd()\n",
                "print(f\"Current directory: {current_dir}\")\n",
                "\n",
                "# Try to find ModelChecker in various locations\n",
                "possible_roots = [\n",
                "    current_dir,  # Current directory\n",
                "    os.path.dirname(current_dir),  # Parent directory\n",
                "    os.path.join(os.path.dirname(current_dir), 'Code'),  # Parent/Code\n",
                "    os.path.expanduser(\"~/Documents/Philosophy/Projects/ModelChecker/Code\"),  # Common path\n",
                "]\n",
                "\n",
                "project_root = None\n",
                "for root in possible_roots:\n",
                "    if os.path.exists(os.path.join(root, 'src', 'model_checker')):\n",
                "        project_root = root\n",
                "        break\n",
                "\n",
                "if project_root:\n",
                "    print(f\"Found ModelChecker at: {project_root}\")\n",
                "    \n",
                "    # Add to Python path if needed\n",
                "    paths_to_add = [project_root, os.path.join(project_root, 'src')]\n",
                "    for path in paths_to_add:\n",
                "        if path not in sys.path:\n",
                "            sys.path.insert(0, path)\n",
                "            print(f\"Added to path: {path}\")\n",
                "else:\n",
                "    print(\"Could not find ModelChecker. Please run from the correct directory.\")\n",
                "\n",
                "# Print system path for diagnostics\n",
                "print(\"\\nSystem path:\")\n",
                "for p in sys.path:\n",
                "    print(f\"  {p}\")\n",
                "\n",
                "# Force reload model_checker if it was already imported\n",
                "if 'model_checker' in sys.modules:\n",
                "    print(\"\\nReloading model_checker module...\")\n",
                "    importlib.reload(sys.modules['model_checker'])"
            ]
        }
        
        # Replace the first setup cell
        if len(notebook["cells"]) > 0 and notebook["cells"][0]["cell_type"] == "code":
            notebook["cells"][0] = robust_setup
        else:
            notebook["cells"].insert(0, robust_setup)
        
        # Add error reporting to each cell
        for i in range(1, len(notebook["cells"])):
            if notebook["cells"][i]["cell_type"] == "code":
                # Add error handling to the cell
                cell_source = notebook["cells"][i]["source"]
                if isinstance(cell_source, list):
                    if not any("except Exception as e:" in line for line in cell_source):
                        new_source = cell_source.copy()
                        # If cell doesn't already have try/except, add it
                        if not any("try:" in line for line in cell_source):
                            new_source = ["try:\n"] + ["    " + line for line in new_source]
                            new_source.extend([
                                "\nexcept Exception as e:\n",
                                "    print(f\"Error: {str(e)}\")\n",
                                "    import traceback\n",
                                "    traceback.print_exc()"
                            ])
                            notebook["cells"][i]["source"] = new_source
        
        # Save the enhanced notebook
        with open(enhanced_path, 'w') as f:
            json.dump(notebook, f, indent=2)
        
        print(f"✓ Created enhanced notebook with better error handling: {enhanced_path}")
        print(f"  Please use this notebook for troubleshooting!")
        
        return True
    except Exception as e:
        print(f"✗ Error enhancing notebook: {e}")
        import traceback
        traceback.print_exc()
        return False

def main():
    """Main entry point for the fix script."""
    print("ModelChecker Jupyter Integration Fix Tool")
    print("========================================")
    
    # Run checks and fixes
    env_ok = check_environment()
    path_fixed = fix_paths()
    deps_ok = check_dependencies()
    mc_ok = verify_model_checker()
    jupyter_ok = fix_jupyter_integration()
    notebook_ok = fix_notebook_compatibility()
    
    # Summary
    print_separator("FIX SUMMARY")
    print(f"Environment check: {'✓ PASS' if env_ok else '✗ FAIL'}")
    print(f"Path fixes: {'✓ PASS' if path_fixed else '✗ FAIL'}")
    print(f"Dependencies: {'✓ PASS' if deps_ok else '✗ FAIL'}")
    print(f"ModelChecker verification: {'✓ PASS' if mc_ok else '✗ FAIL'}")
    print(f"Jupyter integration: {'✓ PASS' if jupyter_ok else '✗ FAIL'}")
    print(f"Notebook compatibility: {'✓ PASS' if notebook_ok else '✗ FAIL'}")
    
    all_ok = env_ok and path_fixed and deps_ok and mc_ok and jupyter_ok and notebook_ok
    
    if all_ok:
        print("\n✓ All checks and fixes completed successfully!")
        print("  You should now be able to run the notebooks without errors.")
    else:
        print("\n✗ Some checks or fixes failed.")
        print("  Review the errors above and take appropriate action.")
    
    print("\nRECOMMENDED NEXT STEPS:")
    print("1. Run: ./run_jupyter.sh")
    print("2. Open the enhanced notebook: debug/simple_test_enhanced.ipynb")
    print("3. Restart the kernel and run all cells")
    print("4. If errors persist, run debug/debug_error_capture.py for detailed diagnostics")
    
    return 0 if all_ok else 1

if __name__ == "__main__":
    sys.exit(main())