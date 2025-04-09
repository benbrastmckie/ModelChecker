"""
Environment setup utilities for Jupyter notebooks.

This module ensures the ModelChecker package is properly configured
in the notebook environment, handling path resolution and imports.
"""

import os
import sys
import importlib
import warnings
from typing import Dict, List, Any, Optional, Union


def setup_environment() -> Dict[str, Any]:
    """
    Set up the environment for notebooks by adding the correct paths
    to sys.path and ensuring all modules can be imported properly.
    
    Returns:
        dict: Information about the setup environment
    """
    # Auto-detect project root
    current_dir = os.getcwd()
    project_root = _find_project_root(current_dir)
    
    if not project_root:
        # More aggressive search for project root
        for parent_level in range(5):  # Go up to 5 levels up
            parent_dir = current_dir
            for _ in range(parent_level + 1):
                parent_dir = os.path.dirname(parent_dir)
            
            # Check if this could be the project root
            if os.path.exists(os.path.join(parent_dir, 'pyproject.toml')) or \
               os.path.exists(os.path.join(parent_dir, 'src', 'model_checker')):
                project_root = parent_dir
                break
        
        if not project_root:
            # Look for common installation paths
            common_paths = [
                os.path.expanduser("~/Documents/Philosophy/Projects/ModelChecker/Code"),
                os.path.expanduser("~/ModelChecker/Code"),
                # Add other common paths as needed
            ]
            
            for path in common_paths:
                if os.path.exists(path) and os.path.exists(os.path.join(path, 'src', 'model_checker')):
                    project_root = path
                    break
        
        if not project_root:
            warnings.warn(
                "Could not automatically find ModelChecker project root. "
                "If you experience import errors, please specify the path manually."
            )
            return {"status": "warning", "message": "Could not find project root"}
    
    # Add paths to sys.path if needed
    paths_to_add = [
        project_root,
        os.path.join(project_root, 'src'),
    ]
    
    # Ensure the paths exist before adding
    for path in paths_to_add:
        if os.path.exists(path) and path not in sys.path:
            sys.path.insert(0, path)
            print(f"Added to Python path: {path}")
    
    # Try importing model_checker with helpful error messages
    try:
        # If already imported, reload it to ensure we're using the right one
        if "model_checker" in sys.modules:
            importlib.reload(sys.modules["model_checker"])
            import model_checker
            print(f"Reloaded model_checker from {model_checker.__file__}")
        else:
            import model_checker
            print(f"Imported model_checker from {model_checker.__file__}")
        
        return {
            "status": "success",
            "project_root": project_root,
            "model_checker_path": model_checker.__file__,
            "model_checker_version": getattr(model_checker, "__version__", "unknown"),
            "python_path": sys.path,
        }
    except ImportError as e:
        error_message = f"Could not import model_checker: {str(e)}"
        print(f"ERROR: {error_message}")
        print("\nCurrent sys.path:")
        for p in sys.path:
            print(f"  {p}")
        print("\nTroubleshooting tips:")
        print("1. Make sure you're running from the ModelChecker/Code directory")
        print("2. Try manually adding paths: import sys; sys.path.insert(0, '/path/to/ModelChecker/Code/src')")
        print("3. Check that the model_checker package is properly installed")
        
        return {
            "status": "error",
            "message": error_message,
            "project_root": project_root,
            "python_path": sys.path,
        }


def _find_project_root(start_dir: str) -> Optional[str]:
    """
    Find the ModelChecker project root by looking for key identifiers.
    
    Args:
        start_dir: Directory to start searching from
        
    Returns:
        str or None: Path to project root if found, None otherwise
    """
    # Search strategies:
    # 1. Look for pyproject.toml with model_checker in it
    # 2. Look for src/model_checker directory
    # 3. Look for common installation paths
    
    # First check if we're already in the project root
    if os.path.exists(os.path.join(start_dir, 'pyproject.toml')) and \
       os.path.exists(os.path.join(start_dir, 'src', 'model_checker')):
        return start_dir
    
    # Search parent directories for project root
    current_dir = start_dir
    for _ in range(10):  # Limit search depth
        parent_dir = os.path.dirname(current_dir)
        if parent_dir == current_dir:  # We've reached the filesystem root
            break
            
        current_dir = parent_dir
        
        # Check if this directory is the project root
        if os.path.exists(os.path.join(current_dir, 'pyproject.toml')) and \
           os.path.exists(os.path.join(current_dir, 'src', 'model_checker')):
            return current_dir
    
    # Check well-known locations
    common_locations = [
        os.path.expanduser("~/Documents/Philosophy/Projects/ModelChecker/Code"),
        os.path.expanduser("~/ModelChecker/Code"),
    ]
    
    for location in common_locations:
        if os.path.exists(location) and \
           os.path.exists(os.path.join(location, 'src', 'model_checker')):
            return location
    
    # Couldn't find the project root
    return None


def get_available_theories() -> List[str]:
    """
    Get the list of available semantic theories.
    
    Returns:
        list: Names of available theories
    """
    try:
        from model_checker.theory_lib import AVAILABLE_THEORIES
        return AVAILABLE_THEORIES
    except ImportError:
        # Fallback: try to manually discover directories in theory_lib
        try:
            import model_checker
            theory_lib_path = os.path.join(os.path.dirname(model_checker.__file__), 'theory_lib')
            
            # Get all directories in theory_lib that aren't __pycache__ and have an __init__.py file
            theories = []
            for item in os.listdir(theory_lib_path):
                item_path = os.path.join(theory_lib_path, item)
                if os.path.isdir(item_path) and item != '__pycache__' and \
                   os.path.exists(os.path.join(item_path, '__init__.py')):
                    theories.append(item)
            
            # Make sure 'default' is included if available
            if 'default' in theories:
                # Move default to front of list
                theories.remove('default')
                theories.insert(0, 'default')
                
            return theories if theories else ["default"]
        except (ImportError, FileNotFoundError):
            return ["default"]  # Fallback to default theory


def manually_setup_paths(project_root: str) -> Dict[str, Any]:
    """
    Manually set up Python path for the ModelChecker project.
    
    Args:
        project_root: Path to the ModelChecker project root directory
        
    Returns:
        dict: Status and info about the setup
    """
    if not os.path.exists(project_root):
        return {
            "status": "error",
            "message": f"Project root does not exist: {project_root}"
        }
    
    if not os.path.exists(os.path.join(project_root, 'src', 'model_checker')):
        return {
            "status": "error",
            "message": f"Not a ModelChecker project root: {project_root}"
        }
    
    # Add paths to sys.path
    paths_to_add = [
        project_root,
        os.path.join(project_root, 'src'),
    ]
    
    for path in paths_to_add:
        if path not in sys.path:
            sys.path.insert(0, path)
    
    # Try importing model_checker
    try:
        if "model_checker" in sys.modules:
            importlib.reload(sys.modules["model_checker"])
        else:
            import model_checker
        
        return {
            "status": "success",
            "project_root": project_root,
            "model_checker_path": model_checker.__file__,
            "model_checker_version": getattr(model_checker, "__version__", "unknown")
        }
    except ImportError as e:
        return {
            "status": "error",
            "message": f"Could not import model_checker: {str(e)}",
            "project_root": project_root
        }


def get_diagnostic_info() -> Dict[str, Any]:
    """
    Get diagnostic information about the environment.
    
    Returns:
        dict: Diagnostic information
    """
    # Set up environment first
    env_info = setup_environment()
    
    diagnostic = {
        "environment": env_info,
        "python_version": sys.version,
        "sys_path": sys.path,
    }
    
    # Try to import key dependencies and get their versions
    dependencies = {
        "ipywidgets": "not found",
        "matplotlib": "not found",
        "networkx": "not found",
        "z3": "not found",
    }
    
    for dep_name in dependencies:
        try:
            dep = importlib.import_module(dep_name)
            dependencies[dep_name] = getattr(dep, "__version__", "unknown")
        except ImportError:
            pass
    
    diagnostic["dependencies"] = dependencies
    
    # Get details about model_checker if available
    try:
        import model_checker
        diagnostic["model_checker"] = {
            "path": model_checker.__file__,
            "version": getattr(model_checker, "__version__", "unknown"),
            "theories": get_available_theories(),
        }
    except ImportError:
        diagnostic["model_checker"] = "not found"
    
    return diagnostic