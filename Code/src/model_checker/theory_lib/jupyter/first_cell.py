"""
Helper module with code for the first cell in Jupyter notebooks.
This code helps set up the environment correctly in NixOS and other environments.
"""

def get_setup_code():
    """Returns the code to include in the first cell of a Jupyter notebook"""
    return """
# Set up the environment for the model_checker package
import sys
import os
import importlib

# Helper function to setup imports
def setup_model_checker_env():
    # Try to find the ModelChecker project root
    possible_roots = [
        # If notebook is in the repo structure
        os.path.abspath(os.path.join(os.getcwd(), "../../../../../")),
        os.path.abspath(os.path.join(os.getcwd(), "../../../../")),
        os.path.abspath(os.path.join(os.getcwd(), "../../../")),
        os.path.abspath(os.path.join(os.getcwd(), "../../")),
        # Common installation paths
        os.path.expanduser("~/Documents/Philosophy/Projects/ModelChecker/Code"),
        os.path.expanduser("~/ModelChecker/Code"),
    ]
    
    project_root = None
    for path in possible_roots:
        if os.path.isdir(path) and os.path.isdir(os.path.join(path, "src", "model_checker")):
            project_root = path
            break
    
    if project_root is None:
        print("Could not find ModelChecker project root. Please specify the path manually.")
        return False
    
    # Add project root and src directory to path
    paths_to_add = [project_root, os.path.join(project_root, "src")]
    for path in paths_to_add:
        if path not in sys.path:
            sys.path.insert(0, path)
    
    # Try importing model_checker
    try:
        # If already imported, reload to ensure we're using the correct version
        if "model_checker" in sys.modules:
            importlib.reload(sys.modules["model_checker"])
        else:
            import model_checker
        
        # Make sure jupyter module is properly imported
        if "model_checker.jupyter" in sys.modules:
            importlib.reload(sys.modules["model_checker.jupyter"])
        
        print(f"Imported model_checker from {sys.modules['model_checker'].__file__}")
        return True
    except ImportError as e:
        print(f"Error importing model_checker: {e}")
        return False

# Run the setup
setup_success = setup_model_checker_env()

# Diagnostic information
if setup_success:
    import model_checker
    print(f"ModelChecker version: {model_checker.__version__}")
    print(f"ModelChecker location: {model_checker.__file__}")
    
    # Check if jupyter module is available
    try:
        from model_checker.jupyter import diagnostic_info
        info = diagnostic_info()
        print(f"Jupyter module location: {info['jupyter_module_location']}")
        print("ModelChecker Jupyter integration is ready to use")
    except ImportError:
        print("Jupyter module not available. You may need to install ipywidgets, matplotlib, and networkx.")
else:
    print("Failed to set up ModelChecker environment")
"""