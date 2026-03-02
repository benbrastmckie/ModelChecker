"""Command line interface entry point for model checker."""

# Debug imports
import os
import sys
import inspect
import builtins  # Use the builtins module directly

def debug_imports():
    """Print debug information about which modules are being imported."""
    print("\n=== DEBUG: MODULE IMPORT PATHS ===")
    print(f"Current working directory: {os.getcwd()}")
    print(f"Python executable: {sys.executable}")
    print(f"Python path: {sys.path}")
    
    # Get the path of imported modules
    try:
        from model_checker.__main__ import main as main_func
        main_path = inspect.getfile(main_func)
        print(f"main() function imported from: {main_path}")
    except ImportError:
        print("Could not import main() from model_checker.__main__")
    
    try:
        import model_checker
        print(f"model_checker package imported from: {inspect.getfile(model_checker)}")
    except ImportError:
        print("Could not import model_checker package")
    
    try:
        from model_checker import builder
        print(f"builder module imported from: {inspect.getfile(builder)}")
    except ImportError:
        print("Could not import builder module")
    
    print("=================================\n")

# Run the debug function
debug_imports()

# Import main function directly
from model_checker.__main__ import main

# Create a custom main function that overrides any save_or_append behavior
def custom_main():
    """Wrapper for main that handles user input for saving."""
    # Store the original input function
    original_input = builtins.input
    
    def custom_input(prompt):
        result = original_input(prompt)
        # If this is the save prompt and user said no, don't return to main function
        if "save the output" in prompt and result.lower() in ['n', 'no']:
            print("Output not saved.")
            sys.exit(0)  # Exit before reaching the problematic code
        return result
    
    # Replace input function temporarily
    builtins.input = custom_input
    
    try:
        main()
    finally:
        # Restore original input function
        builtins.input = original_input

if __name__ == '__main__':
    custom_main()