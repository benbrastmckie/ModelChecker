# Debugging ModelChecker Jupyter Integration

This guide provides a systematic workflow for testing and debugging ModelChecker's Jupyter integration. It is designed for both users encountering issues and developers extending the integration.

## Table of Contents

1. [Debugging Workflow Overview](#debugging-workflow-overview)
2. [Step 1: Environment Setup](#step-1-environment-setup)
3. [Step 2: Dependency Verification](#step-2-dependency-verification)
4. [Step 3: Import Testing](#step-3-import-testing)
5. [Step 4: Component Testing](#step-4-component-testing)
6. [Step 5: Theory Testing](#step-5-theory-testing)
7. [Step 6: Interactive Widget Testing](#step-6-interactive-widget-testing)
8. [Debugging Specific Issues](#debugging-specific-issues)
9. [Debug Tools Reference](#debug-tools-reference)
10. [Advanced Debugging Techniques](#advanced-debugging-techniques)

## Debugging Workflow Overview

The ModelChecker Jupyter integration has several components that need to work together:

1. **Environment**: Python paths must include the ModelChecker package
2. **Dependencies**: Required packages (ipywidgets, matplotlib, networkx) must be installed
3. **Core Integration**: The jupyter module must import correctly
4. **Theories**: The specific theories being used must be available
5. **Widgets**: For interactive components, the widget system must function properly

This guide will help you systematically test each component to identify and fix issues.

## Step 1: Environment Setup

First, verify your environment is correctly set up:

1. **Create a diagnostic notebook**:
   - Create a new Jupyter notebook in your ModelChecker/Code directory
   - Name it "modelchecker_diagnostic.ipynb"

2. **Add this environment check cell**:

```python
import os
import sys
import importlib

print(f"Current directory: {os.getcwd()}")
print(f"Python version: {sys.version}")

# Create a function to check paths
def check_modelchecker_path():
    # Look for ModelChecker in various common locations
    possible_roots = [
        os.getcwd(),  # Current directory
        os.path.dirname(os.getcwd()),  # Parent directory
        os.path.expanduser("~/Documents/Philosophy/Projects/ModelChecker/Code"),  # Common installation path
        os.path.expanduser("~/ModelChecker/Code"),  # Another common path
    ]
    
    found_paths = []
    for root in possible_roots:
        mc_path = os.path.join(root, "src", "model_checker")
        if os.path.exists(mc_path):
            found_paths.append((root, mc_path))
    
    return found_paths

# Check paths
found_paths = check_modelchecker_path()
print("\nPotential ModelChecker paths found:")
for root, mc_path in found_paths:
    print(f"- Project root: {root}")
    print(f"  Module path: {mc_path}")

# Check if ModelChecker is in sys.path
modelchecker_in_path = False
for path in sys.path:
    if os.path.exists(os.path.join(path, "model_checker")) or os.path.exists(os.path.join(path, "src", "model_checker")):
        modelchecker_in_path = True
        print(f"\nModelChecker found in Python path: {path}")

if not modelchecker_in_path:
    print("\nModelChecker NOT found in Python path!")
    
    # If we found paths, suggest adding them
    if found_paths:
        print("\nSuggested fix: Add these paths to sys.path:")
        for root, _ in found_paths:
            print(f"sys.path.insert(0, '{root}')")
            print(f"sys.path.insert(0, '{os.path.join(root, 'src')}')")
        
        # Automatic fix
        fix_choice = input("Would you like to automatically add the first found path to sys.path? (y/n): ")
        if fix_choice.lower() == 'y':
            root = found_paths[0][0]
            sys.path.insert(0, root)
            sys.path.insert(0, os.path.join(root, "src"))
            print(f"Added {root} and {os.path.join(root, 'src')} to sys.path")
```

3. **Review the output** to see if ModelChecker is properly in your Python path

4. **If needed, add paths manually**:

```python
# Add paths manually - adjust these paths to your setup
import sys
import os

project_root = "/path/to/ModelChecker/Code"  # Update this path
sys.path.insert(0, project_root)
sys.path.insert(0, os.path.join(project_root, "src"))

print("Paths added successfully.")
```

## Step 2: Dependency Verification

Verify all required dependencies are installed:

```python
def check_dependencies():
    dependencies = {
        "ipywidgets": "Interactive widgets",
        "matplotlib": "Visualization",
        "networkx": "Graph visualization",
        "z3": "SMT solver (core requirement)"
    }
    
    results = {}
    for dep, description in dependencies.items():
        try:
            module = importlib.import_module(dep)
            version = getattr(module, "__version__", "unknown")
            results[dep] = {"status": "installed", "version": version}
        except ImportError:
            results[dep] = {"status": "missing", "description": description}
    
    return results

# Check dependencies
dep_results = check_dependencies()

print("Dependency Status:")
print("-----------------")
for dep, info in dep_results.items():
    if info["status"] == "installed":
        print(f"✓ {dep}: v{info['version']}")
    else:
        print(f"✗ {dep}: MISSING - {info['description']}")
        print(f"  Install with: pip install {dep}")

# Check if any required dependencies are missing
missing_deps = [dep for dep, info in dep_results.items() if info["status"] == "missing"]
if missing_deps:
    print("\n⚠️ Missing required dependencies. Install them with:")
    for dep in missing_deps:
        print(f"pip install {dep}")
```

## Step 3: Import Testing

Test importing ModelChecker and its Jupyter integration:

```python
def test_imports():
    import_tests = [
        ("model_checker", "Main package"),
        ("model_checker.jupyter", "Jupyter integration"),
        ("model_checker.jupyter.environment", "Environment module"),
        ("model_checker.jupyter.unicode", "Operator handling"),
        ("model_checker.jupyter.display", "Visualization"),
        ("model_checker.jupyter.interactive", "Interactive UI"),
        ("model_checker.jupyter.adapters", "Theory adapters"),
        ("model_checker.jupyter.utils", "Utilities")
    ]
    
    results = {}
    for module, description in import_tests:
        try:
            # Try to reload if already imported
            if module in sys.modules:
                importlib.reload(sys.modules[module])
                mod = sys.modules[module]
            else:
                mod = importlib.import_module(module)
                
            # Get location and version if available
            location = getattr(mod, "__file__", "unknown location")
            version = getattr(mod, "__version__", "unknown")
            
            results[module] = {
                "status": "success", 
                "location": location,
                "version": version if module == "model_checker" else None
            }
        except Exception as e:
            results[module] = {"status": "error", "error": str(e), "description": description}
    
    return results

# Test imports
import_results = test_imports()

print("Import Test Results:")
print("-------------------")
for module, info in import_results.items():
    if info["status"] == "success":
        version_info = f" (v{info['version']})" if info["version"] else ""
        print(f"✓ {module}{version_info}")
        print(f"  Location: {info['location']}")
    else:
        print(f"✗ {module} - {info['description']}")
        print(f"  Error: {info['error']}")

# Check if any imports failed
failed_imports = [module for module, info in import_results.items() if info["status"] == "error"]
if failed_imports:
    print("\n⚠️ Some imports failed. This needs to be fixed before proceeding.")
else:
    print("\n✅ All imports successful!")
```

## Step 4: Component Testing

Test the core components of the ModelChecker Jupyter integration:

```python
def test_environment_module():
    print("Testing environment module...")
    try:
        from model_checker.jupyter.environment import setup_environment, get_diagnostic_info
        
        # Test environment setup
        env_result = setup_environment()
        print(f"Environment setup result: {env_result.get('status', 'unknown')}")
        
        # Test diagnostic info
        diag_info = get_diagnostic_info()
        print(f"Diagnostic info retrieved successfully")
        
        return True
    except Exception as e:
        print(f"Error testing environment module: {e}")
        import traceback
        traceback.print_exc()
        return False

def test_operators_module():
    print("\nTesting operators module...")
    try:
        from model_checker.jupyter.unicode import unicode_to_latex, latex_to_unicode
        
        # Test Unicode conversion
        unicode_formula = "p → q ∧ □r"
        latex = unicode_to_latex(unicode_formula)
        back_to_unicode = latex_to_unicode(latex)
        
        print(f"Unicode conversion: '{unicode_formula}' → '{latex}' → '{back_to_unicode}'")
        
        return True
    except Exception as e:
        print(f"Error testing operators module: {e}")
        import traceback
        traceback.print_exc()
        return False

def test_display_module():
    print("\nTesting display module...")
    try:
        from model_checker.jupyter.display import convert_ansi_to_html
        
        # Test ANSI conversion
        ansi_text = "\033[31mRed text\033[0m \033[32mGreen text\033[0m"
        html = convert_ansi_to_html(ansi_text)
        
        print(f"ANSI conversion successful")
        
        return True
    except Exception as e:
        print(f"Error testing display module: {e}")
        import traceback
        traceback.print_exc()
        return False

def test_utils_module():
    print("\nTesting utils module...")
    try:
        from model_checker.jupyter.utils import load_examples, get_example_categories
        
        # Test example loading for default theory
        examples = load_examples("default")
        
        if examples:
            print(f"Successfully loaded {len(examples)} examples from default theory")
            
            # Test categorization
            categories = get_example_categories(examples)
            print(f"Examples categorized into {len(categories)} categories")
        else:
            print("No examples found for default theory")
        
        return True
    except Exception as e:
        print(f"Error testing utils module: {e}")
        import traceback
        traceback.print_exc()
        return False

# Run component tests
print("Running component tests...")
env_test = test_environment_module()
operators_test = test_operators_module()
display_test = test_display_module()
utils_test = test_utils_module()

# Summary
print("\nComponent Test Summary:")
print(f"Environment module: {'✓ PASS' if env_test else '✗ FAIL'}")
print(f"Operators module: {'✓ PASS' if operators_test else '✗ FAIL'}")
print(f"Display module: {'✓ PASS' if display_test else '✗ FAIL'}")
print(f"Utils module: {'✓ PASS' if utils_test else '✗ FAIL'}")
```

## Step 5: Theory Testing

Test the available theories and their integration:

```python
def test_theories():
    print("Testing theory availability...")
    try:
        from model_checker.jupyter.environment import get_available_theories
        from model_checker import get_theory
        
        # Get list of available theories
        theories = get_available_theories()
        print(f"Available theories: {theories}")
        
        # Try loading each theory
        results = {}
        for theory_name in theories:
            try:
                theory = get_theory(theory_name)
                results[theory_name] = {"status": "success", "theory": theory}
                print(f"✓ Successfully loaded theory: {theory_name}")
            except Exception as e:
                results[theory_name] = {"status": "error", "error": str(e)}
                print(f"✗ Error loading theory {theory_name}: {e}")
        
        # Try to check a simple formula with each working theory
        from model_checker import check_formula
        for theory_name, info in results.items():
            if info["status"] == "success":
                try:
                    result = check_formula("p → p", theory_name=theory_name)
                    print(f"✓ Successfully checked formula with theory: {theory_name}")
                except Exception as e:
                    print(f"✗ Error checking formula with theory {theory_name}: {e}")
        
        return results
    except Exception as e:
        print(f"Error testing theories: {e}")
        import traceback
        traceback.print_exc()
        return {}

# Test theories
theory_results = test_theories()

# Summary
print("\nTheory Test Summary:")
print("-------------------")
success_count = sum(1 for info in theory_results.values() if info["status"] == "success")
print(f"Loaded {success_count} out of {len(theory_results)} theories successfully")

if success_count < len(theory_results):
    print("\nTheories with errors:")
    for theory_name, info in theory_results.items():
        if info["status"] == "error":
            print(f"- {theory_name}: {info['error']}")
```

## Step 6: Interactive Widget Testing

Test the interactive UI components:

```python
def test_widgets():
    print("Testing interactive widgets...")
    try:
        import ipywidgets
        from IPython.display import display
        
        # Create a simple button to test widget rendering
        button = ipywidgets.Button(
            description='Test Widget',
            button_style='info'
        )
        
        print("Displaying test button. If you can see and click it, widgets are working.")
        display(button)
        
        # Try creating a ModelExplorer
        print("\nTesting ModelExplorer creation...")
        try:
            from model_checker import ModelExplorer
            explorer = ModelExplorer()
            print("✓ Successfully created ModelExplorer")
            
            print("Displaying ModelExplorer. If you can see the UI, it's working correctly.")
            display(explorer.ui)
            return True
        except Exception as e:
            print(f"✗ Error creating ModelExplorer: {e}")
            import traceback
            traceback.print_exc()
            return False
    except Exception as e:
        print(f"Error testing widgets: {e}")
        import traceback
        traceback.print_exc()
        return False

# Test interactive widgets
widget_test = test_widgets()

# Summary
print("\nWidget Test Summary:")
print(f"Interactive widgets: {'✓ PASS' if widget_test else '✗ FAIL'}")
```

## Debugging Specific Issues

### Formula Checking Issues

If you're having problems with formula checking, use this test:

```python
def test_formula_checking():
    print("Testing formula checking...")
    try:
        from model_checker import check_formula
        
        test_formulas = [
            # Simple propositional formulas
            "p",
            "p → q",
            "(p ∧ q) → p",
            
            # Modal formulas
            "□p → p",
            "◇p → □◇p",
            
            # With premises
            ("q", ["p", "p → q"]),
        ]
        
        for formula in test_formulas:
            try:
                if isinstance(formula, tuple):
                    # Formula with premises
                    formula_str, premises = formula
                    print(f"Testing: {formula_str} with premises {premises}...")
                    result = check_formula(formula_str, premises=premises)
                else:
                    # Simple formula
                    print(f"Testing: {formula}...")
                    result = check_formula(formula)
                print(f"✓ Successfully checked formula: {formula}")
            except Exception as e:
                print(f"✗ Error checking formula {formula}: {e}")
                import traceback
                traceback.print_exc()
        
        return True
    except Exception as e:
        print(f"Error in formula checking test: {e}")
        import traceback
        traceback.print_exc()
        return False

# Test formula checking
formula_test = test_formula_checking()

# Summary
print("\nFormula Checking Test Summary:")
print(f"Formula checking: {'✓ PASS' if formula_test else '✗ FAIL'}")
```

### Theory Import Issues

If you're having problems with specific theories, use this detailed test:

```python
def test_theory_imports():
    print("Testing theory imports in detail...")
    theory_modules = {
        "default": ["model_checker.theory_lib.default", "Default theory (hyperintensional)"],
        "exclusion": ["model_checker.theory_lib.exclusion", "Exclusion theory"],
        "imposition": ["model_checker.theory_lib.imposition", "Imposition theory"],
        "bimodal": ["model_checker.theory_lib.bimodal", "Bimodal theory"]
    }
    
    results = {}
    for theory_name, (module_path, description) in theory_modules.items():
        print(f"\nTesting {theory_name} theory ({description}):")
        
        # Test main module import
        try:
            theory_module = importlib.import_module(module_path)
            print(f"✓ Successfully imported {module_path}")
            
            # Check for key components
            components = {}
            
            # Check for semantic.py components
            semantic_module = f"{module_path}.semantic"
            try:
                semantics = importlib.import_module(semantic_module)
                components["semantic"] = "success"
                print(f"✓ Successfully imported {semantic_module}")
            except ImportError as e:
                components["semantic"] = f"error: {str(e)}"
                print(f"✗ Error importing {semantic_module}: {e}")
            
            # Check for operators.py components
            operators_module = f"{module_path}.operators"
            try:
                operators = importlib.import_module(operators_module)
                components["operators"] = "success"
                print(f"✓ Successfully imported {operators_module}")
            except ImportError as e:
                components["operators"] = f"error: {str(e)}"
                print(f"✗ Error importing {operators_module}: {e}")
            
            # Check for examples.py
            examples_module = f"{module_path}.examples"
            try:
                examples = importlib.import_module(examples_module)
                components["examples"] = "success"
                print(f"✓ Successfully imported {examples_module}")
            except ImportError as e:
                components["examples"] = f"error: {str(e)}"
                print(f"✗ Error importing {examples_module}: {e}")
            
            results[theory_name] = {
                "status": "success", 
                "components": components
            }
        except ImportError as e:
            print(f"✗ Error importing {module_path}: {e}")
            results[theory_name] = {
                "status": "error", 
                "error": str(e)
            }
    
    return results

# Test theory imports
theory_import_results = test_theory_imports()

# Summary
print("\nTheory Import Test Summary:")
print("-------------------------")
for theory_name, info in theory_import_results.items():
    if info["status"] == "success":
        components = info["components"]
        all_success = all(status == "success" for status in components.values())
        status_symbol = "✓" if all_success else "⚠️"
        print(f"{status_symbol} {theory_name}")
        
        # Print component details if there are issues
        if not all_success:
            for component, status in components.items():
                if status != "success":
                    print(f"  - {component}: {status}")
    else:
        print(f"✗ {theory_name}: {info['error']}")
```

## Debug Tools Reference

Here are some useful tools for debugging that are built into the ModelChecker Jupyter integration:

### 1. Get Diagnostic Information

```python
from model_checker.jupyter.environment import get_diagnostic_info

diag_info = get_diagnostic_info()
print(diag_info)
```

### 2. Setup Environment

```python
from model_checker.jupyter.environment import setup_environment

env_info = setup_environment()
print(env_info)
```

### 3. Running the Debug Script

ModelChecker includes a debug script that can be run from the command line:

```bash
cd /path/to/ModelChecker/Code
python debug_notebook.py
```

Or you can copy this script and run it in a notebook cell:

```python
def run_debug_tests():
    import os
    import sys
    import importlib
    import traceback
    
    print("ModelChecker Jupyter Integration Debug Tests")
    print("===========================================")
    
    # Check environment
    print("\n1. Environment Check")
    print("-------------------")
    print(f"Python version: {sys.version}")
    print(f"Current directory: {os.getcwd()}")
    
    # Add paths if needed
    current_dir = os.getcwd()
    if os.path.exists(os.path.join(current_dir, 'src', 'model_checker')):
        project_root = current_dir
    else:
        project_root = None
        # Try common locations
        common_paths = [
            os.path.expanduser("~/Documents/Philosophy/Projects/ModelChecker/Code"),
            os.path.expanduser("~/ModelChecker/Code")
        ]
        for path in common_paths:
            if os.path.exists(os.path.join(path, 'src', 'model_checker')):
                project_root = path
                break
    
    if project_root:
        print(f"Found ModelChecker at: {project_root}")
        # Add to path if needed
        if project_root not in sys.path:
            sys.path.insert(0, project_root)
            print(f"Added to path: {project_root}")
        src_path = os.path.join(project_root, 'src')
        if src_path not in sys.path:
            sys.path.insert(0, src_path)
            print(f"Added to path: {src_path}")
    else:
        print("Could not find ModelChecker. Try specifying the path manually.")
    
    # Check imports
    print("\n2. Import Check")
    print("--------------")
    tests = [
        ("model_checker", "Core package"),
        ("model_checker.jupyter", "Jupyter integration"),
        ("model_checker.jupyter.environment", "Environment module"),
        ("ipywidgets", "Interactive widgets"),
        ("matplotlib", "Visualization"),
        ("networkx", "Graph visualization")
    ]
    
    for module, description in tests:
        try:
            if module in sys.modules:
                importlib.reload(sys.modules[module])
            mod = importlib.import_module(module)
            location = getattr(mod, "__file__", "unknown location")
            version = getattr(mod, "__version__", "unknown")
            print(f"✓ {module}: {location} (version: {version})")
        except ImportError as e:
            print(f"✗ {module} ({description}): {e}")
    
    # Check functions
    print("\n3. Function Check")
    print("---------------")
    functions = [
        ("check_formula", "from model_checker import check_formula"),
        ("ModelExplorer", "from model_checker import ModelExplorer"),
        ("setup_environment", "from model_checker.jupyter.environment import setup_environment"),
        ("unicode_to_latex", "from model_checker.jupyter.unicode import unicode_to_latex")
    ]
    
    for func_name, import_stmt in functions:
        try:
            exec(import_stmt)
            func = eval(func_name)
            print(f"✓ {func_name}: {func}")
        except Exception as e:
            print(f"✗ {func_name}: {e}")
    
    # Summary
    print("\nDebug Test Complete")
    print("=================")
    print("If you're seeing errors, check the troubleshooting guide:")
    print("- /path/to/ModelChecker/Code/src/model_checker/jupyter/TROUBLESHOOTING.md")

# Run the debug tests
run_debug_tests()
```

## Advanced Debugging Techniques

### Testing with Custom Theories

If you're developing a custom theory and want to debug its Jupyter integration:

```python
def test_custom_theory(theory_name):
    """Test a custom theory with the Jupyter integration."""
    print(f"Testing custom theory: {theory_name}")
    
    try:
        # Try importing the theory
        theory_module = importlib.import_module(f"model_checker.theory_lib.{theory_name}")
        print(f"✓ Successfully imported theory module")
        
        # Try getting the theory
        from model_checker import get_theory
        theory = get_theory(theory_name)
        print(f"✓ Successfully got theory via get_theory()")
        
        # Test basic formula checking
        from model_checker import check_formula
        result = check_formula("p → p", theory_name=theory_name)
        print(f"✓ Successfully checked formula with theory")
        
        # Test loading examples
        from model_checker.jupyter.utils import load_examples
        examples = load_examples(theory_name)
        if examples:
            print(f"✓ Successfully loaded {len(examples)} examples")
        else:
            print("No examples found for this theory")
        
        return True
    except Exception as e:
        print(f"✗ Error testing custom theory: {e}")
        traceback.print_exc()
        return False

# Replace "my_theory" with your custom theory name
test_custom_theory("my_theory")  
```

### Monkey Patching for Debugging

If you need to debug a specific function without modifying the source:

```python
def debug_wrapper(original_function, name="function"):
    """Wrap a function with debugging output."""
    def wrapper(*args, **kwargs):
        print(f"Calling {name} with args: {args}, kwargs: {kwargs}")
        try:
            result = original_function(*args, **kwargs)
            print(f"{name} returned successfully")
            return result
        except Exception as e:
            print(f"Error in {name}: {e}")
            traceback.print_exc()
            raise
    return wrapper

# Example: Debug check_formula
from model_checker import check_formula
original_check_formula = check_formula
model_checker.check_formula = debug_wrapper(check_formula, "check_formula")

# Now use it normally
check_formula("p → q")  # Will print debugging info

# Restore the original when done
model_checker.check_formula = original_check_formula
```

### Creating a Test Suite

For ongoing development, you can create a comprehensive test suite:

```python
def run_integration_test_suite():
    """Run a complete test suite for the Jupyter integration."""
    # Define the tests to run
    tests = [
        ("Environment Setup", test_environment_module),
        ("Operator Handling", test_operators_module),
        ("Display Functions", test_display_module),
        ("Utility Functions", test_utils_module),
        ("Theory Availability", lambda: bool(test_theories())),
        ("Formula Checking", test_formula_checking),
        ("Widget Integration", test_widgets)
    ]
    
    # Run each test and collect results
    results = {}
    for name, test_func in tests:
        print(f"\nRunning test: {name}")
        print("-" * (len(name) + 13))
        try:
            result = test_func()
            results[name] = result
        except Exception as e:
            print(f"Error running test {name}: {e}")
            traceback.print_exc()
            results[name] = False
    
    # Print summary
    print("\nTest Suite Summary")
    print("=================")
    for name, result in results.items():
        status = "PASS" if result else "FAIL"
        symbol = "✓" if result else "✗"
        print(f"{symbol} {name}: {status}")
    
    # Overall result
    success_rate = sum(1 for r in results.values() if r) / len(results) * 100
    print(f"\nOverall success rate: {success_rate:.1f}%")
    
    if success_rate < 100:
        print("\nFailing tests:")
        for name, result in results.items():
            if not result:
                print(f"- {name}")
    
    return results

# Run the full test suite
test_results = run_integration_test_suite()
```

## Conclusion

By following this systematic debugging workflow, you can identify and fix issues in the ModelChecker Jupyter integration. Start with the environment setup, then move through dependency verification, import testing, and component testing to pinpoint problems.

For specific issues, use the targeted tests in the "Debugging Specific Issues" section. The debug tools in the "Debug Tools Reference" section provide additional utilities for troubleshooting.

If you're developing custom extensions or theories, the "Advanced Debugging Techniques" section offers tools for more complex debugging scenarios.

For further assistance, refer to the [TROUBLESHOOTING.md](TROUBLESHOOTING.md) guide or the [NixOS_jupyter.md](NixOS_jupyter.md) guide for NixOS-specific issues.

## Included Debugging Tools

The ModelChecker repository includes several debugging tools in the `Code/debug/` directory:

1. **jupyter_test.py**: A diagnostic script that checks your environment and ModelChecker installation
   ```bash
   cd /path/to/ModelChecker/Code
   python debug/jupyter_test.py
   ```

2. **debug_notebook.py**: A script that tests specific components of the Jupyter integration
   ```bash
   cd /path/to/ModelChecker/Code
   python debug/debug_notebook.py
   ```

3. **simple_test.ipynb**: A minimal Jupyter notebook for isolating issues
   ```bash
   cd /path/to/ModelChecker/Code
   jupyter notebook debug/simple_test.ipynb
   ```

4. **demo_notebook_fixed.ipynb**: A robust version of the demo notebook with enhanced error handling
   ```bash
   cd /path/to/ModelChecker/Code
   jupyter notebook debug/demo_notebook_fixed.ipynb
   ```

These tools can help you diagnose specific issues with your environment or installation.
