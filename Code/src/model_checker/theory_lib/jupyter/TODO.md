# Jupyter Note Book Integration

Other relevant files to consult in the repository:

- `theory_lib/jupyter/README_jupyter.md` documents the current jupyter notebook integration
- `theory_lib/README.md` documents the API including details about syntax for the languages that the model-checker supports

## TODOs

- [ ] revise `theory_lib/jupyter/jupyter_demo.ipynb` as needed to get its cells to run, looking at the `exclusion/examples.py` module for inspiration
- [ ] test `jupyter_demo.ipynb`, confirming that all cells are up and running
- [ ] adapt `theory_lib/exclusion/notebooks/exclusion_demo.ipynb` to work with the current integration of Jupyter notebooks used in the model-checker as described in `theory_lib/jupyter/README_jupyter.md`
- [ ] test `exclusion_demo.ipynb` confirming that all cells are running

## Issues

> I'm having the problems in the following notebooks:

### Current problems to be solved in `jupyter_demo.ipynb`

Here is the sixth cell:

```
# Create an explorer with the default theory
explorer = InteractiveModelExplorer()

# Display the interactive UI
explorer.display()
```

I'm getting the following error upon running the cell:

```
---------------------------------------------------------------------------
TypeError                                 Traceback (most recent call last)
Cell In[6], line 2
      1 # Create an explorer with the default theory
----> 2 explorer = InteractiveModelExplorer()
      4 # Display the interactive UI
      5 explorer.display()

File ~/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/jupyter.py:327, in InteractiveModelExplorer.__init__(self, theory_name)
    325 self.theory_name = theory_name
    326 # Fix the TypeError by getting semantic theories first
--> 327 semantic_theories = get_semantic_theories()
    328 self.theory = get_theory(theory_name, semantic_theories)
    329 self.settings = {
    330     'N': 3,
    331     'max_time': 5,
   (...)
    335     'model': True  # Default to looking for a satisfying model
    336 }

TypeError: get_semantic_theories() missing 1 required positional argument: 'theory_name'
```

### Current problems to be solved in `exclusion_demo.ipynb`

Here is the seventh cell:

```
# Create settings dictionary with required keys to avoid missing key errors
settings = semantics.DEFAULT_EXAMPLE_SETTINGS.copy()  # Start with default settings

# Add default general settings if they don't exist
DEFAULT_GENERAL_SETTINGS = {
    "print_impossible": False,
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
    "expectation": True,  # Add this required key directly
}

# Update settings with general settings
for key in DEFAULT_GENERAL_SETTINGS:
    settings[key] = DEFAULT_GENERAL_SETTINGS[key]

# Define premises and conclusions using raw strings for proper backslash handling
premises2 = [r"(\exclude (P \uniwedge Q) \uniequiv (\exclude P \univee \exclude Q))"]
conclusions2 = []

# Create syntax, model constraints, and model structure
syntax2 = mc.syntactic.Syntax(premises2, conclusions2, operators)

# Create model constraints - make sure we're using the correct types
try:
    model_constraints2 = model.ModelConstraints(settings, syntax2, semantics, proposition_class)
    
    # Import ExclusionStructure class directly to avoid import issues
    from model_checker.theory_lib.exclusion.semantic import ExclusionStructure
    
    # Create model structure with the right type
    model_structure2 = ExclusionStructure(model_constraints2, settings)
    
    # Print the results
    model_structure2.print_all(settings, "DeMorgan's Identity", "Exclusion Semantics")
except Exception as e:
    print(f"Error: {e}")
    print(f"Model constraints type: {type(model_constraints2)}")
    print(f"Expected type: {model.ModelConstraints}")
    print(f"Are they equal? {type(model_constraints2) == model.ModelConstraints}")
    
    # Try alternative approach
    print("\nTrying alternative approach")
    from model_checker.theory_lib.exclusion.examples import exclusion_theory
    
    # Use the semantic_theory method to build
    model_builder = mc.BuildExample(None, exclusion_theory, [premises2, conclusions2, settings])
    model_builder.model_structure.print_all(settings, "DeMorgan's Identity", "Exclusion Semantics")
```

Here is the error that I'm getting:

```
Error: Expected model_constraints to be a ModelConstraints object, got <class 'model_checker.model.ModelConstraints'>. Make sure you're passing the correct model_constraints object.
Model constraints type: <class 'model_checker.model.ModelConstraints'>
Expected type: <class 'model_checker.model.ModelConstraints'>
Are they equal? True

Trying alternative approach
---------------------------------------------------------------------------
TypeError                                 Traceback (most recent call last)
Cell In[7], line 33
     32 # Create model structure with the right type
---> 33 model_structure2 = ExclusionStructure(model_constraints2, settings)
     35 # Print the results

File ~/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/exclusion/semantic.py:653, in ExclusionStructure.__init__(self, model_constraints, combined_settings)
    652 if not isinstance(model_constraints, model.ModelConstraints):
--> 653     raise TypeError(
    654         f"Expected model_constraints to be a ModelConstraints object, got {type(model_constraints)}. "
    655         "Make sure you're passing the correct model_constraints object."
    656     )
    658 super().__init__(model_constraints, combined_settings)

TypeError: Expected model_constraints to be a ModelConstraints object, got <class 'model_checker.model.ModelConstraints'>. Make sure you're passing the correct model_constraints object.

During handling of the above exception, another exception occurred:

AttributeError                            Traceback (most recent call last)
Cell In[7], line 48
     45 from model_checker.theory_lib.exclusion.examples import exclusion_theory
     47 # Use the semantic_theory method to build
---> 48 model_builder = mc.BuildExample(None, exclusion_theory, [premises2, conclusions2, settings])
     49 model_builder.model_structure.print_all(settings, "DeMorgan's Identity", "Exclusion Semantics")

File ~/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/builder.py:849, in BuildExample.__init__(self, build_module, semantic_theory, example_case)
    847 """Initialize model structure from module flags."""
    848 # Store from build_module
--> 849 self.module = build_module.module
    850 self.module_flags = build_module.module_flags
    852 # Unpack and store semantic_theory

AttributeError: 'NoneType' object has no attribute 'module'
```
