# Jupyter Note Book Integration

Other relevant files to consult in the repository:

- `theory_lib/jupyter/README_jupyter.md` documents the current jupyter notebook integration
- `theory_lib/README.md`
- `model_checker/README.md`

## TODOs

- [ ] adapt `theory_lib/exclusion/notebooks/exclusion_demo.ipynb` to work with the current integration of Jupyter notebooks used in the model-checker as described in `theory_lib/jupyter/README_jupyter.md`
- [ ] test `exclusion_demo.ipynb` confirming that all cells are running

### Current problems to be solved in `exclusion_demo.ipynb`

### Complete Fix for `exclusion_demo.ipynb`

A more comprehensive solution would be to rewrite the notebook to use the `check_formula` and `InteractiveModelExplorer` functions from the new jupyter integration instead of constructing the model components manually:

```python
from model_checker.jupyter import check_formula

# Define formula using the proper syntax
formula = r"(\exclude (P \uniwedge Q) \uniequiv (\exclude P \univee \exclude Q))"

# Check the formula using the exclusion theory
result = check_formula(
    formula, 
    theory_name="exclusion", 
    settings={
        "N": 3,
        "max_time": 5,
        "contingent": True,
        "non_empty": True,
        "print_constraints": False
    }
)

# Display the result
display(result)
```

### Implementation Plan

1. **jupyter_demo.ipynb Fix**:
   - Update the `jupyter.py` file with the modified `__init__` method for `InteractiveModelExplorer`
   - Fix the `_get_available_theories` method to handle the API change
   - Fix the `_on_theory_change` method to use the theory_name parameter

2. **exclusion_demo.ipynb Fix**:
   - Create a new version of the notebook that uses the standardized jupyter integration
   - Use the `check_formula` and `InteractiveModelExplorer` classes instead of manual model construction
   - Create helper methods for common exclusion-specific operations
   - Add improved error handling and diagnostics

3. **Documentation Updates**:
   - Update the README_jupyter.md file with examples specific to the exclusion theory
   - Add notes about common issues and their solutions
   - Document the API changes in get_semantic_theories()

4. **Additional Testing**:
   - Create a test script to verify all notebook cells execute without errors
   - Test with different theories to ensure interoperability
   - Verify unicode and LaTeX operator handling works correctly

By implementing these changes, we should be able to get both notebooks working correctly with the current ModelChecker codebase.

