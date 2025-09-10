# Plan 074: Runnable Notebook Generation

## Problem Statement

The current notebook generation creates notebooks with only data structure definitions, not runnable code. The generated notebooks are missing the actual calls to `create_build_example()` and output display logic that makes them executable and useful.

### Current Issues

1. **Non-runnable examples**: Generated notebooks only define data structures (`cf_cm_1 = [...]`) without actually running them
2. **Missing execution code**: No calls to `create_build_example()` to actually run the model checker
3. **No output handling**: No code to display results (countermodels or theorem validation messages)
4. **Incomplete template**: Template only includes data definition, not execution logic

### Reference Comparison

**Reference notebook** (`counterfactual_examples.ipynb`):
```python
# CF_CM_1: Test antecedent strengthening for would-counterfactuals
CF_CM_1_example = [
    ['\\neg A', '(A \\boxright C)'],
    ['((A \\wedge B) \\boxright C)'],
    {...}
]

print("Running model checker...")
model = create_build_example('CF_CM_1', cf_theory, CF_CM_1_example)

# Display the countermodel if found
if model.model_structure.z3_model:
    model.model_structure.print_to(
        model.settings,
        'CF_CM_1',
        'Would-Counterfactual Antecedent Strengthening',
        output=sys.stdout
    )
else:
    print("No countermodel found (unexpected - the argument should be invalid)")
```

**Currently generated**:
```python
# CF_CM_1: Test for Countermodel
cf_cm_1 = [
    ["\\neg A", "(A \\boxright C)"],
    ["((A \\wedge B) \\boxright C)"],
    {...}
]
# Nothing else - not runnable!
```

## Root Cause Analysis

The template was incorrectly simplified to remove ALL execution code instead of just removing pre-computed outputs. The notebook should include:
1. Example data definition
2. Model checker execution call
3. Conditional output display logic

## Solution Design

### Correct Template Structure

The template should generate notebooks with THREE parts per example:
1. **Header cell** (markdown): Example name and type
2. **Code cell**: Definition + execution + output handling
3. **Interpretation cell** (markdown): Placeholder for user notes

### Code Cell Template

```json
{
  "code_cell": {
    "cell_type": "code",
    "metadata": {},
    "source": [
      "# {{EXAMPLE_NAME}}: {{EXAMPLE_TYPE}}",
      "{{EXAMPLE_CODE}}",
      "",
      "print('Running model checker...')",
      "model = create_build_example('{{EXAMPLE_NAME}}', theory, {{EXAMPLE_VAR}})",
      "",
      "# Display the results",
      "if model.model_structure.z3_model:",
      "    model.model_structure.print_to(",
      "        model.settings,",
      "        '{{EXAMPLE_NAME}}',",
      "        theory['semantics'].__name__,",
      "        output=sys.stdout",
      "    )",
      "else:",
      "    print('=' * 70)",
      "    print('THEOREM VALIDATED: {{EXAMPLE_NAME}}')",
      "    print('=' * 70)",
      "    print('No countermodel found - the inference is VALID')",
      "    print('=' * 70)"
    ],
    "outputs": [],
    "execution_count": null
  }
}
```

### Key Differences from Current Implementation

1. **Include execution code**: Add the `create_build_example()` call
2. **Include output handling**: Add conditional logic for displaying results
3. **Maintain clean outputs**: Keep `outputs: []` so users run it themselves
4. **Proper variable naming**: Use consistent variable names (lowercase with underscores)

## Implementation Steps

### Step 1: Fix Template Files

Update all template.json files to include the complete runnable code pattern:

1. **Counterfactual template**: `theory_lib/logos/subtheories/counterfactual/notebooks/template.json`
2. **Modal template**: `theory_lib/logos/subtheories/modal/notebooks/template.json`
3. **Exclusion template**: `theory_lib/exclusion/notebooks/template.json`
4. **Imposition template**: `theory_lib/imposition/notebooks/template.json`

### Step 2: Verify Variable Substitution

Ensure the streaming generator properly substitutes:
- `{{EXAMPLE_NAME}}`: The example identifier (e.g., "CF_CM_1")
- `{{EXAMPLE_TYPE}}`: "Test for Countermodel" or "Test for Theorem"
- `{{EXAMPLE_CODE}}`: The formatted example definition
- `{{EXAMPLE_VAR}}`: The variable name (e.g., "cf_cm_1")

### Step 3: Test Output Quality

The generated notebooks should:
1. **Run without errors**: All cells execute successfully
2. **Display outputs**: Show countermodels or validation messages
3. **Match reference style**: Similar structure to handcrafted notebooks
4. **Be self-contained**: No external dependencies beyond imports

## Testing Plan

### Test Cases

1. **Counterfactual examples**: Generate and run CF_CM_1, CF_TH_5, etc.
2. **Mixed types**: Ensure both countermodel and theorem examples work
3. **Multiple examples**: Verify all examples in example_range are included
4. **Output verification**: Check that running cells produces expected output

### Validation Criteria

A generated notebook is considered correct if:
1. All code cells have valid Python syntax
2. Running the setup cell loads the theory successfully
3. Running example cells executes the model checker
4. Output is displayed (either countermodel or validation message)
5. No errors occur during execution

## Expected Output

### Example Generated Cell

```python
# CF_CM_1: Test for Countermodel
cf_cm_1 = [
    ["\\neg A", "(A \\boxright C)"],
    ["((A \\wedge B) \\boxright C)"],
    {
        'N': 4,
        'contingent': True,
        'non_null': True,
        'non_empty': True,
        'disjoint': False,
        'max_time': 10,
        'iterate': 2,
        'expectation': True,
    }
]

print('Running model checker...')
model = create_build_example('CF_CM_1', theory, cf_cm_1)

# Display the results
if model.model_structure.z3_model:
    model.model_structure.print_to(
        model.settings,
        'CF_CM_1',
        theory['semantics'].__name__,
        output=sys.stdout
    )
else:
    print('=' * 70)
    print('THEOREM VALIDATED: CF_CM_1')
    print('=' * 70)
    print('No countermodel found - the inference is VALID')
    print('=' * 70)
```

When executed, this cell would:
1. Define the example data structure
2. Run the model checker
3. Display the countermodel or validation message

## Benefits

1. **Actually runnable**: Users can execute cells to see results
2. **Interactive exploration**: Users can modify examples and re-run
3. **Educational value**: Shows how to use the model checker API
4. **Consistent with reference**: Matches the style of handcrafted notebooks
5. **Self-documenting**: Code shows the complete workflow

## Migration Notes

This plan RESTORES the execution code that was incorrectly removed. The key insight is:
- **Keep**: Example definition + execution + output handling code
- **Remove**: Pre-computed output data in the outputs field
- **Result**: Clean notebooks that users run themselves to see results

## Success Metrics

1. Generated notebooks execute without errors
2. Output matches what CLI produces for same examples
3. Users can modify and re-run examples
4. Structure matches reference notebooks
5. All examples from example_range are included and runnable