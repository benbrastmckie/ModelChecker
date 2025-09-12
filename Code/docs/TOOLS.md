# ModelChecker Tools Guide

[← Back to Technical Docs](README.md) | [Development →](DEVELOPMENT.md) | [Tests →](TESTS.md)

## Overview

This guide explains advanced features of the ModelChecker for exploring logical theories, finding multiple models, and comparing different semantic frameworks. These tools are essential for researchers and developers working with complex logical theories and requiring detailed model analysis.

## Table of Contents

1. [Using the Iterate Setting](#using-the-iterate-setting)
2. [Comparing Multiple Theories](#comparing-multiple-theories)
3. [Using the Maximize Flag](#using-the-maximize-flag)
4. [Debugging and Output Flags](#debugging-and-output-flags)

---

## Using the Iterate Setting

The `iterate` setting allows you to find multiple semantically distinct models for a logical formula. This is useful for exploring the full space of possible models and understanding how different interpretations can satisfy the same logical constraints.

### Basic Usage

In any theory's example file, add the `iterate` setting to request multiple models:

```python
# Example from logos theory
LOGOS_CM_1_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'max_time': 5,
    'iterate': 3,        # Find up to 3 distinct models
    'expectation': True,
}
```

### How It Works

When `iterate` is set to a value greater than 1:

1. The system finds the first model normally
2. For each additional model, it:
   - Adds constraints ensuring the new model differs from previous ones
   - Searches for a structurally distinct solution
   - Displays differences between consecutive models

### Example Output

```bash
MODEL 1/3
========================================
EXAMPLE LOGOS_CM_1: there is a countermodel.
[First model details...]

Finding 3 models: [████████████████████] 2/3 (checked 4) 0.8s

MODEL 2/3
=== DIFFERENCES FROM PREVIOUS MODEL ===
Verification Changes:
  w1 verifies A: True → False
  w2.s1 verifies B: False → True

State Changes:
  (w1, s2) exists: True → False

[Second model details...]

MODEL 3/3
=== DIFFERENCES FROM PREVIOUS MODEL ===
Part-of Changes:
  s1 ⊑ s3: True → False

Verification Changes:
  w2 verifies C: False → True

[Third model details...]

Found 3/3 distinct models.
```

### Theory-Specific Differences

Each theory defines what makes models "semantically distinct":

- **Logos Theory**: Different verification/falsification patterns, world structures, state configurations
- **Exclusion Theory**: Different exclusion relations between states, witness structures
- **Bimodal Theory**: Different temporal/modal accessibility relations
- **Imposition Theory**: Different imposition relations and counterfactual patterns

### Advanced Settings

You can fine-tune the iteration behavior:

```python
settings = {
    'iterate': 5,                    # Maximum models to find
    'max_invalid_attempts': 5,       # Max consecutive invalid models before stopping
    'iteration_attempts': 5,         # Max isomorphic models before adding stronger constraints
    'escape_attempts': 3,            # Max attempts to escape isomorphism loops
    'iteration_timeout': 1.0,        # Timeout for isomorphism check (seconds)
    'iteration_solver_timeout': 5.0, # Z3 solver timeout per iteration (seconds)
}
```

### Use Cases

- **Semantic Exploration**: Understand all possible ways a formula can be satisfied
- **Countermodel Analysis**: Find diverse counterexamples to invalid arguments
- **Theory Testing**: Verify that logical principles behave consistently across model variations
- **Educational**: Demonstrate the richness of non-classical semantic frameworks

---

## Comparing Multiple Theories

ModelChecker allows you to test the same logical formulas across different semantic theories. This is invaluable for understanding how different logical frameworks handle the same inferences.

### Setting Up Theory Comparison

In your `examples.py` file, define multiple theories in the `semantic_theories` dictionary:

```python
# Import the theories you want to compare
from model_checker.theory_lib.logos import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
    logos_registry
)
from model_checker.theory_lib.imposition import (
    ImpositionSemantics,
    Proposition as ImpositionProposition,
    ModelStructure as ImpositionModelStructure,
    imposition_operators
)

# No translation needed - both theories use the same operator names
# Both use \\boxright for must-counterfactual and \\diamondright for might-counterfactual

# Set up the theories for comparison
semantic_theories = {
    "Fine": {
        "semantics": ImpositionSemantics,
        "proposition": ImpositionProposition,
        "model": ImpositionModelStructure,
        "operators": imposition_operators,
        "dictionary": {}  # No translation needed
    },
    "Brast-McKie": {
        "semantics": LogosSemantics,
        "proposition": LogosProposition,
        "model": LogosModelStructure,
        "operators": logos_registry.get_operators(),
        "dictionary": {}  # No translation needed - same operator names
    }
}
```

### Understanding Translation Dictionaries

The `dictionary` parameter in `semantic_theories` enables automatic operator translation between theories. This is essential when different theories use different notation for the same logical concepts.

#### How Translation Works

When you define multiple theories for comparison, the ModelChecker uses translation dictionaries to convert formulas from one theory's notation to another:

```python
# Example: If theory A uses custom operators that need translation to theory B
theory_a_to_theory_b = {
    "\\myand": "\\wedge",       # Map theory A's conjunction to standard
    "\\myor": "\\vee",          # Map theory A's disjunction to standard  
    "\\mynot": "\\neg",         # Map theory A's negation to standard
    "\\mybox": "\\Box",         # Map theory A's necessity to standard
    "\\implies": "\\rightarrow",  # Map alternative implication symbol
    "\\mycount": "\\boxright",   # Map custom counterfactual to standard
}
```

The translation process:
1. Formulas are written using the first theory's operators
2. When testing with another theory, operators are automatically translated
3. Each theory evaluates the formula using its own semantics

#### Standard Theories: No Translation Required

The theories provided in ModelChecker (logos, exclusion, imposition, bimodal) all use standardized operator names, so **no translation is needed** when comparing them:

```python
# Example: Comparing exclusion and logos theories
exclusion_to_logos = {}  # Empty dictionary - both use same operators

# Example: Comparing imposition and logos theories  
imposition_to_logos = {}  # Empty dictionary - both use \\boxright, \\diamondright

semantic_theories = {
    "Exclusion": {
        "semantics": ExclusionSemantics,
        "proposition": ExclusionProposition,
        "model": ExclusionModelStructure,
        "operators": exclusion_operators,
        "dictionary": {}  # No translation needed
    },
    "Logos": {
        "semantics": LogosSemantics,
        "proposition": LogosProposition,
        "model": LogosModelStructure,
        "operators": logos_registry.get_operators(),
        "dictionary": {}  # No translation needed
    }
}
```

#### When You Need Translation

Translation dictionaries are only necessary when:
1. Implementing a custom theory with non-standard operators
2. Comparing with legacy code using different notation
3. Adapting formulas from published papers using different symbols

For all standard ModelChecker theories, you can safely use empty dictionaries.

### Example: Imposition and Logos Comparison

The imposition theory (Kit Fine's truthmaker semantics) and logos theory (Brast-McKie's hyperintensional semantics) are designed for comparison:

```python
# Define an example testing counterfactual logic
IM_CM_1_premises = ['\\neg A', '(A \\boxright C)']
IM_CM_1_conclusions = ['((A \\wedge B) \\boxright C)']
IM_CM_1_settings = {
    'N': 4,
    'contingent': True,
    'non_null': True,
    'max_time': 5,
    'iterate': 2,
}
IM_CM_1_example = [
    IM_CM_1_premises,
    IM_CM_1_conclusions,
    IM_CM_1_settings,
]

example_range = {
    "antecedent_strengthening" : IM_CM_1_example,
}
```

When run, this will:

1. Test the imposition theory with `\boxright` operators
2. Translate to logos theory using `\boxright` operators
3. Show whether each theory finds a countermodel

### Running the Comparison

To execute the comparison:

```bash
# Simply run the example file with multiple theories defined
./dev_cli.py path/to/examples.py

# Or use the maximize flag for performance comparison
./dev_cli.py -m path/to/examples.py
```

### What to Expect

The output will show results for each theory:

- Whether a model/countermodel was found
- The model structure if one exists
- Any differences in how theories handle the same logical principle

---

## Using the Maximize Flag

The maximize flag (`-m` or `--maximize`) enables a special comparison mode that tests the scalability of different semantic theories.

### What It Does

Instead of finding a single model, maximize mode:

1. Starts with the initial N (number of worlds) specified in settings
2. If a model is found within the time limit, increments N and tries again
3. Continues until the solver times out
4. Reports the maximum N each theory could handle

### Usage

Command line:

```bash
./dev_cli.py -m examples_file.py
```

Or in the example file:

```python
general_settings = {
    "maximize": True,
}
```

### Example Output

```
========================================
EXAMPLE = antecedent_strengthening
  Premises:
    ¬A
    (A □→ C)
  Conclusions:
    ((A ∧ B) □→ C)

ImpositionSemantics (Fine):
  RUN TIME = 0.23, MAX TIME = 5, N = 4.
ImpositionSemantics (Fine):
  RUN TIME = 0.89, MAX TIME = 5, N = 5.
ImpositionSemantics (Fine):
  RUN TIME = 3.45, MAX TIME = 5, N = 6.
ImpositionSemantics (Fine): TIMED OUT
  RUN TIME = 5.01, MAX TIME = 5, N = 7.

LogosSemantics (Brast-McKie):
  RUN TIME = 0.18, MAX TIME = 5, N = 4.
LogosSemantics (Brast-McKie):
  RUN TIME = 0.52, MAX TIME = 5, N = 5.
LogosSemantics (Brast-McKie):
  RUN TIME = 1.89, MAX TIME = 5, N = 6.
LogosSemantics (Brast-McKie):
  RUN TIME = 4.21, MAX TIME = 5, N = 7.
LogosSemantics (Brast-McKie): TIMED OUT
  RUN TIME = 5.02, MAX TIME = 5, N = 8.

========================================
```

### Interpreting Results

The results show:

- **Maximum N**: The highest number of worlds each theory could handle
- **Performance**: Which theories scale better with complexity
- **Timeouts**: When each theory hits computational limits

In the example above:

- Fine's imposition theory handled up to N=6
- Brast-McKie's logos theory handled up to N=7
- This suggests logos may have better scalability for this example

### Use Cases

1. **Performance Benchmarking**: Compare computational efficiency of theories
2. **Theory Development**: Test if optimizations improve scalability
3. **Research**: Empirically study complexity of different semantic frameworks
4. **Debugging**: Identify when theories struggle with larger models

### Tips for Effective Use

- Set reasonable `max_time` values (5-10 seconds) for meaningful comparisons
- Start with small N values in your examples
- Use colored output to quickly identify successes (green) vs timeouts (red)
- Compare theories with similar expressive power for fair benchmarks

### Limitations

- Requires multiple theories to be defined in `semantic_theories`
- Results depend heavily on the specific example being tested
- Memory usage can be high for large N values
- Some theories may have inherently different complexity characteristics

---

## Best Practices

### For Iterate

- Start with small iterate values (2-3) to understand the model space
- Use larger values only when exploring specific semantic phenomena
- Monitor performance as iterate values increase

### For Theory Comparison

- Ensure operator translations are semantically appropriate
- Test theories on standard examples first
- Document any unexpected behavioral differences

### For Maximize Mode

- Use consistent time limits across comparisons
- Run multiple examples to get a comprehensive view
- Consider both worst-case and average-case performance

## Troubleshooting

### Common Issues

1. **"No more distinct models found"**: The logical constraints may only allow limited distinct models
2. **Translation errors**: Ensure all operators in formulas have mappings in the dictionary
3. **Timeout in maximize mode**: Normal behavior when reaching computational limits
4. **Memory errors**: Reduce N values or use fewer concurrent processes

### Getting Help

- Check theory-specific documentation in `theory_lib/*/docs/`
- Review example files in each theory directory
- Use the `-p` flag to see Z3 constraints for debugging

## Debugging and Output Flags

ModelChecker provides several command-line flags to help with debugging, understanding model internals, and saving output. These flags give you deeper insight into how the solver works and what constraints are being generated.

### Print Impossible States (-i)

The `-i` flag sets `print_impossible = True`, which displays impossible states in the model output.

**Usage:**

```bash
./dev_cli.py -i examples_file.py
```

**What It Shows:**

- States that cannot exist according to the semantic constraints
- Helps understand which world-state combinations are ruled out
- Useful for debugging unexpected model behavior

**Example Output:**

```
Impossible States:
- (w1, s2): State s2 cannot exist at world w1
- (w3, s1): Incompatible with verification constraints
```

**When to Use:**

- Debugging why certain expected states don't appear in models
- Understanding semantic constraints on state existence
- Verifying that impossibility constraints work correctly

### Print Z3 Constraints (-p)

The `-p` flag sets `print_constraints = True`, which displays the Z3 SMT solver constraints generated from your logical formulas.

**Usage:**

```bash
./dev_cli.py -p examples_file.py
```

**What It Shows:**

- The actual Z3 constraints generated from your premises and conclusions
- Variable declarations for worlds, states, and propositions
- Semantic constraints imposed by the theory
- If no model exists, shows the unsat core (minimal conflicting constraints)

**Example Output:**

```
Z3 CONSTRAINTS:
================
; Variable declarations
(declare-fun A_verifier () (_ BitVec 8))
(declare-fun B_verifier () (_ BitVec 8))

; Semantic constraints
(assert (= (bvand A_verifier B_verifier) #x00))

; Premise constraints
(assert (not (= A_verifier #x00)))

; Conclusion constraints (negated for countermodel)
(assert (= B_verifier #x00))
```

**When to Use:**

- Debugging why formulas don't produce expected models
- Understanding how logical operators translate to constraints
- Learning how the semantic theory works internally
- Identifying conflicting constraints when no model exists

### Print Z3 Model (-z)

The `-z` flag sets `print_z3 = True`, which displays the raw Z3 model or unsat core.

**Usage:**

```bash
./dev_cli.py -z examples_file.py
```

**What It Shows:**

- If a model exists: The complete Z3 variable assignments
- If no model exists: The unsat core showing conflicting constraints
- Raw bitvector values for all semantic variables

**Example Output (Model Found):**

```
Z3 MODEL:
=========
A_verifier = #b00000011
B_verifier = #b00001100
world_partial_order = [else -> #b11111111]
state_partial_order = [else -> #b00001111]
```

**Example Output (No Model):**

```
Z3 UNSAT CORE:
==============
The following constraints are mutually inconsistent:
1. (not (= A_verifier #x00))  ; A is non-empty
2. (= A_verifier B_verifier)   ; A equals B
3. (= B_verifier #x00)         ; B is empty
```

**When to Use:**

- Deep debugging of constraint satisfaction issues
- Understanding exact variable assignments in models
- Analyzing why certain formulas are unsatisfiable
- Verifying bitvector encodings work correctly

### Save Output (-s)

The `-s` flag sets `save_output = True`, which automatically saves all model output to structured files in a timestamped directory.

**Usage:**

```bash
# Basic save (batch mode)
./dev_cli.py -s examples_file.py

# Save with sequential output mode
./dev_cli.py -s --output-mode sequential examples_file.py

# Sequential mode with single file
./dev_cli.py -s --output-mode sequential --sequential-files single examples_file.py
```

**What It Does:**

1. Creates a timestamped output directory (e.g., `output_20240305_143022/`)
2. Saves all model outputs to structured files:
   - `EXAMPLES.md`: Human-readable formatted output with color indicators
   - `MODELS.json`: Machine-readable model data
3. In sequential mode, can save each example to separate files
4. Displays output location when complete

**Output Modes:**

- **Batch Mode** (default): All examples saved to single `EXAMPLES.md` file
- **Sequential Mode**: Each example saved separately
  - `multiple`: Each example in its own file under `sequential/` directory
  - `single`: All examples in one `EXAMPLES.md` with separators

**Directory Structure:**

```
output_20240305_143022/
├── EXAMPLES.md          # Formatted human-readable output
├── MODELS.json          # Structured model data
└── sequential/          # (Only in sequential mode with multiple files)
    ├── example1.md
    ├── example2.md
    └── ...
```

**EXAMPLES.md Format:**

```markdown
## Example: test_case (Theory: logos)

**Model Found**: Yes

**Evaluation World**: s1

### States

- ⭐ s1 (Evaluation World)
- 🔵 s2 (World State)
- 🟢 s0 (Possible)
- 🔴 s3 (Impossible)

### Relations

#### R Relation

- s1 → s1, s2
- s2 → s1

### Propositions

- **p**: s1 ✓, s2 ✗
- **q**: s1 ✗, s2 ✓

### Model Output

```
[Original console output preserved here]
```
```

**State Indicators:**
- 🟢 Green = Possible states
- 🔴 Red = Impossible states  
- 🔵 Blue = World states
- ⭐ Star = Evaluation world

**When to Use:**

- Documenting interesting countermodels for papers or presentations
- Creating test cases from discovered models
- Building a library of example models
- Sharing model results with collaborators

### Combining Flags

You can combine multiple flags for comprehensive debugging:

```bash
# Show constraints, Z3 model, and save output to timestamped directory
./dev_cli.py -p -z -s examples_file.py

# Save output in sequential mode with multiple files
./dev_cli.py -s --output-mode sequential examples_file.py

# Show impossible states and constraints
./dev_cli.py -i -p examples_file.py

# Maximum debugging information
./dev_cli.py -i -p -z examples_file.py

# Debug and save with custom output mode
./dev_cli.py -p -z -s --output-mode sequential --sequential-files single examples_file.py
```

### In Example Files

You can also set these options in your example file's `general_settings`:

```python
general_settings = {
    "print_impossible": True,    # Same as -i flag
    "print_constraints": True,   # Same as -p flag
    "print_z3": True,           # Same as -z flag
    "save_output": True,        # Same as -s flag (automatically saves to timestamped directory)
}
```

Note: The `save_output` option now automatically saves to a timestamped directory without prompting. Use command-line flags `--output-mode` and `--sequential-files` to control the output format.

### Debugging Workflow

A typical debugging workflow might look like:

1. **Run normally first** to see if a model exists
2. **Add -p** to see what constraints are generated
3. **Add -z** to see exact variable assignments or unsat core
4. **Add -i** if states seem to be missing
5. **Use -s** to save interesting results

### Performance Considerations

- **-p and -z flags** add overhead by formatting constraint output
- **-i flag** may increase computation time for models with many impossible states
- For performance testing, run without debug flags
- Debug flags are ignored in maximize mode (-m) for cleaner comparison output

## Related Documentation

- **[Examples Guide](EXAMPLES.md)** - Standard structure for example files
- **[Architecture](ARCHITECTURE.md)** - System design and component relationships
- **[Theory Library](../src/model_checker/theory_lib/README.md)** - Available semantic theories
- **[Development Guide](DEVELOPMENT.md)** - Contributing and development workflow

---

[← Back to Technical Docs](README.md) | [Development →](DEVELOPMENT.md) | [Tests →](TESTS.md)
