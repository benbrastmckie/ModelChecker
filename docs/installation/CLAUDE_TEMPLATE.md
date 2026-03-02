# [Project Name] - Claude Code Configuration

**ModelChecker Project Guide**

## Project Overview

This project uses ModelChecker to explore semantic theories and test logical validity. ModelChecker uses the Z3 SMT solver to generate models and countermodels for logical arguments.

**Project Directory**: `[Replace with your project path]`

## Essential Commands

### Running Examples

```bash
# Run your examples file
model-checker examples.py

# Run with maximization (find limits)
model-checker examples.py --maximize

# Save output to files
model-checker examples.py --save

# Print additional debugging information
model-checker examples.py -p  # Print Z3 constraints
model-checker examples.py -z  # Print Z3 model details
```

### Project Structure

```
my_project/
├── examples.py          # Main examples file (required)
├── semantic.py          # Theory semantic definitions
├── operators.py         # Logical operators
├── docs/               # Local project documentation
│   ├── examples.md     # Examples guide
│   ├── settings.md     # Settings reference
│   ├── workflow.md     # Development workflow
│   └── operators.md    # Operator reference
└── README.md           # Project overview
```

## Documentation Index

### Essential Guides

Links to ModelChecker documentation that can be copied to your `docs/` directory:

**Working with Examples:**
- [Examples Guide](https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/Docs/usage/EXAMPLES.md) - How to write and structure examples
- [Settings Guide](https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/Docs/usage/SETTINGS.md) - Configuration options
- [Tools Guide](https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/Docs/usage/TOOLS.md) - Command-line tools and debugging

**Understanding Results:**
- [Output Guide](https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/Docs/usage/OUTPUT.md) - Interpreting model output
- [Semantics Guide](https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/Docs/usage/SEMANTICS.md) - Understanding semantic theories

**Operators and Formulas:**
- [Operators Guide](https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/Docs/usage/OPERATORS.md) - Available logical operators
- [Workflow Guide](https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/Docs/usage/WORKFLOW.md) - Development workflow

**Project Setup:**
- [Project Guide](https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/Docs/usage/PROJECT.md) - Project structure and organization

**Theory Background:**
- [Z3 Background](https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/Docs/theory/Z3_BACKGROUND.md) - Understanding Z3 solver
- [Hyperintensional Semantics](https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/Docs/theory/HYPERINTENSIONAL.md) - Theoretical foundations
- [Theory Implementation](https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/Docs/theory/IMPLEMENTATION.md) - How theories are implemented

## Example File Structure

Your `examples.py` should contain:

### 1. Theory Import

```python
from model_checker.theory_lib.logos import logos_theory
# Or: from model_checker.theory_lib.imposition import imposition_theory
# Or: from model_checker.theory_lib.exclusion import exclusion_theory
```

### 2. Example Definitions

```python
# Define premises, conclusions, and settings
example_premises = ["A", "(A \\rightarrow B)"]
example_conclusions = ["B"]
example_settings = {
    'N': 3,                    # Max atomic propositions
    'contingent': False,       # Allow non-contingent props
    'non_null': False,         # Allow null state
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # False = expect theorem
}

# Combine into example
example = [example_premises, example_conclusions, example_settings]
```

### 3. Required Variables

```python
# Map theory names to implementations
semantic_theories = {
    "logos": logos_theory,
}

# Define which examples to run
example_range = {
    "MODUS_PONENS": example,
}

# Optional: control output format
general_settings = {
    "print_impossible": False,
    "print_constraints": False,
    "save_output": False,
}
```

## Common Workflows

### Testing a New Argument

```bash
# 1. Add example to examples.py
# 2. Run the model checker
model-checker examples.py

# 3. If unexpected results, debug
model-checker examples.py -p  # See constraints
```

### Comparing Theories

```python
# In examples.py, define multiple theories
semantic_theories = {
    "logos": logos_theory,
    "exclusion": exclusion_theory,
}

# Run with maximization
# model-checker examples.py --maximize
```

### Iterating Models

```python
# Set iterate > 1 to find multiple models
example_settings = {
    'N': 4,
    'iterate': 5,  # Find up to 5 different models
    # ...
}
```

## Best Practices

### Organizing Examples

- Group related examples together
- Use descriptive example names (e.g., "MODUS_PONENS", "CONTRAPOSITION")
- Comment complex formulas
- Start with small N values (3-4) and increase as needed

### Settings Strategy

- **For theorems**: Set `expectation: False`, use minimal N
- **For countermodels**: Set `expectation: True`, may need larger N
- Use `contingent: True` to require non-trivial propositions
- Use `max_time` to prevent long searches

### Debugging

1. Start with simple examples
2. Use `-p` flag to see Z3 constraints
3. Use `-z` flag to see detailed model information
4. Reduce N if searches take too long
5. Check formula syntax carefully

## Notes for Claude Code

- Examples must be valid Python files
- Formula syntax follows LaTeX conventions (\\rightarrow, \\wedge, etc.)
- Z3 solver handles all constraint solving
- Output shows verifier/falsifier sets for each formula
- Check the [Examples Guide](docs/examples.md) for formula syntax details

## Local Documentation

To set up local documentation, ask Claude Code:

```
Please create a docs/ directory in my project and download the following guides
from the ModelChecker repository:
- Examples Guide
- Settings Guide
- Operators Guide
- Tools Guide
- Output Guide
- Workflow Guide

Adapt these guides to focus on my specific project and theory.
```

Claude Code will fetch these files from the GitHub URLs listed above and customize them for your project.

## Getting Help

- Review local documentation in `docs/`
- Check [ModelChecker repository](https://github.com/benbrastmckie/ModelChecker)
- Ask Claude Code to explain specific concepts or examples
- Create issues on GitHub for bugs or feature requests
