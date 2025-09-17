# Getting Started with ModelChecker

[← Back to Installation](README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Technical Docs →](../../Code/docs/README.md)

This guide walks you through the basics of using ModelChecker to explore logical theories and test formulas.

## Table of Contents

1. [Before You Begin: Setting Up Your Editor](#before-you-begin-setting-up-your-editor)
2. [Creating Your First Project](#creating-your-first-project)
3. [Understanding the Project Structure](#understanding-the-project-structure)
4. [Running Examples](#running-examples)
5. [Modifying Examples](#modifying-examples)
6. [Exploring Different Theories](#exploring-different-theories)
7. [Next Steps](#next-steps)

## Before You Begin: Setting Up Your Editor

> NOTE: Skip this section if you already have an editor set up.

Working with ModelChecker involves editing Python files containing logical formulas. A properly configured text editor makes this much easier by providing:

- **Syntax highlighting** for Python code
- **Unicode support** for logical symbols (∧, ∨, ¬, □, ◇)
- **LaTeX preview** for mathematical notation
- **Auto-completion** for common patterns
- **Keybindings** for running examples

Setting up a good text editor provides an essential foundation for using the `model-checker`. In addition to editing Python files, modern editors provide a vastly improved experience for writing in LaTeX and Markdown, consolidating all of your text editing into a single platform which you can configure to suite your exact needs. Especially for academics, no tool is more important than your editor.

### Recommended Editors

It is well worth watching demo videos on YouTube and chatting with an LLM before choosing your editor if you have not already.

#### For Beginners: VSCodium

- **Repository**: [VSCodium Setup Guide](https://github.com/benbrastmckie/VSCodium)
- Open-source version of VS Code with helpful extensions pre-configured
- User-friendly interface with point-and-click functionality
- Great for those new to programming

#### For Advanced Users: NeoVim

- **Repository**: [NeoVim Configuration](https://github.com/benbrastmckie/.config)
- Powerful text editor with extensive customization
- Keyboard-driven workflow for efficiency
- Ideal for experienced developers

## Creating Your First Project

### Step 1: Install ModelChecker

If you haven't already, install ModelChecker:

```bash
pip install model-checker
```

### Step 2: Create a New Project

To create a project using a given theory as a template, run:

```bash
model-checker -l <theory_name>
```

You'll be prompted to:

1. Choose whether to create a new project (type `y`)
2. Enter a project name (use snake_case, e.g., `some_name`)

Available theories:

- `logos` - Hyperintensional bilateral semantics (default)
- `exclusion` - Unilateral semantics with exclusion
- `imposition` - Fine's counterfactual semantics
- `bimodal` - Temporal-modal logic

**Example**:

```bash
model-checker -l imposition
```

You can also load the `logos` theory by simply running:

```bash
model-checker
```

This creates a new project with the Logos theory by default.

## Understanding the Project Structure

After creating a project, you'll have these files:

```
project_my_logic/
├── README.md       # Theory-specific documentation
├── examples.py     # Pre-configured examples to run
├── __init__.py     # Makes the directory a Python package
├── semantic.py     # Core semantic definitions
├── operators.py    # Logical operators for the theory
├── docs/          # Additional documentation
└── notebooks/     # Interactive Jupyter notebooks (if available)
```

### The `examples.py` File

This is your main working file. It contains:

1. **Import statements** - Load the theory components
2. **Example definitions** - Logical formulas to test
3. **Settings** - Control model generation
4. **Theory configuration** - Specify which semantic theory to use

Examples files may be saved in an `examples/` directory if you have many example files that you are working with for a given theory.

## Running Examples

### Required Variables in examples.py

For ModelChecker to successfully run an examples.py file, it must contain these essential variables:

#### 1. `semantic_theories` (Required)

A dictionary mapping theory names to their implementations, where at least one must be provided:

```python
semantic_theories = {
    "logos": logos_theory,            # Maps a name to the theory object
    "imposition": imposition_theory,  # NOTE: it is often convenient to comment out all but one theory
}
```

#### 2. `example_range` (Required)

A dictionary of examples that will be executed when you run the file. Each key is an example name, each value is a list containing `[premises, conclusions, settings]`:

```python
# Define individual examples first
EXT_CM_1_premises = ["A", "(A \\rightarrow B)"]
EXT_CM_1_conclusions = ["\\Box B"]
EXT_CM_1_settings = {
    'N': 4,                    # Max number of atomic propositions
    'contingent': True,        # All propositions must be contingent
    'non_null': True,          # Exclude the null state
    'non_empty': True,         # Require non-empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': True,       # True = expect countermodel, False = expect theorem
}
EXT_CM_1_example = [
    EXT_CM_1_premises,
    EXT_CM_1_conclusions,
    EXT_CM_1_settings
]

EXT_TH_1_premises = ["A", "(A \\rightarrow B)"]
EXT_TH_1_conclusions = ["B"]
EXT_TH_1_settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # True = expect countermodel, False = expect theorem
}
EXT_TH_1_example = [
    EXT_TH_1_premises,
    EXT_TH_1_conclusions,
    EXT_TH_1_settings
]

# This is what model-checker executes
example_range = {
  # Countermodels
  "EXT_CM_1": EXT_CM_1_example,
  # ... potentially dozens more

  # Theorems
  "EXT_TH_1": EXT_TH_1_example,
  # ... potentially dozens more
}
```

For more detailed information, see the [Examples Documentation](Code/docs/EXAMPLES.md).

#### 3. `unit_tests` (Common but Optional)

A dictionary used by the testing framework (`run_tests.py`) to run comprehensive test suites. Often organized by grouping countermodels and theorems separately:

```python
# Group examples by type
ext_cm_examples = {
    "EXT_CM_1": EXT_CM_1_example,   # ANTECEDENT STRENGTHENING
    "EXT_CM_2": EXT_CM_2_example,   # CONTRAPOSITION
    "EXT_CM_3": EXT_CM_3_example,   # TRANSITIVITY FAILURE
    # ... more countermodels
}

ext_th_examples = {
    "EXT_TH_1": EXT_TH_1_example,   # MODUS PONENS
    "EXT_TH_2": EXT_TH_2_example,   # DISJUNCTIVE SYLLOGISM
    "EXT_TH_3": EXT_TH_3_example,   # HYPOTHETICAL SYLLOGISM
    # ... more theorems
}

# Combine collections using dictionary unpacking
unit_tests = {**ext_cm_examples, **ext_th_examples}

# Used by: ./run_tests.py --examples logos
```

For more detailed information, see the [Unit Tests Documentation](Code/UNIT_TESTS.md).

#### 4. `general_settings` (Optional)

Controls execution behavior and output formatting:

```python
general_settings = {
    "print_impossible": False,    # Show impossible states
    "print_constraints": False,   # Display Z3 constraints
    "print_z3": False,           # Show Z3 model/unsat core
    "save_output": False,        # Save results to files
    "maximize": False,           # Find maximum N for each theory
    "align_vertically": False,   # Vertical time display (bimodal)
}
```

If not provided, all default to `False`.

See the [Tools and Settings](TOOLS.md) as well as the [Examples Standard](EXAMPLES.md) for how to create and use example files.

### Basic Execution

Navigate to your project directory and run:

```bash
model-checker examples.py
```

### What You'll See

The output shows:

- Whether the formula is valid (a theorem) or invalid
- Countermodels when formulas are invalid
- Model details including propositions and their truth values

### Example Output

#### Valid Formula (Theorem)

```
========================================

EXAMPLE EXT_TH_1: there is no countermodel.

Atomic States: 3

Semantic Theory: Brast-McKie

Premises:
1. A
2. (A \rightarrow B)

Conclusion:
3. B

Z3 Run Time: 0.0098 seconds

========================================
```

#### Invalid Formula (Countermodel)

```
========================================

EXAMPLE CF_CM_1: there is a countermodel.

Atomic States: 4

Semantic Theory: Brast-McKie

Premises:
1. \neg A
2. (A \boxright C)

Conclusion:
3. ((A \wedge B) \boxright C)

Z3 Run Time: 0.0293 seconds

========================================
State Space:
  #b0000 = □
  #b0001 = a
  #b0010 = b
  #b0100 = c
  #b0101 = a.c (world)
  #b0110 = b.c (world)
  ...

The evaluation world is: b.c

INTERPRETED PREMISES:

1.  |\neg A| = < {b.c}, {a, a.b.c.d} >  (True in b.c)
      |A| = < {a, a.b.c.d}, {b.c} >  (False in b.c)

2.  |(A \boxright C)| = < {a.c, b.c}, {a.d} >  (True in b.c)
      |A| = < {a, a.b.c.d}, {b.c} >  (False in b.c)
      |A|-alternatives to b.c = {a.c}
        |C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >  (True in a.c)

INTERPRETED CONCLUSION:

3.  |((A \wedge B) \boxright C)| = < ∅, {a.d, b.c} >  (False in b.c)
      |(A \wedge B)| = < {a.b, a.b.c, a.b.c.d, a.b.d, a.d}, {a.b.c, a.c, b.c} >  (False in b.c)
        |A| = < {a, a.b.c.d}, {b.c} >  (False in b.c)
        |B| = < {a.b, a.b.c, a.b.c.d, a.b.d, b, b.c.d, b.d, d}, {a.c} >  (True in b.c)
      |(A \wedge B)|-alternatives to b.c = {a.d}
        |C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >  (False in a.d)

Total Run Time: 0.2815 seconds

========================================
```

For countermodels, the output includes:

- **State Space**: All possible states and their status (world, impossible, or base state)
- **Evaluation World**: The specific world where the premises are true but conclusion is false
- **Interpreted Formulas**: Shows verifier/falsifier sets and truth values at the evaluation world

## Exploring Different Theories

### Theory-Specific Features

Each theory has unique operators and capabilities:

#### Logos Theory

- Full hyperintensional semantics
- Counterfactual operators: `\boxright`, `\diamondright`
- Constitutive operators: `\equiv`, `\sqsubseteq`
- See: [Logos Documentation](../Code/src/model_checker/theory_lib/logos/README.md)

#### Exclusion Theory

- Unilateral negation semantics
- Exclusion operator: `\exclude`
- Solves the False Premise Problem
- See: [Exclusion Documentation](../Code/src/model_checker/theory_lib/exclusion/README.md)

#### Imposition Theory

- Fine's counterfactual semantics
- Specialized for counterfactual reasoning
- See: [Imposition Documentation](../Code/src/model_checker/theory_lib/imposition/README.md)

#### Bimodal Theory

- Combines temporal and modal operators
- Past/Future: `P`, `F`
- Necessity/Possibility: `\Box`, `\Diamond`
- See: [Bimodal Documentation](../Code/src/model_checker/theory_lib/bimodal/README.md)

## Next Steps

### Essential Documentation

**In this directory (Docs/):**

- [Installation Guide](INSTALLATION.md) - Platform-specific setup
- [Development Guide](DEVELOPMENT.md) - Contributing to ModelChecker
- [Tools Guide](TOOLS.md) - Advanced debugging and analysis
- [Architecture](architecture/README.md) - Research approach and validation

**Theory Documentation:**

- [Theory Library Overview](../Code/src/model_checker/theory_lib/README.md)
- [Usage Guide](../Code/src/model_checker/theory_lib/docs/USAGE_GUIDE.md)
- [Examples Guide](../Code/src/model_checker/theory_lib/docs/EXAMPLES.md)

**Framework Documentation:**

- [Core Framework](../Code/src/model_checker/README.md) - Architecture and design
- [API Reference](../Code/src/model_checker/README.md) - Framework API documentation

### Advanced Topics

- **Custom Theories**: Create your own semantic theory
- **Model Iteration**: Find multiple models satisfying constraints
- **Debugging**: Use print flags (`-p`, `-z`) to see Z3 constraints
- **Batch Testing**: Run comprehensive test suites

### Getting Help

- Check the [Tools Guide](../Code/docs/TOOLS.md#troubleshooting) for troubleshooting
- Review theory-specific documentation
- Examine the example files in each theory
- Create an issue on [GitHub](https://github.com/benbrastmckie/ModelChecker/issues)

---

[← Back to Docs](README.md) | [Installation →](INSTALLATION.md) | [Technical Docs →](../Code/docs/README.md)
