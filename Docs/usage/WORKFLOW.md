# Methodology Overview: Developing Semantic Theories

[← Previous: Project Setup](PROJECT.md) | [Next: Writing Examples →](EXAMPLES.md)

## Introduction

The ModelChecker provides a systematic methodology for developing and studying semantic theories. Rather than working with abstract logical systems, you create concrete computational models that can automatically test inferences, generate counterexamples, and compare different semantic approaches.

This guide presents the big picture methodology - a step-by-step workflow for developing semantic theories from initial project creation through advanced analysis and output.

**Architecture Foundation**: For the complete system architecture that enables this workflow, see [Architecture Overview](../architecture/README.md) and the [Pipeline Architecture](../architecture/PIPELINE.md) that shows the complete data flow.

## The ModelChecker Methodology

### Step 1: Create Your Theory Project

Start by creating a new project or loading an existing theory:

```bash
# Create a copy of the logos semantics
model-checker                           # Creates a logos semantics by default with all subtheories

# Load an existing theory as starting point
model-checker -l logos                  # Creates a logos semantics by default with all subtheories
model-checker -l exclusion              # Unilateral exclusion semantics
model-checker -l imposition             # Fine's counterfactual semantics
model-checker -l bimodal                # Temporal-modal logic

# Load specific logos subtheories (default loads all)
model-checker -l logos --subtheory counterfactual       # Just counterfactual + dependencies
model-checker -l logos --subtheory modal constitutive   # Multiple subtheories
model-checker -l logos -st extensional                  # Short form (-st)
```

**Available Logos Subtheories:**
When using `model-checker -l logos`, all available subtheories are loaded by default:
- **extensional**: Basic logical operators (¬, ∧, ∨, →, ↔, ⊤, ⊥)
- **modal**: Necessity and possibility operators (□, ◇) - requires extensional, counterfactual
- **constitutive**: Content relationships (≡, ≤, ⊑, ⪯, ⇒)
- **counterfactual**: Counterfactual conditionals (□→, ◇→) - requires extensional
- **relevance**: Content-sensitive relevance logic - requires constitutive

**Note on Dependencies:** When you specify a subtheory, its dependencies are automatically loaded. For example, `--subtheory modal` will also load extensional and counterfactual.

This creates a complete project directory with `examples.py`, `semantic.py`, `operators.py`, and supporting files. You now have a working semantic theory that you can run, test, and modify.

**Purpose**: Establish the computational foundation for your semantic investigation.

**Next**: See [Project Creation Guide](PROJECT.md) for detailed project setup options and structure.

### Step 2: Develop Examples

Edit the `examples.py` file to test logical inferences relevant to your theory:

```python
# Test counterfactual antecedent strengthening (expects countermodel)
CF_CM_1_premises = ["\\neg A", "(A \\boxright C)"]
CF_CM_1_conclusions = ["((A \\wedge B) \\boxright C)"]
CF_CM_1_settings = {
    'N': 3,
    'max_time': 10,
    'expectation': True  # Expect countermodel (invalid inference)
}

# Test a counterfactual theorem (expects validity)
CF_TH_5_premises = ["(A \\boxright B)"]
CF_TH_5_conclusions = ["(\\neg B \\boxright \\neg A)"]
CF_TH_5_settings = {
    'N': 3,
    'max_time': 10,
    'expectation': False  # Expect valid (no countermodel)
}
```

Run your examples to test whether inferences are valid:

```bash
model-checker examples.py
```

### Example Output:

Here's what you see when running counterfactual logic examples:

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

Z3 Run Time: 0.0341 seconds

========================================

State Space:
  #b0101 = a.c (world)
  #b0110 = b.c (world)
  #b1001 = a.d (world)

The evaluation world is: b.c

INTERPRETED PREMISES:

1. |\neg A| = < {b.c}, {a, a.b.c.d} >  (True in b.c)
2. |(A \boxright C)| = < {a.c, b.c}, {a.d} >  (True in b.c)
    |A|-alternatives to b.c = {a.c}
    |C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >  (True in a.c)

INTERPRETED CONCLUSION:

3. |((A \wedge B) \boxright C)| = < {}, {a.c, a.d, b.c} >  (False in b.c)
    |(A \wedge B)|-alternatives to b.c = {a.d}
    |C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >  (False in a.d)

Total Run Time: 0.389 seconds
========================================
```

This shows the ModelChecker found a countermodel, demonstrating that the counterfactual antecedent strengthening argument is invalid in this semantic theory.

**Purpose**: Define the logical questions your theory should answer and verify its behavior on key inferences.

**Next**: See [Examples Guide](EXAMPLES.md) for formula syntax, example patterns, and testing strategies.

### Step 3: Configure Settings

Adjust model parameters to control how ModelChecker searches for countermodels:

```python
# Quick testing - small state spaces
QUICK_settings = {
    'N': 3,              # 8 possible states
    'max_time': 5,       # 5 second timeout
    'contingent': False, # Allow non-contingent propositions
    'iterate': 1,        # Find 1 model
}

# Thorough analysis - larger search space
THOROUGH_settings = {
    'N': 5,              # 32 possible states
    'max_time': 30,      # 30 second timeout
    'contingent': True,  # Require contingent propositions
    'iterate': 3,        # Find up to 3 different models
}
```

Settings control the computational complexity and the types of models ModelChecker will consider.

**Purpose**: Balance computational efficiency with thoroughness to find the models most relevant to your semantic questions.

**Next**: See [Settings Guide](SETTINGS.md) for complete parameter reference and optimization strategies.

### Step 4: Adapt Semantic Framework

Modify `semantic.py` to implement your specific semantic theory by adding constraints:

```python
# Add a new constraint to your semantic class
class MySemantics(LogosSemantics):
    def __init__(self, combined_settings=None, **kwargs):
        super().__init__(combined_settings, **kwargs)

        # Add your custom semantic constraints
        self.frame_constraints.extend([
            self.my_custom_constraint(),
            self.another_constraint()
        ])

    def my_custom_constraint(self):
        """Define how your theory differs from the base theory."""
        x, y = z3.BitVecs("custom_x custom_y", self.N)
        return ForAll([x, y],
            z3.Implies(
                # Your constraint conditions
                z3.And(self.is_world(x), self.is_world(y)),
                # Your constraint requirements
                self.custom_relation(x, y)
            )
        )
```

**Purpose**: Implement the core logical principles that distinguish your semantic theory from others.

**Next**: See [Semantics Guide](SEMANTICS.md) for constraint implementation patterns and semantic frameworks.

### Step 5: Define Custom Operators

Add new logical operators by creating operator classes in `operators.py`:

```python
# Define a new operator
class MyOperator(syntactic.DefinedOperator):
    """Custom logical operator."""

    name = "\\myop"  # LaTeX command
    arity = 2        # Binary operator

    def derived_definition(self, leftarg, rightarg):
        # Define in terms of existing operators
        return [AndOperator,
                [NegationOperator, leftarg],
                rightarg]

# Register the operator
def get_operators():
    return {
        "\\neg": NegationOperator,
        "\\wedge": AndOperator,
        "\\myop": MyOperator,  # Your new operator
    }
```

Use your new operators in examples:

```python
premises = ["(A \\myop B)"]
conclusions = ["(\\neg A \\wedge B)"]
```

**Purpose**: Extend your theory's expressive power with operators that capture the logical concepts central to your investigation.

**Next**: See [Operators Guide](OPERATORS.md) for both defined and primitive operator implementation.

### Step 6: Iterate Models and Compare Theories

Find multiple models to understand the full space of possibilities, and compare different theoretical approaches:

```python
# Find multiple models for a single theory
ITERATION_settings = {
    'N': 4,
    'iterate': 5,        # Find up to 5 different models
    'max_time': 20,
}

# Compare multiple theories on the same examples
semantic_theories = {
    "theory_a": my_theory_a,
    "theory_b": my_theory_b,
    "baseline": logos_theory,
}
```

Run comparative analysis:

```bash
# Find multiple models
model-checker examples.py

# Compare theories (when multiple theories defined)
model-checker examples.py --maximize
```

**Purpose**: Explore the space of models your theory allows and systematically compare it with alternative approaches.

**Next**: See [Tools Guide](TOOLS.md) for model iteration, theory comparison, and advanced analysis techniques.

### Step 7: Save and Export Results

Export your findings in formats suitable for further analysis or publication:

```python
# Configure output in your examples
general_settings = {
    "save_output": True,
    "output_format": "markdown",  # or "json", "latex"
}
```

```bash
# Command-line output options
model-checker examples.py --save json      # Machine-readable
model-checker examples.py --save markdown  # Human-readable
model-checker examples.py --save latex     # Publication-ready
```

Results are saved in the `output/` directory with countermodels, model comparisons, and iteration analyses.

**Purpose**: Preserve and format your semantic investigations for analysis, documentation, and publication.

**Next**: See [Output Guide](OUTPUT.md) for format options, file organization, and integration workflows.

## Quick Command Reference

```bash
# Project Setup
model-checker                    # Create new project
model-checker -l <theory_name>   # Load existing theory
model-checker -l logos --subtheory modal  # Load logos with specific subtheories

# Run Examples
model-checker examples.py        # Basic execution
model-checker examples.py --N=4  # Larger state space
model-checker examples.py --iterate=3  # Multiple models

# Debug and Analyze
model-checker examples.py --maximize    # Compare theories

# Save Results
model-checker examples.py --save json      # JSON format
model-checker examples.py --save markdown  # Markdown format
```

## The Complete Methodology

This systematic approach enables you to:

1. **Start** with working theories as foundations
2. **Test** logical inferences computationally
3. **Customize** semantic behavior through constraints
4. **Extend** expressive power with new operators
5. **Explore** the space of possible models
6. **Compare** different theoretical approaches
7. **Document** and share your findings

Each step builds on the previous ones, creating a complete framework for semantic investigation that combines theoretical rigor with computational verification.

## Next Steps

### Learn the Details

Now that you understand the methodology, dive into the specific guides:

1. **[PROJECT.md](PROJECT.md)** - Project creation and organization
2. **[EXAMPLES.md](EXAMPLES.md)** - Writing and testing logical formulas
3. **[SETTINGS.md](SETTINGS.md)** - Model parameters and optimization
4. **[SEMANTICS.md](SEMANTICS.md)** - Implementing semantic constraints
5. **[OPERATORS.md](OPERATORS.md)** - Defining new logical operators
6. **[TOOLS.md](TOOLS.md)** - Advanced analysis and comparison
7. **[OUTPUT.md](OUTPUT.md)** - Results formatting and export

### Advanced Topics

- **[Architecture Documentation](../architecture/README.md)** - Complete system architecture and design
- **[Pipeline Architecture](../architecture/PIPELINE.md)** - Data flow from inputs to outputs
- **[Builder Architecture](../architecture/BUILDER.md)** - Workflow orchestration details
- **[Theory Library Architecture](../architecture/THEORY_LIB.md)** - Theory framework design
- **[Theory Library Implementation](../../Code/src/model_checker/theory_lib/README.md)** - Existing theories for reference

---

[← Previous: Project Setup](PROJECT.md) | [Back to Usage](README.md) | [Next: Writing Examples →](EXAMPLES.md)
