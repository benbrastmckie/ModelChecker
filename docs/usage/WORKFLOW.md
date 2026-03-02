# Methodology Overview: Developing Semantic Theories

[← Previous: Project Setup](PROJECT.md) | [Next: Writing Examples →](EXAMPLES.md)

## Introduction

The ModelChecker provides a systematic methodology for developing and studying semantic theories. Implementing a semantics with the model-checker provides the computational tools needed to study the logic for language in question by exploring the range of countermodels and theorems in that language.

This guide presents the big picture methodology - a step-by-step workflow for developing semantic theories from initial project creation through advanced analysis and output.

**Architecture**: For the complete system architecture, see [Architecture Overview](../architecture/README.md) and the [Pipeline](../architecture/PIPELINE.md) which cover the end-to-end data flow.

## The ModelChecker Methodology

### Step 1: Create Your Theory Project

After [installing the model-checker](../installation/README.md), start by creating a new project or loading an existing theory:

```bash
# Create a copy of the logos semantics
model-checker                           # Creates a logos semantics by default with all subtheories

# Load an existing theory as starting point
model-checker -l logos                  # Creates a logos semantics by default with all subtheories
model-checker -l exclusion              # Unilateral exclusion semantics
model-checker -l imposition             # Fine's counterfactual semantics
model-checker -l bimodal                # Bimodal logic for tense and circumstantial modalities

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

**Purpose**: Study an existing semantic theory or else use an existing theory as a template by which to create your own semantics.

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
CF_CM_1_example = [
    CF_CM_1_premises,
    CF_CM_1_conclusions,
    CF_CM_1_settings
]

# Test a counterfactual theorem (expects validity)
CF_TH_5_premises = ["((A \\vee B) \\boxright C)"]
CF_TH_5_conclusions = ["(A \\boxright C)"]
CF_TH_5_settings = {
    'N': 3,
    'max_time': 10,
    'expectation': False  # Expect valid (no countermodel)
}
CF_TH_5_example = [
    CF_TH_5_premises,
    CF_TH_5_conclusions,
    CF_TH_5_settings
]

# Export examples for the model checker
example_range = {
    "CF_CM_1": CF_CM_1_example,
    "CF_TH_5": CF_TH_5_example
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

For theorems (valid inferences), the output is simpler since no countermodel exists:

```
EXAMPLE CF_TH_5: there is no countermodel.

Atomic States: 4

Semantic Theory: Brast-McKie

Premise:
1. ((A \vee B) \boxright C)

Conclusion:
2. (A \boxright C)

Z3 Run Time: 0.0441 seconds

========================================
```

This confirms that CF_TH_5 is a valid theorem - from "If A or B, then C" we can infer "If A, then C" in counterfactual logic - since there are no countermodels with `N = 3`.

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

Modify `semantic.py` to implement your specific semantic theory by inheriting from LogosSemantics:

```python
from model_checker.theory_lib.logos.semantic import LogosSemantics
from z3 import *

class MySemantics(LogosSemantics):
    def __init__(self, combined_settings=None, **kwargs):
        super().__init__(combined_settings, **kwargs)

        # LogosSemantics provides these default constraints:
        #   - possibility_downward_closure (states inherit possibility from their parts)
        #   - is_world(main_world) (evaluation point must be a world)

        # OPTION 1: Extend existing constraints (adds to defaults)
        self.frame_constraints.extend([
            self.some_new_constraint(),
            self.another_frame_constraint()
        ])

        # OPTION 2: Replace constraints entirely (removes defaults)
        # self.frame_constraints = [
        #     self.possibility_upward_closure(),  # Different from default
        #     self.is_world(self.main_world),     # Keep this essential constraint
        # ]

    def possibility_upward_closure(self):
        """Alternative: parts inherit possibility from wholes."""
        x, y = z3.BitVecs("up_x up_y", self.N)
        return ForAll([x, y],
            z3.Implies(
                z3.And(
                    self.possible(x),
                    self.is_part_of(x, y)
                ),
                self.possible(y)  # Opposite of default behavior
            )
        )
```

**Purpose**: Implement the core logical principles that distinguish your semantic theory from others.

**Next**: See [Semantics Guide](SEMANTICS.md) for constraint implementation patterns and semantic frameworks.

### Step 5: Define Custom Operators

Add logical operators in `operators.py`. There are two types:

#### Defined Operators (Convenience - No New Expressive Power)

These are shortcuts for commonly used combinations of existing operators:

```python
from model_checker.syntactic import DefinedOperator

class MaterialBiconditional(DefinedOperator):
    """Material biconditional: P ↔ Q := (P → Q) ∧ (Q → P)"""

    name = "\\leftrightarrow"  # LaTeX command
    arity = 2                  # Binary operator

    def derived_definition(self, leftarg, rightarg):
        # Define using existing operators
        return [AndOperator,
                [ConditionalOperator, leftarg, rightarg],
                [ConditionalOperator, rightarg, leftarg]]

class NecessarilyImplies(DefinedOperator):
    """Necessary implication: □(P → Q)"""

    name = "\\strictif"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [BoxOperator,
                [ConditionalOperator, leftarg, rightarg]]
```

#### Primitive Operators (Extends Expressive Power)

These require semantic interpretation and cannot be defined using other operators:

```python
from model_checker.syntactic import PrimitiveOperator

class CounterfactualOperator(PrimitiveOperator):
    """Counterfactual conditional (cannot be reduced to other operators)"""

    name = "\\boxright"
    arity = 2

    # Must define semantic methods for your theory
    def true_at(self, leftarg, rightarg, eval_point):
        """When is A □→ B true at an evaluation point?"""
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("t_cf_x", N)
        u = z3.BitVec("t_cf_u", N)
        return ForAll([x, u],
            z3.Implies(
                z3.And(
                    semantics.extended_verify(x, leftarg, eval_point),
                    semantics.is_alternative(u, x, eval_point["world"])
                ),
                semantics.true_at(rightarg, {"world": u})
            )
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """When is A □→ B false at an evaluation point?"""
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("f_cf_x", N)
        u = z3.BitVec("f_cf_u", N)
        return Exists([x, u],
            z3.And(
                semantics.extended_verify(x, leftarg, eval_point),
                semantics.is_alternative(u, x, eval_point["world"]),
                semantics.false_at(rightarg, {"world": u})
            )
        )

    # Many other methods are typically provided for robustness:
    # find_verifiers_and_falsifiers, semantic_equivalence, etc.
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
from model_checker.theory_lib.logos import get_theory as get_logos
from model_checker.theory_lib.exclusion import get_theory as get_exclusion

logos_theory = get_logos()
exclusion_theory = get_exclusion()

semantic_theories = {
    "Logos": logos_theory,
    "Exclusion": exclusion_theory,
}
```

When you define multiple theories, ModelChecker will:
1. **Run each example against all theories** to find different verdicts
2. **Report which theories validate/invalidate each inference**
3. **Show countermodels only for theories that find the inference invalid**

Run comparative analysis:

```bash
# Test single theory (normal mode)
model-checker examples.py

# Compare all defined theories and show differences
model-checker examples.py --maximize
```

The `--maximize` flag enables **theory comparison mode**, showing how different semantic theories handle the same logical inferences differently.

**Purpose**: Explore the space of models your theory allows and systematically compare it with alternative approaches.

**Next**: See [Tools Guide](TOOLS.md) for model iteration, theory comparison, and advanced analysis techniques.

### Step 7: Save and Export Results

Export your findings in formats suitable for further analysis or publication:

```python
# Configure output in your examples
general_settings = {
    "save_output": True,
    "output_format": "markdown",  # or "json", "jupyter"
}
```

```bash
# Command-line output options
model-checker examples.py --save json      # Machine-readable JSON
model-checker examples.py --save markdown  # Human-readable markdown
model-checker examples.py --save jupyter   # Interactive Jupyter notebook
model-checker examples.py --save           # All formats (json, markdown, jupyter)
```

Results are saved in the `output/` directory with countermodels, model comparisons, and iteration analyses.

**Purpose**: Preserve and format your semantic investigations for analysis, documentation, and publication.

**Next**: See [Output Guide](OUTPUT.md) for format options, file organization, and integration workflows.

## Quick Command Reference

```bash
# Project Setup
model-checker                              # Create new logos project
model-checker -l <theory_name>             # Load existing theory
model-checker -l logos --subtheory modal   # Load logos with specific subtheories

# Run Examples
model-checker examples.py                  # Basic execution
model-checker examples.py --maximize       # Test theories

# Save Results
model-checker examples.py --save           # All formats (json, markdown, jupyter)
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
