# Notebooks for Imposition Theory

This directory contains Jupyter notebooks that demonstrate various aspects of Fine's imposition theory implementation. These notebooks provide interactive examples and visualizations to help you understand the theory's semantics and counterfactual operators.

## Available Notebooks

| Notebook | Description |
|----------|-------------|
| [examples.ipynb](examples.ipynb) | Demonstrates both imposition and counterfactual operators with comprehensive examples of countermodels and theorems |

## Usage

Each notebook follows a consistent structure:
1. Setup and imports
2. Helper function definition for running examples
3. Countermodels demonstrating invalid arguments
4. Theorems demonstrating valid arguments

To run these notebooks:
```bash
# From project root directory
./run_jupyter.sh
```

Then navigate to the `src/model_checker/theory_lib/imposition/notebooks/` directory and select a notebook to open.

## Relationship to Example Module

The notebooks directly correspond to the examples module in the imposition theory:

- `examples.ipynb`: [examples.py](../examples.py)

This notebook provides an interactive way to explore the examples defined in the examples.py file, allowing you to see the semantic models that verify or falsify specific logical principles.

## Notebook Output

Each example in these notebooks produces output showing:
- The model structure (with possible and impossible states)
- The evaluation world
- Interpreted premises and conclusions
- Verification and falsification patterns for each formula
- Visual indicators of truth values at each world

This allows you to:
- Understand why certain arguments involving counterfactuals are valid or invalid
- Visualize the semantic structure underlying imposition operators
- Compare Fine's imposition approach with Brast-McKie's counterfactual theory
- Explore the detailed formal semantics for counterfactual reasoning

## Example Output Format

```
========================================

EXAMPLE Example Name: there is a countermodel.

Atomic States: 3

Semantic Theory: Imposition Semantics

Premise:
1. (A \imposition C)

Conclusion:
2. ((A \wedge B) \imposition C)

Z3 Run Time: 0.004 seconds

========================================
State Space:
  #b000 = □
  #b001 = a
  #b010 = b
  #b011 = a.b (world)
  ...

The evaluation world is: a.b

INTERPRETED PREMISE:
1. |(A \imposition C)| = < {□}, ∅ >  (True in a.b)
   |A| = < {a.b}, {b.c} >  (True in a.b)
   |A|-alternatives to a.b = {a.b}
     |C| = < {c}, {a.c} >  (True in a.b)

INTERPRETED CONCLUSION:
2. |((A \wedge B) \imposition C)| = < ∅, {□} >  (False in a.b)
   |(A \wedge B)| = < {a.b.c}, {a, b} >  (False in a.b)
     |A| = < {a.b}, {b.c} >  (True in a.b)
     |B| = < {b.c}, {a} >  (False in a.b)
   |(A \wedge B)|-alternatives to a.b = {b.c}
     |C| = < {c}, {a.c} >  (False in b.c)

Total Run Time: 0.085 seconds
========================================
```

## Imposition vs. Counterfactual Semantics

The notebooks demonstrate both of Fine's imposition operators (`\imposition` and `\could`) alongside Brast-McKie's counterfactual operators (`\boxright` and `\diamondright`), highlighting their similarities and differences:

1. **Imposition Operators**:
   - `\imposition`: Fine's "would" counterfactual operator
   - `\could`: Fine's "might" counterfactual operator (possibility under imposition)

2. **Counterfactual Operators**:
   - `\boxright`: Brast-McKie's "would" counterfactual operator
   - `\diamondright`: Brast-McKie's "might" counterfactual operator

The examples show that both semantic approaches validate similar core principles while differing on others, providing insight into the formal semantics of counterfactual reasoning.

## Next Steps

After exploring these notebooks, you may want to:
1. Compare the results with the [default theory notebooks](../../default/notebooks/) to understand the differences between Fine's and Brast-McKie's approaches
2. Explore the implementation in [semantic.py](../semantic.py) and [operators.py](../operators.py)
3. Try creating your own examples or modifying existing ones to deepen your understanding
4. Read the papers by Fine and Brast-McKie referenced in the documentation