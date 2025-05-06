# Notebooks for Default Theory

This directory contains Jupyter notebooks that demonstrate various aspects of the default theory implementation. These notebooks provide interactive examples and visualizations to help you understand the theory's semantics and operators.

## Available Notebooks

| Notebook | Description |
|----------|-------------|
| [constitutive.ipynb](constitutive.ipynb) | Demonstrates constitutive logic operators (ground, essence, identity) with countermodels and valid theorems |
| [counterfactual.ipynb](counterfactual.ipynb) | Explores counterfactual operators (would/might conditionals) with examples of invalid and valid reasoning patterns |
| [extensional.ipynb](extensional.ipynb) | Illustrates classical extensional logic (conjunction, disjunction, implication) showing key countermodels and theorems |
| [modal.ipynb](modal.ipynb) | Covers modal operators (necessity, possibility) demonstrating modal axioms (K, T, 4, B, 5) and defined operators |
| [relevance.ipynb](relevance.ipynb) | Examines relevance logic with examples showing content-sensitive reasoning patterns |

## Usage

Each notebook follows a consistent structure:
1. Setup and imports
2. Helper function definition for running examples
3. Countermodels demonstrating invalid arguments
4. Theorems demonstrating valid arguments
5. (In some cases) Exploration of defined operators

To run these notebooks:
```bash
# From project root directory
./run_jupyter.sh
```

Then navigate to the `src/model_checker/theory_lib/default/notebooks/` directory and select a notebook to open.

## Relationship to Example Modules

These notebooks directly correspond to the example modules found in the [examples](../examples/) directory:

- `constitutive.ipynb`: [examples/constitutive.py](../examples/constitutive.py)
- `counterfactual.ipynb`: [examples/counterfactual.py](../examples/counterfactual.py)
- `extensional.ipynb`: [examples/extensional.py](../examples/extensional.py)
- `modal.ipynb`: [examples/modal.py](../examples/modal.py)
- `relevance.ipynb`: [examples/relevance.py](../examples/relevance.py)

For detailed documentation on the example modules, see the [examples README](../examples/README.md).

## Notebook Output

Each example in these notebooks produces output showing:
- The model structure (with possible and impossible states)
- The evaluation world
- Interpreted premises and conclusions
- Verification and falsification patterns for each formula
- Visual indicators of truth values at each world

This allows you to:
- Understand why certain logical arguments are valid or invalid
- Visualize the semantic structure underlying logical operators
- Explore the relationships between different logical systems within the default theory

## Example Output Format

```
========================================

EXAMPLE Example Name: there is a countermodel.

Atomic States: 3

Semantic Theory: Default Semantics

Premise:
1. A

Conclusion:
2. B

Z3 Run Time: 0.004 seconds

========================================
State Space:
  #b000 = ¡
  #b001 = a
  #b010 = b
  #b011 = a.b (world)
  ...

The evaluation world is: a.b

INTERPRETED PREMISE:
1. |A| = < {a.b}, {b.c} >  (True in a.b)

INTERPRETED CONCLUSION:
2. |B| = < {b}, {a.c} >  (False in a.b)

Total Run Time: 0.085 seconds
========================================
```

## Next Steps

After exploring these notebooks, you may want to:
1. Check out the [default theory demo notebooks](../notebooks/default_demo.ipynb) for higher-level interactive examples
2. Explore the example files in the [examples directory](../examples/) to see all available examples
3. Review the implementation in [semantic.py](../semantic.py) and [operators.py](../operators.py)
4. Try creating your own examples or modifying existing ones to deepen your understanding
