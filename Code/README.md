# ModelChecker

[← GitHub Repository](https://github.com/benbrastmckie/ModelChecker) | [General Docs →](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/README.md) | [Technical Docs →](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/docs/README.md)

[![License: GPL-3.0](https://img.shields.io/badge/License-GPL%203.0-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![Python 3.8+](https://img.shields.io/badge/python-3.8+-blue.svg)](https://www.python.org/downloads/)
[![Z3 SMT Solver](https://img.shields.io/badge/Z3-SMT%20Solver-green.svg)](https://github.com/Z3Prover/z3)

A programmatic framework for implementing modular semantic theories powered by the Z3 SMT solver.

## Features

- **Automated Model Finding**: Discovers countermodels to invalid formulas automatically
- **Modular Theory Architecture**: Mix and match logical operators from different theories
- **Hyperintensional Reasoning**: Distinguishes necessarily equivalent propositions
- **Multiple Model Generation**: Find diverse models satisfying your constraints
- **Theory Library**: Pre-built theories to test, adapt, and share with others

## Installation

```bash
pip install model-checker
```

For Jupyter notebook support:

```bash
pip install model-checker[jupyter]
```

## Quick Start

Create a new logic project:

```bash
model-checker -l logos     # Hyperintensional logic
model-checker -l exclusion # Unilateral semantics
model-checker -l imposition # Fine's counterfactuals
model-checker -l bimodal   # Temporal-modal logic
```

## Programmatic Semantics

ModelChecker is a theory-agnostic framework that allows researchers to implement, test, and share semantic theories for logical reasoning. The **[TheoryLib](https://github.com/benbrastmckie/ModelChecker/tree/master/Code/src/model_checker/theory_lib)** provides a collection of pre-built theories that can be used directly, modified for specific needs, or serve as templates for developing new theories. Users can upload their own theories to share with the community, fostering collaborative development of computational semantics.

### Logos: A Formal Language of Thought

The **[Logos Semantics](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/theory_lib/logos/semantic.py)** provides a bilateral semantics for a formal language of thought, implementing hyperintensional distinctions through verifier and falsifier sets. This approach enables the framework to distinguish between propositions that are necessarily equivalent but differ in content which is critical for modeling fine-grained reasoning about counterfactuals and explanatory operators.

Logos currently includes operators organized into modular subtheories:
- **[Extensional operators](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/theory_lib/logos/subtheories/extensional/README.md)**: Classical logical connectives (`∧`, `∨`, `¬`, `→`, `↔`, `⊤`, `⊥`)
- **[Modal operators](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/theory_lib/logos/subtheories/modal/README.md)**: Necessity and possibility (`□`, `◇`)
- **[Counterfactual operators](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/theory_lib/logos/subtheories/counterfactual/README.md)**: Would and might counterfactuals (`□→`, `◇→`)
- **[Constitutive operators](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/theory_lib/logos/subtheories/constitutive/README.md)**: Grounding, essence, and identity (`≤`, `⊑`, `≡`)
- **[Relevance operators](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/theory_lib/logos/subtheories/relevance/README.md)**: Content connection and relevance (`≼`)

The modular architecture allows users to load only the operators needed for their analysis, with automatic dependency resolution ensuring semantic coherence. Additional operators are actively being developed, expanding the theory's expressiveness for new applications in philosophy, logic, and cognitive science.

### Semantic Primitives

The framework defines semantic theories by extending the base `SemanticDefaults` class:

```python
class LogosSemantics(SemanticDefaults):
    def __init__(self, combined_settings):
        super().__init__(combined_settings)
        
        # Core attributes
        self.N = combined_settings['N']  # Bit-width for states
        self.all_states = [BitVecVal(i, self.N) for i in range(1 << self.N)]
        self.null_state = BitVecVal(0, self.N)
        self.full_state = BitVecVal((1 << self.N) - 1, self.N)
        
        # Z3 function declarations
        self.verify = z3.Function("verify", BitVecSort(self.N), AtomSort, BoolSort())
        self.falsify = z3.Function("falsify", BitVecSort(self.N), AtomSort, BoolSort())
        self.possible = z3.Function("possible", BitVecSort(self.N), BoolSort())
        
        # Evaluation point
        self.main_world = z3.BitVec("w", self.N)
        self.main_point = {"world": self.main_world}
        # self.main_time = z3.IntVal(0)  # Under construction in bimodal/
        # self.main_point = {"world": self.main_world, "time": self.main_time}
        
        # Frame constraints
        self.frame_constraints = [self.is_world(self.main_world), ...]
```

### Key Methods

```python
def fusion(self, bit_s, bit_t):
    """Combines two states using bitwise OR."""
    return bit_s | bit_t

def is_part_of(self, bit_s, bit_t):
    """Tests if bit_s is a part of bit_t."""
    return (bit_s & bit_t) == bit_s

def compatible(self, state_x, state_y):
    """Determines if the fusion of two states is possible."""
    return self.possible(self.fusion(state_x, state_y))

def is_world(self, state_w):
    """Determines if a state is a possible world (possible and maximal)."""
    return z3.And(
        self.possible(state_w),
        self.maximal(state_w)
    )

def true_at(self, sentence, eval_point):
    """Evaluates if sentence is true at eval_point.
    For atoms: `∃x ⊆ w: verify(x, atom)`
    For complex: delegates to operator.true_at()"""
    eval_world = eval_point["world"]
    if sentence.sentence_letter is not None:
        x = z3.BitVec("t_atom_x", self.N)
        return Exists(x, z3.And(
            self.is_part_of(x, eval_world),
            self.verify(x, sentence.sentence_letter)
        ))
    return sentence.operator.true_at(*sentence.arguments, eval_point)

def extended_verify(self, state, sentence, eval_point):
    """Tests if state verifies sentence.
    For atoms: verify(state, atom)
    For complex: delegates to operator.extended_verify()"""
    if sentence.sentence_letter is not None:
        return self.verify(state, sentence.sentence_letter)
    return sentence.operator.extended_verify(
        state, *sentence.arguments, eval_point
    )

def is_alternative(self, u, x, w):
    """Tests if u is an x-alternative to w.
    Used in counterfactual evaluation."""
    # Implementation varies by theory
    # Example: u is world where `x ∨ (w ∧ ¬x)` is maximal
```

## Operators

The framework provides modular operators across five subtheories:

### Extensional Operators
- `¬` - Negation (swaps verifiers/falsifiers)
- `∧` - Conjunction (fuses verifiers, distributes falsifiers)
- `∨` - Disjunction (distributes verifiers, fuses falsifiers)
- `→` - Material conditional
- `↔` - Biconditional
- `⊤` - Tautology (always true)
- `⊥` - Contradiction (always false)

### Modal Operators
- `□` - Necessity (true at all worlds)
- `◇` - Possibility (true at some world)

### Counterfactual Operators
- `□→` - Would counterfactual
- `◇→` - Might counterfactual

### Constitutive Operators
- `≤` - Grounding (A grounds B)
- `⊑` - Essence (A is essential to B)
- `≡` - Constitutive equivalence

### Counterfactual Operator Implementation

The counterfactual operator (`□→`) demonstrates the framework's approach:

### Truth Conditions
```python
def true_at(self, leftarg, rightarg, eval_point):
    """A `□→` B is true at w iff:
    For all verifiers x of A and all x-alternatives u to w,
    B is true at u"""
    return ForAll([x, u],
        Implies(
            And(extended_verify(x, leftarg, eval_point),
                is_alternative(u, x, eval_point["world"])),
            true_at(rightarg, {"world": u})
        ))
```

### Falsity Conditions
```python
def false_at(self, leftarg, rightarg, eval_point):
    """A `□→` B is false at w iff:
    There exists a verifier x of A and x-alternative u to w
    where B is false at u"""
    return Exists([x, u],
        And(extended_verify(x, leftarg, eval_point),
            is_alternative(u, x, eval_point["world"]),
            false_at(rightarg, {"world": u})))
```

This implementation captures the hyperintensional nature of counterfactuals - the alternative worlds depend on which specific verifier of the antecedent we consider.

## Theory Examples

Each semantic theory includes an `examples.py` module with a range of examples. The following subsection will focus on counterfactual conditionals.

### Counterfactual Conditionals

**Example 1: Counterfactual Antecedent Strengthening (Invalid)**

```python
# Enable specific examples in examples.py
example_range = {
    "CF_CM_1": CF_CM_1_example,   # Antecedent strengthening
    "CF_TH_5": CF_TH_5_example,    # Simplification of disjunctive antecedent
}

# Run the examples
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py
```

Output for CF_CM_1:
```
EXAMPLE CF_CM_1: there is a countermodel.

Premises:
1. `¬A`
2. `(A □→ C)`

Conclusion:
3. `((A ∧ B) □→ C)`

The evaluation world is: b.c

INTERPRETED PREMISES:
1. `|¬A| = < {b.c}, {a, a.b.c.d} >` (True in b.c)
2. `|(A □→ C)| = < {a.c, b.c}, {a.d} >` (True in b.c)
     `|A|`-alternatives to b.c = {a.c}
     `|C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >` (True in a.c)

INTERPRETED CONCLUSION:
3. `|((A ∧ B) □→ C)| = < {}, {a.c, a.d, b.c} >` (False in b.c)
     `|(A ∧ B)|`-alternatives to b.c = {a.d}
     `|C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >` (False in a.d)
```

This shows that "If A were true then C" doesn't entail "If A and B were true then C" since the additional condition B can change which alternatives are relevant to quantify over. For instance, just the match would light if it were struck, it does not follow that it would light if struck when wet.

**Example 2: Simplification of Disjunctive Antecedent (Valid Theorem)**

Output for CF_TH_5:
```
EXAMPLE CF_TH_5: there is no countermodel.

Premise:
1. `((A ∨ B) □→ C)`

Conclusion:
2. `(A □→ C)`

Z3 Run Time: 0.0342 seconds
```

This theorem shows that counterfactuals satisfy simplification of disjunctive antecedent: assuming C would be the case if either A or B were the case, it follows that C would be the case if A alone were the case (similarly for for B).

### Running Examples

To run specific examples from a theory:

1. Edit the `example_range` dictionary in the theory's examples.py file
2. Run with dev_cli.py:
   ```bash
   ./dev_cli.py src/model_checker/theory_lib/logos/subtheories/[subtheory]/examples.py
   ```

## Available Theories

### Logos: Hyperintensional Truthmaker Semantics

- 19 operators across 5 modular subtheories
- Tracks what propositions are "about" via verifier/falsifier sets
- Distinguishes necessarily equivalent but distinct propositions

### Exclusion: Unilateral Semantics

- Solves the False Premise Problem
- First computational implementation of Bernard & Champollion's semantics
- Uses witness predicates for proper negation handling

### Imposition: Fine's Counterfactual Semantics

- Evaluates counterfactuals without possible worlds
- Based on primitive imposition relation between states
- Implements Fine's five frame constraints

### Bimodal: Temporal-Modal Logic

- Combines reasoning about time and possibility
- World histories as sequences of states
- Past, future, and modal operators

## Tools

- **Multiple Model Generation**: Set `'iterate': n` in settings to find up to n distinct models
- **Theory Comparison**: Define multiple theories in `semantic_theories` dictionary
- **Constraint Visualization**: Set `'print_constraints': True` to see Z3 constraints
- **Impossible State Analysis**: Set `'print_impossible': True` to examine impossible states
- **Z3 Output**: Set `'print_z3': True` for raw solver output
- **Model Saving**: Set `'save_output': True` to save results to file
- **Theory Maximization**: Set `'maximize': True` to compare theories systematically

For comprehensive guidance on theory comparison, avoiding circular imports, and advanced multi-theory setups, see **[Theory Comparison Guide](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/usage/COMPARE_THEORIES.md)**.

## Documentation

- **[GitHub Repository](https://github.com/benbrastmckie/ModelChecker)** - Full documentation and source code
- **[Development Guide](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/DEVELOPMENT.md)** - Contributing and development workflow
- **[Theory Documentation](https://github.com/benbrastmckie/ModelChecker/tree/master/Code/src/model_checker/theory_lib)** - Detailed theory specifications
- **[Academic Background](http://www.benbrastmckie.com/research#access)** - Theoretical foundations

## Contributing

We welcome contributions! See our [GitHub repository](https://github.com/benbrastmckie/ModelChecker) for:

- Contributing guidelines
- Development setup instructions
- Issue tracking
- Pull request procedures

## Academic Citations

If you use ModelChecker in your research, please cite:

- Brast-McKie, B. (2025). Model-Checker: A Programmatic Semantics Framework. [https://github.com/benbrastmckie/ModelChecker](https://github.com/benbrastmckie/ModelChecker)
- Brast-McKie, B. (2025). ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8), Journal of Philosophical Logic

## License

GPL-3.0 - see [LICENSE](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/LICENSE) for details.

## Support

- **Issues**: [GitHub Issues](https://github.com/benbrastmckie/ModelChecker/issues)
- **Discussions**: [GitHub Discussions](https://github.com/benbrastmckie/ModelChecker/discussions)
- **Documentation**: [Project Wiki](https://github.com/benbrastmckie/ModelChecker/wiki)

## Building and Testing Semantic Theories

ModelChecker provides a framework for developing, testing, and comparing semantic theories for logical operators. The current implementation focuses on the objective fragment of the language, with operators for:

- **Extensional logic**: Classical connectives (`∧`, `∨`, `¬`, `→`, `↔`)
- **Modal logic**: Necessity and possibility (`□`, `◇`)
- **Counterfactual logic**: Would and might counterfactuals (`□→`, `◇→`)
- **Constitutive logic**: Grounding, essence, and identity (`≤`, `⊑`, `≡`)

### Current State and Future Directions

The framework currently implements operators from the **objective language**, with normative and epistemic operators planned for future development. Each theory can be:

- **Built** using modular operator definitions
- **Tested** against known theorems and countermodels
- **Compared** with other theories to explore logical relationships

The **bimodal theory** provides a purely intensional treatment of temporal and modal operators, where worlds are functions from times to world states that respect a primitive task relation that specifies which transitions between states are possible.

Future work will integrate this temporal dimension into the Logos framework, completing the implementation of the **hyperintensional semantics** developed in Brast-McKie (2025).

### Research Applications

Use ModelChecker to:

1. **Explore logical principles**: Test which principles hold in different theories
2. **Find countermodels**: Discover why certain inferences fail
3. **Compare frameworks**: See how different semantic approaches handle the same operators
4. **Develop new theories**: Build and test semantic theories

The framework serves as a research tool for computational semantics and a testing ground for theories about modality, counterfactuals, grounding, and time.

---

[← Back to Project](https://github.com/benbrastmckie/ModelChecker) | [General Docs →](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/README.md) | [Technical Docs →](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/docs/README.md)
