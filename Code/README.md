# ModelChecker

[← GitHub Repository](https://github.com/benbrastmckie/ModelChecker) | [General Docs →](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/README.md) | [Technical Docs →](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/docs/README.md)

[![License: GPL-3.0](https://img.shields.io/badge/License-GPL%203.0-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![Python 3.8+](https://img.shields.io/badge/python-3.8+-blue.svg)](https://www.python.org/downloads/)
[![Z3 SMT Solver](https://img.shields.io/badge/Z3-SMT%20Solver-green.svg)](https://github.com/Z3Prover/z3)

A programmatic framework for implementing modular semantic theories powered by the Z3 SMT solver.

## Features

- **Automated Model Finding**: Discovers countermodels to invalid formulas and inferences
- **Modular Theory Architecture**: Mix and match logical operators for compatible theories
- **Hyperintensional Reasoning**: Distinguishes necessarily equivalent propositions
- **Multiple Model Generation**: Find diverse models satisfying a set of formulas
- **Theory Library**: Pre-built theories to test, adapt, and share with others

## Quick Start

Install the package:
```bash
pip install model-checker
```

For development:
```bash
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code
pip install -e .
```

**NixOS users**: Use `nix-shell` instead. See [NixOS Development](../Docs/installation/DEVELOPER_SETUP.md#nixos-development).

For complete installation guides, see [Installation Documentation](../Docs/installation/README.md).

Create a new logic project:

```bash
model-checker -l logos     # Hyperintensional logic
model-checker -l exclusion # Unilateral semantics
model-checker -l imposition # Fine's counterfactuals
model-checker -l bimodal   # Temporal-modal logic
```

## Programmatic Semantics

The ModelChecker is a theory-agnostic framework that allows researchers to implement, test, and share semantic theories for logical reasoning. The **[TheoryLib](https://github.com/benbrastmckie/ModelChecker/tree/master/Code/src/model_checker/theory_lib)** provides a collection of pre-built theories that can be used directly, modified for specific needs, or serve as templates for developing new theories. Users can upload their own theories to share with the community, fostering collaborative development of computational semantics.

### Logos: A Formal Language of Thought

The semantics for the **[Logos](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/theory_lib/logos/semantic.py)** provides a bilateral semantics for a formal language of thought, implementing hyperintensional distinctions with verifier and falsifier sets of states. This approach enables the framework to distinguish between propositions that are necessarily equivalent but differ in content which is critical for modeling fine-grained reasoning about counterfactuals and explanatory operators.

The Logos currently includes operators organized into modular subtheories:
- **[Extensional operators](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/theory_lib/logos/subtheories/extensional/README.md)**: Classical logical connectives (`∧`, `∨`, `¬`, `→`, `↔`, `⊤`, `⊥`)
- **[Modal operators](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/theory_lib/logos/subtheories/modal/README.md)**: Necessity and possibility (`□`, `◇`)
- **[Counterfactual operators](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/theory_lib/logos/subtheories/counterfactual/README.md)**: Would and might counterfactuals (`□→`, `◇→`)
- **[Constitutive operators](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/theory_lib/logos/subtheories/constitutive/README.md)**: Grounding, essence, and identity (`≤`, `⊑`, `≡`)
- **[Relevance operators](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/theory_lib/logos/subtheories/relevance/README.md)**: Content connection and relevance (`≼`)

The modular architecture allows users to load only the operators needed for their analysis, with automatic dependency resolution ensuring semantic coherence. Additional operators are actively being developed, expanding the theory's expressiveness for new applications in philosophy, logic, linguistics, and AI reasoning.

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

def max_compatible_part(self, state_x, state_w, state_y):
    """Tests if state_x is a maximal part of state_w compatible with state_y.
    Used to preserve maximal compatibility in counterfactual semantics."""
    z = z3.BitVec("max_part", self.N)
    return z3.And(
        self.is_part_of(state_x, state_w),
        self.compatible(state_x, state_y),
        ForAll(
            z,
            z3.Implies(
                z3.And(
                    self.is_part_of(z, state_w),
                    self.compatible(z, state_y),
                    self.is_part_of(state_x, z),
                ),
                state_x == z,
            ),
        ),
    )

def is_alternative(self, state_u, state_y, state_w):
    """Tests if state_u is a y-alternative world to w by imposing state_y on w.
    Alternative worlds contain y and maximal compatible parts of w."""
    z = z3.BitVec("alt_z", self.N)
    return z3.And(
        self.is_world(state_u),
        self.is_part_of(state_y, state_u),
        Exists(
            [z],
            z3.And(
                self.is_part_of(z, state_u),
                self.max_compatible_part(z, state_w, state_y)
            )
        )
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

This implementation captures the hyperintensional nature of counterfactuals where quantifying over alternative worlds depend on which specific verifier of the antecedent we consider.

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

This shows that "If A were true then C" doesn't entail "If A and B were true then C" since the additional condition B can change which alternatives are relevant to quantify over. For instance, just because the match would light if it were struck, it does not follow that the match would light if it were struck when wet.

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
- Sensitive to differences in subject-matter via verifier/falsifier sets
- Distinguishes necessarily equivalent propositions

### Exclusion: Unilateral Semantics

- Implementation of Bernard & Champollion's unilatiral semantics
- Uses witness predicates for proper negation handling

### Imposition: Fine's Counterfactual Semantics

- Evaluates counterfactuals without taking possible worlds to be primitive
- Based on primitive imposition relation between states
- Implements Fine's five frame constraints

### Bimodal: Temporal-Modal Logic

- Combines reasoning about time and possibility
- World histories as functions from times to world states
- Includes past, future, and modal operators

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

Contributions are welcome! See our [GitHub repository](https://github.com/benbrastmckie/ModelChecker) for:

- Contributing guidelines
- Development setup instructions
- Issue tracking
- Pull request procedures

## Academic Citations

If you use ModelChecker in your research, please cite:

- Brast-McKie, B. (2025). Model-Checker: A Programmatic Semantics Framework. [https://github.com/benbrastmckie/ModelChecker](https://github.com/benbrastmckie/ModelChecker)

The theories implemented with the ModelChecker are developed in:

- Brast-McKie, B. (2025). ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8), Journal of Philosophical Logic
- Brast-McKie, B. (draft). ["The Construction of Possible Worlds"](http://www.benbrastmckie.com/wp-content/uploads/2025/11/possible_worlds.pdf).

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

The framework currently implements operators from an objective language with transparent operators., with normative and epistemic operators planned for future development. Each theory can be:

- **Built** using modular operator definitions
- **Tested** against known theorems and countermodels
- **Compared** with other theories to explore logical relationships

The **bimodal theory** provides a purely intensional treatment of temporal and modal operators, where worlds are functions from times to world states that respect a primitive task relation that specifies which transitions between states are possible. This theory is elaborated and defended in [Brast-McKie (draft)](http://www.benbrastmckie.com/wp-content/uploads/2025/11/possible_worlds.pdf).

Future work will integrate this temporal dimension into the Logos framework, completing the implementation of the hyperintensional semantics developed for tensed counterfactuals in [Brast-McKie (2025)](https://link.springer.com/article/10.1007/s10992-025-09793-8).

### Research Applications

Use ModelChecker to:

1. **Explore logical principles**: Test which principles hold in different theories
2. **Find countermodels**: Discover why certain inferences fail
3. **Compare frameworks**: See how different semantic approaches handle the same operators
4. **Develop new theories**: Build and test semantic theories

The framework serves as a research tool for computational semantics and a testing ground for theories about modality, counterfactuals, explanation, and time.

---

[← Back to Project](https://github.com/benbrastmckie/ModelChecker) | [General Docs →](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/README.md) | [Technical Docs →](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/docs/README.md)
