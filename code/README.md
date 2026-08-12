# ModelChecker

[![License: GPL-3.0](https://img.shields.io/badge/License-GPL%203.0-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![Python 3.10+](https://img.shields.io/badge/python-3.10+-blue.svg)](https://www.python.org/downloads/)
[![Z3 SMT Solver](https://img.shields.io/badge/Z3-SMT%20Solver-green.svg)](https://github.com/Z3Prover/z3)

A programmatic framework for implementing and comparing modular semantic theories, powered by the
Z3 SMT solver.

ModelChecker turns a semantic theory into executable constraints. Given a set of premises and
conclusions, it searches for a countermodel — a model satisfying the premises while falsifying the
conclusions — and prints that model in readable form. Where no countermodel exists, the inference
is valid in the theory under test, up to the finite state space searched.

The framework is theory-agnostic. Four semantic theories ship with the package, and new theories
can be written, tested, and shared using the same interfaces.

- **[Repository](https://github.com/benbrastmckie/ModelChecker)**
- **[User Documentation](https://github.com/benbrastmckie/ModelChecker/blob/master/docs/README.md)**
- **[Technical Documentation](https://github.com/benbrastmckie/ModelChecker/blob/master/code/docs/README.md)**

## Features

- **Automated countermodel search** — discovers countermodels to invalid inferences, or reports
  their absence
- **Modular operator architecture** — load only the operators an analysis needs, with dependency
  resolution across subtheories
- **Hyperintensional semantics** — distinguishes necessarily equivalent propositions by their
  verifier and falsifier sets
- **Model iteration** — enumerate multiple non-isomorphic models for a single example
- **Theory comparison** — run the same inference against several theories side by side
- **Dual solver backends** — Z3 by default, with optional cvc5
- **Theory library** — four ready-to-use theories that double as templates for new ones

## Installation

```bash
pip install model-checker
```

For notebook integration:

```bash
pip install model-checker[jupyter]
```

The optional cvc5 backend is a separate package:

```bash
pip install cvc5
```

For development:

```bash
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/code
pip install -e .
```

Requires Python 3.10 or later. **NixOS users** should use `nix-shell` rather than `pip`; see
[Developer Setup](https://github.com/benbrastmckie/ModelChecker/blob/master/docs/installation/DEVELOPER_SETUP.md#nixos-development).
Full instructions are in the
[Installation Documentation](https://github.com/benbrastmckie/ModelChecker/blob/master/docs/installation/README.md).

## Quick Start

Generate a project preloaded with a theory and its examples:

```bash
model-checker -l logos       # hyperintensional truthmaker semantics
model-checker -l exclusion   # unilateral semantics
model-checker -l imposition  # Fine's counterfactual semantics
model-checker -l bimodal     # temporal-modal logic
```

Then run an examples module:

```bash
model-checker examples.py
```

Each example is a triple of premises, conclusions, and settings. This one tests counterfactual
antecedent strengthening: given that `A` is false and that `C` would hold if `A` did, must `C`
also hold if `A` and `B` both did?

```python
CF_CM_1_premises = ['\\neg A', '(A \\boxright C)']
CF_CM_1_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_1_settings = {
    'N': 4,              # bit-width: the state space has 2^N states
    'contingent': True,  # atomic propositions must be contingent
    'iterate': 2,        # find two non-isomorphic models
    'max_time': 10,      # solver timeout in seconds
}
```

It is not valid, and the framework says so by exhibiting a countermodel (abridged below; the
particular model found varies between runs):

```
EXAMPLE CF_CM_1: there is a countermodel.

Premises:
1. \neg A
2. (A \boxright C)

Conclusion:
3. ((A \wedge B) \boxright C)

State Space:
  #b0000 = □
  #b0001 = a
  #b0010 = b
  #b0011 = a.b (world)
  #b0100 = c
  #b0101 = a.c (world)
  #b0110 = b.c (impossible)
  #b0111 = a.b.c (impossible)
  #b1000 = d
  #b1001 = a.d (impossible)
  #b1010 = b.d (world)
  #b1011 = a.b.d (impossible)
  #b1100 = c.d (world)
  #b1101 = a.c.d (impossible)
  #b1110 = b.c.d (impossible)
  #b1111 = a.b.c.d (impossible)

The evaluation world is: b.d

INTERPRETED PREMISES:

...
2.  |(A \boxright C)| = < {b.d, c.d}, {a.b, a.c} >  (True in b.d)
      |A|-alternatives to b.d = {c.d}
        |C| = < {b, b.d, d}, {a.c} >  (True in c.d)

INTERPRETED CONCLUSION:

3.  |((A \wedge B) \boxright C)| = < {}, {a.b, a.c, b.d, c.d} >  (False in b.d)
      |(A \wedge B)|-alternatives to b.d = {a.c}
        |C| = < {b, b.d, d}, {a.c} >  (False in a.c)
```

Strengthening the antecedent changes which worlds are relevant to the evaluation. A match would
light if it were struck; it does not follow that it would light if it were struck while wet.

Propositions print as `< verifiers, falsifiers >`, and states as fusions of atomic states, so
`a.c` is the fusion of `a` and `c`. Formulas use LaTeX commands (`\boxright`, `\wedge`), which are
also how they are written in source; see the
[Formula Reference](https://github.com/benbrastmckie/ModelChecker/blob/master/code/docs/specific/FORMULAS.md).

## Semantic Theories

| Theory | Semantics | Operators |
|--------|-----------|-----------|
| **[Logos](https://github.com/benbrastmckie/ModelChecker/tree/master/code/src/model_checker/theory_lib/logos)** | Hyperintensional truthmaker semantics with bilateral verifier/falsifier sets | 18 |
| **[Exclusion](https://github.com/benbrastmckie/ModelChecker/tree/master/code/src/model_checker/theory_lib/exclusion)** | Bernard and Champollion's unilateral semantics, where negation arises from a primitive exclusion relation | 4 |
| **[Imposition](https://github.com/benbrastmckie/ModelChecker/tree/master/code/src/model_checker/theory_lib/imposition)** | Kit Fine's counterfactual semantics, using a primitive imposition relation on states | 13 |
| **[Bimodal](https://github.com/benbrastmckie/ModelChecker/tree/master/code/src/model_checker/theory_lib/bimodal)** | Temporal-modal logic where worlds are histories mapping times to world states | 17 |

The **[Theory Library](https://github.com/benbrastmckie/ModelChecker/tree/master/code/src/model_checker/theory_lib)**
documents how theories are registered and how to contribute a new one.

### The Logos Theory

The Logos provides a bilateral hyperintensional semantics for a formal language of thought. States
are drawn from a finite mereology, propositions are pairs of verifier and falsifier sets, and
necessarily equivalent propositions may differ in subject matter. Its operators are organized into
four subtheories that can be loaded independently:

| Subtheory | Operators |
|-----------|-----------|
| **[Extensional](https://github.com/benbrastmckie/ModelChecker/blob/master/code/src/model_checker/theory_lib/logos/subtheories/extensional/README.md)** | `\neg` (¬), `\wedge` (∧), `\vee` (∨), `\rightarrow` (→), `\leftrightarrow` (↔), `\top` (⊤), `\bot` (⊥) |
| **[Modal](https://github.com/benbrastmckie/ModelChecker/blob/master/code/src/model_checker/theory_lib/logos/subtheories/modal/README.md)** | `\Box` (□), `\Diamond` (◇), `\CFBox`, `\CFDiamond` |
| **[Constitutive](https://github.com/benbrastmckie/ModelChecker/blob/master/code/src/model_checker/theory_lib/logos/subtheories/constitutive/README.md)** | `\leq` (≤, ground), `\sqsubseteq` (⊑, essence), `\equiv` (≡, identity), `\preceq` (≼, relevance), `\Rightarrow` (reduction) |
| **[Counterfactual](https://github.com/benbrastmckie/ModelChecker/blob/master/code/src/model_checker/theory_lib/logos/subtheories/counterfactual/README.md)** | `\boxright` (□→, would), `\diamondright` (◇→, might) |

Several operators are defined rather than primitive: `A ◇→ B` abbreviates `¬(A □→ ¬B)`,
`\CFBox A` abbreviates `⊤ □→ A`, `\CFDiamond A` abbreviates `⊤ ◇→ A`, and `A \Rightarrow B` is the
conjunction of ground and essence. Additional operators are under active development.

## How Theories Are Defined

A theory supplies four things: a semantics class, operator classes, a proposition class, and a
model structure. The semantics defines the primitives and frame constraints; each operator defines
its own truth, falsity, verification, and falsification conditions as Z3 constraints.

**Semantic primitives.**
[`LogosSemantics`](https://github.com/benbrastmckie/ModelChecker/blob/master/code/src/model_checker/theory_lib/logos/semantic/core.py)
extends
[`SemanticDefaults`](https://github.com/benbrastmckie/ModelChecker/blob/master/code/src/model_checker/models/semantic.py)
and declares three Z3 functions — `verify` and `falsify`, relating states to sentence letters, and
`possible`, marking which states are possible. States are bit vectors of width `N`, so fusion is
bitwise OR and parthood is fusion-identity, both inherited from `SemanticDefaults`. Frame
constraints require that possibility is downward closed under parthood and that the evaluation
world is a world — a possible state that is maximal with respect to compatibility.

**Derived relations.** On that basis `LogosSemantics` builds `compatible`, `maximal`, `is_world`,
`max_compatible_part`, and `is_alternative`. The last two carry the counterfactual semantics: an
alternative world to `w` under `y` contains `y` together with a maximal part of `w` compatible
with it.

**Recursive evaluation.** `true_at`, `false_at`, `extended_verify`, and `extended_falsify` bottom
out on sentence letters and otherwise delegate to the operator at the root of the sentence.

**Operators.** The
[counterfactual operators](https://github.com/benbrastmckie/ModelChecker/blob/master/code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py)
illustrate the pattern. `A □→ B` is true at `w` when, for every verifier `x` of `A` and every
`x`-alternative `u` to `w`, `B` is true at `u`; it is false at `w` when some verifier `x` of `A`
has an `x`-alternative `u` at which `B` is false. Because the alternatives quantified over depend
on which verifier of the antecedent is considered, the operator is hyperintensional: substituting
a necessarily equivalent antecedent can change the result.

Full contracts are in the
[Theory Architecture](https://github.com/benbrastmckie/ModelChecker/blob/master/code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md)
guide.

## Configuration

Settings are set per example in the `settings` dictionary, and may be overridden by command-line
flags.

| Setting | Flag | Effect |
|---------|------|--------|
| `N` | — | Bit-width for states; the space contains 2^N states |
| `max_time` | — | Solver timeout in seconds |
| `iterate` | — | Number of non-isomorphic models to find |
| `contingent` | `-c` | Require atomic propositions to be contingent |
| `non_empty` | `-e` | Require non-empty verifier and falsifier sets |
| `non_null` | `-n` | Exclude the null state from verifying or falsifying |
| `disjoint` | `-d` | Require atomic propositions to be disjoint; the exact constraint is theory-specific |
| `maximize` | `-m` | Compare theories on the same examples |
| `solver` | `--z3` / `--cvc5` | Select the SMT backend |
| `print_impossible` | `-i` | Include impossible states in the display |
| `print_constraints` | `-p` | Show the constraints given to the solver |
| `print_z3` | `-z` | Show raw solver output |
| `save_output` | `-s` | Save results; `-s markdown` or `-s json` selects a format |
| `sequential` | `-q` | Prompt to save each model individually |
| `align_vertically` | `-a` | Display temporal models top to bottom |

Run `model-checker --help` for the full command-line interface. For theory comparison and
multi-theory setups, see the
[Tools Guide](https://github.com/benbrastmckie/ModelChecker/blob/master/docs/usage/TOOLS.md).

## Development

Clone the repository and work from the `code/` directory. These scripts do not require the package
to be installed:

| Script | Purpose |
|--------|---------|
| `./dev_cli.py examples.py` | Run the CLI against local source rather than the installed package |
| `./run_tests.py` | Unified runner for example, unit, and package tests |
| `./run_jupyter.sh` | Start Jupyter with ModelChecker available, inside `nix-shell` |
| `./jupyter_link.py` | Symlink local source into user site-packages for notebook use |

`dev_cli.py` puts the local `src/` directory at the front of `sys.path`, so edits take effect
immediately; it also accepts `--iso-debug` for isomorphism debugging. `run_tests.py` auto-detects
whether a target is a theory or a component:

```bash
./run_tests.py                       # everything
./run_tests.py --examples            # example tests only
./run_tests.py --unit logos          # unit tests for the logos theory
./run_tests.py logos modal           # a single subtheory
./run_tests.py iterate builder       # multiple components
```

Tests can also be run directly with pytest:

```bash
PYTHONPATH=src pytest tests/ -v
```

Contributions are welcome. See the
[Development Guide](https://github.com/benbrastmckie/ModelChecker/blob/master/code/docs/development/README.md)
for workflow, coding standards, and testing requirements.

## Documentation

- **[User Documentation](https://github.com/benbrastmckie/ModelChecker/blob/master/docs/README.md)** — installation, usage, and guides
- **[Technical Documentation](https://github.com/benbrastmckie/ModelChecker/blob/master/code/docs/README.md)** — architecture, standards, and contracts
- **[Theory Library](https://github.com/benbrastmckie/ModelChecker/tree/master/code/src/model_checker/theory_lib)** — theory specifications and the contract for new theories
- **[Academic Background](http://www.benbrastmckie.com/research#access)** — related research

## Citation

If you use ModelChecker in your research, please cite:

> Brast-McKie, B. (2025). *Model-Checker: A Programmatic Semantics Framework.*
> https://github.com/benbrastmckie/ModelChecker

The theories implemented in the framework are developed in:

- Brast-McKie, B. (draft). ["The Construction of Possible Worlds"](http://www.benbrastmckie.com/wp-content/uploads/2025/11/possible_worlds.pdf).
- Brast-McKie, B. (2025). ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8). *Journal of Philosophical Logic*.
- Brast-McKie, B. (2021). ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w). *Journal of Philosophical Logic*, 50, 1471–1503.

## Support

- **[Issues](https://github.com/benbrastmckie/ModelChecker/issues)** — bug reports and feature requests
- **[Discussions](https://github.com/benbrastmckie/ModelChecker/discussions)** — questions and ideas

## License

GPL-3.0. See [LICENSE](https://github.com/benbrastmckie/ModelChecker/blob/master/code/LICENSE).
