# Bimodal Logic User Guide

## Overview

The bimodal theory implements temporal-modal logic, combining reasoning about time and
possibility, by **searching for witness-family certificates** over discrete (ℤ) time. A
countermodel is not a fixed finite structure you configure the size of; it is a small, checkable
certificate — a box guess plus a family of labelled bi-infinite lassos — that denotes an infinite
model by construction. See `../README.md`'s "The Certificate Search" and `ARCHITECTURE.md` for the
full design; this guide is a practical, task-oriented walkthrough.

## Key Features

- **Temporal Operators**: `\Future`/`\Past` (all future/past times) and `\Until`/`\Since`
  (guarded eventualities) for temporal reasoning
- **Modal Operators**: `\Box`/`\Diamond` for necessity/possibility, decided by a box guess plus,
  when guessed false, an explicit witness lasso
- **Extensional Base**: full support for classical propositional logic
- **Certified Models**: every reported certificate denotes an infinite model whose four defining
  properties (local coherence, fulfilment, box faithfulness, target) hold by construction, and are
  independently re-verified by a pure-Python checker before being reported
- **Never claims validity**: an unsuccessful search is always reported as "no certificate found
  within the configured bounds," never as a proof

## Available Operators

The bimodal theory provides operators for both temporal and modal reasoning (LaTeX names, as used
in formula strings):

### Extensional Operators
- **`\neg`** (negation): classical negation
- **`\wedge`** (conjunction): classical conjunction
- **`\vee`** (disjunction): classical disjunction
- **`\rightarrow`** (conditional): material conditional (defined)
- **`\leftrightarrow`** (biconditional): material biconditional (defined)

### Modal Operators
- **`\Box`** (necessity): "it is necessary that..." — true when the box guess for the argument is
  `true`
- **`\Diamond`** (possibility): "it is possible that..." (defined, via `\neg \Box \neg`)

### Temporal Operators
- **`\Future`** (all future): "it will always be the case that..."
- **`\Past`** (all past): "it has always been the case that..."
- **`\Until`** (guarded eventuality): `g \Until e` — guard-first internally; the paper's guarded
  until
- **`\Since`** (guarded past eventuality): the backward mirror of `\Until`
- **`\future`**/**`\past`** (defined, some future/past time), **`\next`**/**`\prev`** (defined,
  the immediately following/preceding position)

### Extremal Operators
- **`\top`** (top): logical truth (defined)
- **`\bot`** (bottom): logical falsehood (primitive)

## Understanding Certificate Search

### Lassos and Positions

A certificate search produces:
- **Lassos**: labelled bi-infinite histories, each `(back)^ω | mid | (fwd)^ω` — a periodic
  backward segment, a finite middle segment, and a periodic forward segment. Position `0` starts
  `mid`. They print as `Histories:` rows of `(t:atoms)` states joined by `⟹`, one row per lasso
  (`… (-2:A) ⟹ (-1:A) | (0:A) | (+1:A) ⟹ (+2:A) …`; see `../README.md`'s "Sample Output").
- **A box guess table**: for each boxed subformula in the closure, whether it is `true` (holds at
  every position of every lasso) or `false` (fails at some position of some witness lasso)
- **A target position**: the position on the main lasso (`L0`) where every premise holds and no
  conclusion does

### Settings That Bound the Search

- `back`/`fwd`: the *exact* cyclic periods of the lasso's back/fwd segments, not maxima — a
  family whose period is `p` is representable only when `p` divides the configured length
- `mid`: a genuine maximum, the one direct-read segment length
- `max_witnesses`: an optional cap on distinct witness lassos

See [SETTINGS.md](SETTINGS.md) for the full exact-period explanation and the operative rule for
choosing `back`/`fwd`.

There is no analogue of the retired `N` (a world count) or `M` (a window of times): the certified
model is always infinite once a certificate is found; these settings only bound the *search*.

## Formula Examples

### Pure Temporal Reasoning

```python
premises = ["\\Box p"]
conclusions = ["\\Future \\Box p"]
settings = {"back": 2, "mid": 1, "fwd": 2}

# What is necessary now is necessarily always going to be necessary (the paper's MF axiom)
```

### Pure Modal Reasoning

```python
premises = ["\\Box p"]
conclusions = ["\\neg \\Diamond \\neg p"]
settings = {"back": 2, "mid": 1, "fwd": 2}

# What is necessary is not possibly false
```

### Combined Temporal-Modal

```python
premises = ["\\Box \\Future p"]
conclusions = ["\\Future \\Box p"]
settings = {"back": 2, "mid": 1, "fwd": 2, "expectation": True}

# It is necessary that p will always be true vs. it will (at every future time) be necessary --
# these come apart: expect a certificate
```

### Complex Interactions

```python
premises = ["\\Past p", "\\Future q"]
conclusions = ["(\\Past p \\wedge \\Future q)"]
settings = {"back": 2, "mid": 1, "fwd": 2}

# Combining past and future information
```

## Working with Examples

### Accessing Built-in Examples

```python
from model_checker.theory_lib.bimodal import get_examples, get_test_examples

# Get the curated 25-example demonstration set
examples = get_examples()
print(f"Available examples: {list(examples.keys())}")

# Get the full 53-example test suite
test_examples = get_test_examples()
print(f"Test examples: {len(test_examples)} total")
```

### Running Specific Examples

```python
from model_checker import BuildExample, ModelConstraints
from model_checker.theory_lib.bimodal import get_theory, get_examples

theory = get_theory()
examples = get_examples()

example_case = examples["BM_CM_1"]
example = BuildExample("bimodal_test", theory, example_case)
result = example.check_result()

print(f"BM_CM_1 result: {result['model_found']}")
```

## Settings and Configuration

### Essential Settings

```python
settings = {
    "back": 2,           # Exact back-segment period (not a maximum; see SETTINGS.md)
    "mid": 1,            # Maximum mid-segment length
    "fwd": 2,             # Exact fwd-segment period (not a maximum; see SETTINGS.md)
    "max_time": 10,      # Solver timeout
    "max_witnesses": None,  # Uncapped witness-lasso allocation
}
```

### Bimodal-Specific Considerations

- **`back`/`fwd`**: choose these as a multiple of the period a formula's refutation genuinely
  needs, rather than simply raising them — they are exact cyclic periods, not maxima, so a larger
  non-multiple can lose a countermodel a smaller value found (see [SETTINGS.md](SETTINGS.md)).
  `mid` may be raised freely. The theory's own 53 examples, including previously-excluded ones (the
  paper's MF axiom, the BX7 linearity theorems), all decide at the defaults (`back=2, mid=1,
  fwd=2`) in well under 50ms.
- **`max_witnesses`**: only lower this to bound cost on formulas with many boxed subformulas — an
  overly small cap makes the search under-complete for that formula, not merely slower.
- **`verify`**: controls whether a reported countermodel is independently checked by a standalone
  Lean-built binary (in addition to the mandatory Python re-check, which always runs). No Lean
  toolchain is required to use it — only a checker binary; see
  [SETTINGS.md's "Certificate Verification" section](SETTINGS.md#certificate-verification) for
  the three values, the three rendered output states, and how to obtain a checker.

For detailed settings documentation, see [SETTINGS.md](SETTINGS.md).

## Model Iteration

Explore multiple certificates for bimodal examples:

```python
from model_checker.theory_lib.bimodal import iterate_example

example = BuildExample("test", theory, example_case)
models = iterate_example(example, max_iterations=3)

print(f"Found {len(models)} certificates")
for i, model in enumerate(models):
    print(f"Certificate {i+1}: {model.z3_model_status}")
    model.print_certificate()
```

Successive certificates are guaranteed to differ in at least one label bit or box guess (an exact
blocking clause), **not** guaranteed to be non-isomorphic. Also, as of this writing, requesting
more than one certificate (`max_iterations > 1` / `iterate: N > 1`) currently raises an
`AttributeError` through a pre-existing, reproduced shared-framework gap — use `max_iterations=1`
(the default) until it is fixed. See [ITERATE.md](ITERATE.md) for the full story.

## Common Use Cases

### 1. Temporal Logic Validation

```python
example_case = [
    [],
    ["(\\future \\future p \\rightarrow \\future p)"],  # Future-operator transitivity
    {"back": 2, "mid": 1, "fwd": 2, "expectation": False}
]
```

### 2. Modal Logic with Time

```python
example_case = [
    ["\\Box p"],
    ["\\Future \\Box p"],
    {"back": 2, "mid": 1, "fwd": 2}
]
```

### 3. Temporal-Modal Interactions

```python
example_case = [
    ["\\Box \\Future p"],
    ["\\Future \\Box p"],
    {"back": 2, "mid": 1, "fwd": 2, "expectation": True}  # These come apart!
]
```

### 4. Dynamic System Modeling

```python
example_case = [
    ["p", "\\next \\neg p", "\\next \\next p"],  # p oscillates: true, false, true
    ["\\Diamond \\future p"],
    {"back": 2, "mid": 2, "fwd": 2}
]
```

## Advanced Topics

### Lasso Semantics

A certificate's carrier is the disjoint union of its lassos' `(index, position)` points, with the
shift `(i, t) ⇒_x (i, t+x)` as the task relation for every integer `x`:

```
L0: ... {A} {A} | {A} | {A} {A} ...     (main lasso: A holds throughout)
L1: ... {}  {}  | {}  | {}  {}  ...     (witness lasso: A fails throughout)
```

Each lasso, together with every one of its integer translates, is one possible world history.
`\Box A` ranges over exactly these certified histories — see `ARCHITECTURE.md`'s "The (SOUND)
Theorem" for why this correspondence is exact, not approximate.

### Evaluation Points

Formulas are evaluated at `(lasso, position)` pairs, not `(world, time)` pairs:
- `\Future p` at `(L, t)`: `p`'s label bit is set at every position strictly after `t` on `L`
- `\Box p` at `(L, t)`: the box guess for `p` is `true` — equivalently, `p`'s label bit is set at
  every position of every lasso

## Tips and Best Practices

### Performance
- Start with the default segment lengths (`back=2, mid=1, fwd=2`). If a specific formula's
  refutation needs a longer period, choose `back`/`fwd` as a multiple of that period rather than
  simply raising them (see [SETTINGS.md](SETTINGS.md)); `mid` may be raised freely.
- The search is quantifier-free, so solver cost scales with `back + mid + fwd` and the closure
  size, not with an exponential state space — there is no `N`/`M` product to worry about.

### Formula Construction
- Use `\Future`/`\Past`/`\Until`/`\Since` for temporal reasoning; `\Until`'s arguments are
  guard-first (`g \Until e`), matching the paper's own convention.
- `\Box`/`\Diamond` range over the whole certified history family, not over a per-time-point set
  of alternatives.

### Model Interpretation
- Check `model.certificate.bx_of(formula)` to see a box's guessed value directly.
- Use iteration to explore alternative label/guess assignments; a certificate that is only a
  rotation of an earlier lasso's `back`/`fwd` segments, or a permutation of its witness lassos,
  is treated as the same model and will not be reported again (see [ITERATE.md](ITERATE.md)).
- Pay attention to the distinction between `\Box \Future p` and `\Future \Box p`
  (`MF_MODAL_FUTURE_TH` is the paper's own axiom relating the two).

### Debugging
- Start with pure temporal or pure modal formulas.
- Use `print_constraints=True` to inspect the raw Z3 constraint set.
- Use `certificate.recheck(family, premises, conclusions, target_time)` directly, outside a Z3
  solve, to debug a specific certificate.

## Common Patterns

### Temporal Sequences

```python
"(p \\wedge (\\next q \\wedge \\next \\next r))"   # p now, q next, r after that
"(p \\wedge \\next \\neg p \\wedge \\next \\next p)"  # p oscillates
"\\Diamond \\future p"                              # Eventually p will be true
```

### Modal Combinations

```python
"\\Box \\Diamond p"    # It's necessary that p is possible
"\\Diamond \\Box p"    # It's possible that p is necessary
"\\Box \\Future p"     # It's necessary that p will always be true
```

### Complex Interactions

```python
"(\\Past \\Box p \\wedge \\Future \\Diamond q)"        # p was always necessary, q will be possible
"(\\Box p \\wedge \\Future \\Diamond \\neg p)"          # Necessary now, but possibly not later
```

## Theoretical Background

The bimodal theory's certificate search targets the source paper's task-semantics
(`app:TaskSemantics`, `def:BL-semantics`): world histories are lawful sequences of world states
evolving over discrete time, sentence letters are assigned at world states alone (times are
exogenous), and every history has infinite temporal extent in both directions. A certificate
denotes such a model directly — see `ARCHITECTURE.md`'s "The (SOUND) Theorem" and `ADEQUACY.md`
for the full correspondence, including the four Lean-proved lemmas that establish it.

## Troubleshooting

### Common Issues

**No certificate found when one is expected**:
- The refutation may need a longer periodic pattern than the defaults allow. Choose `back`/`fwd`
  as a multiple of the period needed (they are exact periods, not maxima — a larger non-multiple
  can lose a countermodel a smaller value found) or try several candidate lengths; raise `mid`
  freely. See [SETTINGS.md](SETTINGS.md) for the full explanation.
- Raise `max_witnesses` if the formula has several boxed subformulas.

**Unexpected "no certificate" results**:
- Remember this theory never asserts validity (D8): "no certificate found within the configured
  bounds" is a bounded-search fact, not a proof — see `ARCHITECTURE.md`.
- Check the distinction between `\Box \Future p` and `\Future \Box p`.

**Solver timeouts**:
- Increase `max_time`.
- The search is quantifier-free and typically fast (well under 50ms for every one of the theory's
  53 examples at the default segment lengths); a timeout usually indicates segment lengths set far
  larger than the formula needs, not an inherent hardness.

### Getting Help

- Review `examples.py` for 53 worked examples across every operator combination.
- Check [ARCHITECTURE.md](ARCHITECTURE.md) for the certificate search's technical details and the
  (SOUND) theorem.
- Check [ADEQUACY.md](ADEQUACY.md) for the full soundness proof and the open adequacy direction.
- Use model iteration to explore alternative certificates.

## Integration with Other Theories

Compare bimodal results with other approaches:

```python
from model_checker.theory_lib.bimodal.examples import semantic_theories

for theory_name, theory_config in semantic_theories.items():
    example = BuildExample(f"test_{theory_name}", theory_config, example_case)
    result = example.check_result()
    print(f"{theory_name}: {result['model_found']}")
```

## Further Reading

- **`../README.md`**: overview, settings, the certificate search, and sample output
- **`ARCHITECTURE.md`**: the two-phase constraint emission, the (SOUND) theorem, and the retired
  designs this theory replaced
- **`ADEQUACY.md`**: the full soundness proof, the Lean citation table, and the open adequacy
  (completeness) direction
- **`ITERATE.md`**: model iteration and its isomorphism-rejection scope

---

**Navigation**: [README](../README.md) | [Architecture](ARCHITECTURE.md) | [Adequacy](ADEQUACY.md)
| [Settings](SETTINGS.md) | [API Reference](API_REFERENCE.md) | [Iteration](ITERATE.md)
