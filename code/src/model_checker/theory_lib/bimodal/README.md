# Bimodal Logic Implementation

## Table of Contents

- [Overview](#overview)
  - [Package Contents](#package-contents)
- [Basic Usage](#basic-usage)
  - [Settings](#settings)
  - [Example Structure](#example-structure)
  - [Running Examples](#running-examples)
    - [1. From the Command Line](#1-from-the-command-line)
    - [2. In VSCodium/VSCode](#2-in-vscodiumvscode)
    - [3. In Development Mode](#3-in-development-mode)
    - [4. Using the API](#4-using-the-api)
  - [Theory Configuration](#theory-configuration)
- [Key Classes](#key-classes)
  - [BimodalSemantics](#bimodalsemantics)
  - [BimodalProposition](#bimodalproposition)
  - [BimodalStructure](#bimodalstructure)
- [Bimodal Language](#bimodal-language)
  - [Necessity Operator](#necessity-operator-box)
  - [Future Operator](#future-operator-future)
  - [Past Operator](#past-operator-past)
  - [Until and Since Operators](#until-and-since-operators)
- [Important Theorems](#important-theorems)
- [The Certificate Search](#the-certificate-search)
  - [What Is Searched](#what-is-searched)
  - [The Certified Model](#the-certified-model)
  - [Sample Output](#sample-output)
- [Model Iteration](#model-iteration)
- [Development Status](#development-status)
- [Known Limitations](#known-limitations)
- [Adequacy](#adequacy)
- [References](#references)

## Overview

The bimodal theory provides **17 operators** (9 primitive, 8 defined) across three categories,
with **53 example formulas** covering extensional, modal, tense, and bimodal (BX-axiom)
fragments:

1. **Temporal operators** (4 primitive: `\Future`, `\Past`, `\Until`, `\Since`; 2 defined duals):
   for reasoning about different times (past and future)
2. **Modal operators** (1 primitive: `\Box`; 1 defined dual `\Diamond`): for reasoning about
   different world histories
3. **Extensional operators** (4 primitive: `\neg`, `\wedge`, `\vee`, `\bot`; 4 defined: `\rightarrow`,
   `\leftrightarrow`, `\top`, plus `\Next`/`\Prev` duals): for classical reasoning

This implementation searches for **witness-family certificates** over discrete (ℤ) time: a
countermodel to an inference is presented as a finite, checkable object — a Boolean guess for
every boxed subformula plus a small family of labelled bi-infinite lassos — that denotes an
infinite **certified `ShiftSet` model** by construction, not by an assertion the solver is asked
to trust. This is a from-scratch redesign, not a repair, of an earlier window-and-abundance Z3
encoding; see [The Certificate Search](#the-certificate-search) and `docs/ARCHITECTURE.md` for
why, and `docs/ADEQUACY.md` for the full soundness proof.

Within that design:

- World histories are the certified lassos and their integer translates, not finite arrays.
- Sentence letters are assigned truth values at `(lasso, position)` points; a certificate's label
  at each position fixes exactly the closure members true there.
- World histories follow lawful (shift) transitions between consecutive positions by
  construction — no separate task-relation axiom is asserted.
- Times are the integers `ℤ`; a lasso's label is finite data (`back`/`mid`/`fwd` segments) but
  denotes an infinite bi-directional history.
- `\Box` ranges over exactly the certified histories (every lasso and every one of its integer
  translates) — never over a finite enumerated set and never over a bounded window.
- The search never reports validity: "no certificate found within the configured segment
  lengths" is the only verdict an unsatisfiable search can produce.

### Package Contents

This package includes the following core modules:

- `semantic/core.py`: `BimodalSemantics` — settings, the Z3 variable layer, and the two-phase
  constraint emission that discharges (C1)-(C4)
- `semantic/model.py`: `BimodalStructure` — certificate extraction, the independent pure-Python
  re-check, and printing
- `semantic/proposition.py`: `BimodalProposition` — truth-value lookups against a found
  certificate's labels
- `semantic/formula.py`: the Lean-mirroring `Formula` ADT (`atom | bot | imp | box | untl |
  snce`), subformula closure, sentence translation, and the JSON wire codec
- `semantic/certificate.py`: `LabelledLasso`/`WitnessFamily`, the certificate wire-format writer,
  and the independent pure-Python re-checker (`recheck`)
- `semantic/witness_registry.py`: the quantifier-free Z3 variable layer (label bits, box guesses,
  witness-lasso allocation)
- `semantic/witness_constraints.py`: the quantifier-free constraint generators for all four
  certificate conditions
- `operators.py`: implements all primitive and defined logical operators as label-lookup
  generators
- `iterate.py`: `BimodalModelIterator` — iteration by blocking clauses on labels and guesses
- `examples.py`: 53 example formulas for testing and demonstration
- `__init__.py`: exposes package definitions for external use

## Key Classes

### BimodalSemantics

`BimodalSemantics` (`semantic/core.py`) owns the certificate search's settings and its
quantifier-free variable/constraint layer:

- **Settings**: `back`/`fwd` (exact cyclic periods of the lasso's back/fwd segments, not
  maxima) and `mid` (a genuine maximum, direct-read segment length), plus `max_witnesses` (an
  optional cap on distinct witness lassos), in place of the retired `N`/`M`/`contingent`/
  `disjoint` — see [Settings](docs/SETTINGS.md) for the exact-period semantics and the
  operative rule for choosing `back`/`fwd`
- **The variable layer**: one `WitnessRegistry` (`semantic/witness_registry.py`) holding a
  Boolean per `(lasso, position slot, closure formula)` label bit and a Boolean box guess per
  boxed closure member — no `ForAll`/`Exists`, no MBQI, no E-matching pattern
- **Truth conditions**: `true_at`/`false_at` are label-membership lookups
  (`witness_registry.bit(lasso, position, formula)`), not quantified Z3 formulas
- **Two-phase emission**: per-premise/conclusion constraints are built as each is translated;
  `finalize_certificate()` appends the remaining box-faithfulness, target-selector, and
  per-lasso local-coherence/fulfilment constraints once every witness lasso a boxed subformula
  might need has been allocated

The semantics is independent of the operators defined over it. This modular design makes it easy
to compare semantic theories for the same operators as well as to compare operators for the same
semantics.

### BimodalProposition

`BimodalProposition` (`semantic/proposition.py`) handles the interpretation and representation of
sentences over a found certificate:

- **Extension calculation**: `find_extension()` computes `{lasso_index: (true_positions,
  false_positions)}` directly from certificate labels — not by recursing through operator
  `find_truth_condition` methods, which no primitive operator defines any more
- **Truth evaluation**: `truth_value_at(eval_lasso, eval_position)` reads a single label
  membership fact
- **Proposition display**: prints truth values per lasso, matching the certificate's own printed
  shape

Although sentence letters may be evaluated at `(lasso, position)` points on their own, tense and
modal operators can only be interpreted relative to a whole labelled lasso family.

### BimodalStructure

`BimodalStructure` (`semantic/model.py`) manages the certificate search's result:

- **Certificate extraction and independent re-check**: on every satisfying Z3 model, extracts a
  `WitnessFamily` and immediately re-checks it against the four certificate conditions with a
  pure-Python checker, independent of the Z3 model object (see
  [The Certificate Search](#the-certificate-search) and `docs/ADEQUACY.md` section 6.2) — a verdict
  other than "countermodel" raises `ModelConstructionError` immediately, so nothing downstream
  ever sees an unverified certificate
- **Never reports validity**: an unsatisfiable solve leaves `self.certificate = None` and
  `self.target_time = None`; every print path renders this as "no certificate found within the
  configured bounds," never as a validity claim
- **Visualization**: `print_certificate`/`print_evaluation`/`print_all` display every lasso, the
  boxed-subformula guess table, and each false box's witness

## Basic Usage

The bimodal theory provides a framework for searching for witness-family certificates that
refute a bimodal inference over discrete time. This section explains how to use the theory's main
components and run examples.

For comprehensive documentation of all available settings, see
**[docs/SETTINGS.md](docs/SETTINGS.md)**.

For general settings that apply across all theories, see the [main settings documentation](../../settings/README.md).

### Settings

The bimodal theory supports the following configurable settings:

```python
DEFAULT_EXAMPLE_SETTINGS = {
    # back/fwd: exact cyclic periods (not maxima) of the searched LabelledLasso family's
    # back/fwd segments (matching WitnessRegistry's nb/nf); mid: direct-read segment
    # length (nm), a genuine maximum. Small defaults; raise back/fwd as a multiple of
    # the period of interest, not simply larger (see docs/SETTINGS.md).
    'back': 2,
    'mid': 1,
    'fwd': 2,
    # Optional cap on the number of distinct witness-lasso indices ever handed out;
    # None (the default) means uncapped -- one witness lasso per boxed subformula.
    'max_witnesses': None,
    # Maximum time Z3 is permitted to look for a model
    'max_time': 1,
    # Whether a model is expected or not (used for unit testing)
    'expectation': True,
    # Number of model iterations to generate
    'iterate': 1,
    # Solver backend: 'z3' or 'cvc5'
    'solver': 'z3',
}
```

`back`, `mid`, and `fwd` replace `N`/`M`, but not identically: `back` and `fwd` are the *exact*
cyclic periods of the searched lasso family's back/fwd segments, not upper bounds — a family whose
true period is `p` is representable only when `p` divides the configured length, so raising `back`
or `fwd` is not monotone and can discard a family a smaller value represented. `mid` is the one
direct-read segment length and is a genuine maximum; raising it does enlarge the search. See
[Settings](docs/SETTINGS.md) for the full explanation and the operative rule. `max_witnesses`
replaces `temporal_depth`.
`contingent`/`disjoint` no longer exist — there is no proposition-level machinery left for them to
gate. The one bimodal-specific *general* (display) setting is `align_vertically` (the `-a` flag):
by default every history prints as one time-labelled arrow chain
`… (-2:A) ⟹ (-1:A) | (0:A) | (+1:A) ⟹ (+2:A) …` (see [Sample Output](#sample-output)); with
it, the histories print as a time-aligned table with one row per position and one column per
lasso (see `docs/SETTINGS.md`'s "General Settings").

### Example Structure

Each example is structured as a list containing three elements:

```python
[premises, conclusions, settings]
```

Where:
- `premises`: list of formulas that must be true in the model
- `conclusions`: list of formulas to check (invalid if all premises are true and at least one
  conclusion is false)
- `settings`: dictionary of settings for this example

Here's a complete example definition:

```python
# Countermodel showing that Future A does not imply Box A
BM_CM_1_premises = ['\\Future A']
BM_CM_1_conclusions = ['\\Box A']
BM_CM_1_settings = {
    'back': 2,
    'mid': 1,
    'fwd': 2,
    'max_time': 10,
    'expectation': True,  # Expects to find a countermodel
}
BM_CM_1_example = [
    BM_CM_1_premises,
    BM_CM_1_conclusions,
    BM_CM_1_settings,
]
```

### Running Examples

You can run examples in several ways:

#### 1. From the Command Line

```bash
# Run the default example from examples.py
model-checker path/to/examples.py

# Run with constraints printed
model-checker -p path/to/examples.py

# Run with Z3 output
model-checker -z path/to/examples.py
```

#### 2. In VSCodium/VSCode

1. Open the `examples.py` file in VSCodium/VSCode
2. Use one of these methods:
   - Click the "Run Python File" play button in the top-right corner
   - Right-click in the editor and select "Run Python File in Terminal"
   - Use keyboard shortcut (Shift+Enter) to run selected lines

#### 3. In Development Mode

For development purposes, you can use the `dev_cli.py` script from the project root directory:

```bash
# Run the examples file
./dev_cli.py path/to/examples.py

# Run with constraints printed
./dev_cli.py -p path/to/examples.py

# Run with Z3 output and constraints printed (combined flags)
./dev_cli.py -z path/to/examples.py
```

#### 4. Using the API

The bimodal theory exposes a clean API:

```python
from model_checker.theory_lib.bimodal import (
    BimodalSemantics, BimodalProposition, BimodalStructure, bimodal_operators
)
from model_checker import ModelConstraints
from model_checker.theory_lib import get_examples

# Get examples
examples = get_examples('bimodal')
example_data = examples['BM_CM_1']
premises, conclusions, settings = example_data

# Create semantic structure
semantics = BimodalSemantics(settings)
model_constraints = ModelConstraints(semantics, bimodal_operators)
model = BimodalStructure(model_constraints, settings)

# Inspect the certificate (None if no certificate was found within the configured bounds)
model.print_certificate()
```

### Theory Configuration

The bimodal theory is defined by combining several components:

```python
bimodal_theory = {
    "semantics": BimodalSemantics,
    "proposition": BimodalProposition,
    "model": BimodalStructure,
    "operators": bimodal_operators,
}

# Define which theories to use when running examples
semantic_theories = {
    "Bimodal" : bimodal_theory,
    # additional theories will require translation dictionaries
}
```

#### Countermodel Example

Examples that are expected to have countermodels may be presented as follows:

```python
# Countermodel showing that Future A does not imply Box A
BM_CM_1_premises = ['\\Future A']
BM_CM_1_conclusions = ['\\Box A']
BM_CM_1_settings = {
    'back': 2,
    'mid': 1,
    'fwd': 2,
    'max_time': 10,
    'expectation': True,  # Expects to find a countermodel
}
BM_CM_1_example = [
    BM_CM_1_premises,
    BM_CM_1_conclusions,
    BM_CM_1_settings,
]
```

**BM_CM_1:** Shows that "Future A → Box A" is not valid (has a countermodel).

#### Theorem Example

Examples that are not expected to have countermodels may be presented as follows:

```python
# Theorem showing that Box A implies Future A
BM_TH_1_premises = ['\\Box A']
BM_TH_1_conclusions = ['\\Future A']
BM_TH_1_settings = {
    'back': 2,
    'mid': 1,
    'fwd': 2,
    'max_time': 10,
    'expectation': False,  # Expects NOT to find a countermodel
}
BM_TH_1_example = [
    BM_TH_1_premises,
    BM_TH_1_conclusions,
    BM_TH_1_settings,
]
```

**BM_TH_1:** No certificate is found for "Box A → Future A" within the configured bounds. Per
the theory's own never-report-validity rule (D8, see [The Certificate Search](#the-certificate-search)),
this is reported as "no certificate found," not asserted as a proof of validity — deciding
validity is the tableau/proof system's job, not this search's.

### Testing

The examples are collected into dictionaries with `name_string : example` entries:

```python
example_range = {
    # Curated subset for the default demonstration run
    "BM_CM_1": BM_CM_1_example,
    "BM_TH_1": BM_TH_1_example,
    # ... 25 examples total
}
```

`test_example_range` (aliasing `unit_tests`) carries the full 53-example suite used by the test
framework, spanning extensional, modal, tense, and bimodal (BX-axiom) fragments, with every
formerly-excluded example restored (see [Development Status](#development-status)).

See [tests/README.md](tests/README.md) for the full running guide.

## Bimodal Language

> [NOTE] The code blocks included below are abridged for readability.
> Consult `operators.py` for the complete implementation of the semantic clauses for the language.

Formal languages implemented in the `model-checker` must conform to the following specifications:

- Operators are designated with a double backslash as in `\\Box` and `\\Future`.
- Sentence letters are alpha-numeric strings as in `A`, `B_2`, `Mary_sings`, etc., using underscore `_` for spaces.
- Parentheses must be included around sentences whose main connective is a binary operator.
- Parentheses must NOT be included around sentences whose main connective is a unary operator.

Every primitive operator's `true_at`/`false_at` mirrors its own case in `semantic/formula.py`'s
`translate` dispatch (report 01 section 4.4): it reconstructs the `Formula` its combinator
produces from its already-translated arguments, then looks up
`self.semantics.witness_registry.bit(eval_point["lasso"], eval_point["position"], formula)`. There
is exactly one rule per operator, stated in two places (the translation table and the operator's
own `true_at`), not two independently-evolving encodings of the same rule.

### Necessity Operator (`\\Box`)

The necessity operator (`\\Box`) evaluates whether a formula holds across every certified world
history at the same evaluation position.

**Key Properties:**

- Evaluates truth across every lasso and every one of its integer translates (purely modal)
- Returns true only if the box guess `bx(A)` is `true` — which, by box faithfulness (C3), holds
  exactly when `A` belongs to the label at every position of every lasso in the family
- Returns false if `bx(A)` is `false`, in which case the certificate carries a **witness lasso**
  whose label omits `A` at some position

#### Truth Condition

`\\Box A` is true at `(lasso, position)` if and only if `Box(A)` is in the label at that position
— by (C1)'s box clause, this holds for every position of every lasso exactly when `bx(A) = true`.

```python
def true_at(self, argument, eval_point):
    formula = Box(translate(argument.sentence_letter or argument, ...))
    return self.semantics.witness_registry.bit(
        eval_point["lasso"], eval_point["position"], formula
    )
```

#### Falsity Condition

`\\Box A` is false at `(lasso, position)` if and only if `bx(A) = false`, in which case the
certificate's witness lasso for `A` (allocated by `WitnessRegistry.allocate_witness_lasso`)
demonstrates a position where `A`'s label is absent.

### Future Operator (`\\Future`)

The future operator (`\\Future`) evaluates whether a formula holds at every strictly later
position of the same lasso.

**Key Properties:**

- Evaluates truth across every future position of the current lasso (purely temporal)
- Defined via `\\Until`: `\\Future A` is `\\neg (\\top \\Until \\neg A)` — "there is no future
  point where `A` first fails while `\\top` holds throughout," i.e. `A` holds at every future
  point
- Future positions exclude the present position of evaluation

#### Truth Condition

`\Future A` is true at `(lasso, position)` if and only if `A`'s label bit is set at every strictly
later position of the same lasso — read directly from the periodic label, not from a bounded
window.

### Past Operator (`\Past`)

The past operator `\Past A` is the temporal mirror of `\Future`, defined via `\\Since`, and reads
`A`'s label bit at every strictly earlier position of the same lasso.

### Until and Since Operators

`\\Until` and `\\Since` are primitive, guard-first (matching the Lean `untl`/`snce`
constructors — argument order is `(guard, event)`. ModelChecker's own `UntilOperator`/
`SinceOperator` are guard-first too, so `translate` is positional identity, not a swap; see
`semantic/formula.py`'s module docstring). `g \\Until e` is true at a position exactly when (C1)'s
fixpoint clause holds there — `e`'s label bit is set at the next position, or `g`'s label bit is
set at the next position and `g \\Until e` recurses — and (C2) fulfilment guarantees this fixpoint
is never satisfied merely by infinite postponement: there must be an actual later position where
`e` holds with `g` holding at every position strictly in between. `\\Since` is the backward
mirror.

## Important Theorems

The bimodal semantics validates several important theorems that demonstrate the interaction
between modal and temporal operators, all decided by the certificate search at the default
`back=2/mid=1/fwd=2` segment lengths:

1. **Box-Future Theorem** (`BM_TH_1`): `\Box A → \Future A`
2. **Box-Past Theorem** (`BM_TH_2`): `\Box A → \Past A`
3. **Modal-Future Theorem** (`MF_MODAL_FUTURE_TH`): `\Box A → \Box \Future A` — the paper's own
   bimodal axiom MF. The retired window-and-abundance encoding refuted this axiom (a countermodel
   at `N=1, M=2`), which is the decisive evidence that encoding was not a model of the paper's
   semantics rather than merely slow or incomplete; see `docs/ARCHITECTURE.md`. The certificate
   encoding finds no certificate for its negation, matching the paper.
4. The **BX axiom system** (`BX6`/`BX6P`/`BX7`/`BX7P`/`BX11`/`BX11P`/`BX13`/`BX13P`): linearity,
   absorption, and enrichment theorems over `\\Until`/`\\Since`, including `BX7_LINEAR_U_TH` and
   `BX7P_LINEAR_S_TH`, both of which the retired encoding excluded for solver-cost reasons and
   which now decide correctly in well under 50ms each.

## The Certificate Search

### What Is Searched

Fix the premises and conclusions of an inference and let `C` be the subformula closure of their
union (`semantic/formula.py`'s `closure_of`). A **certificate** is:

- a **box guess** `bx : C → Bool` for every boxed subformula in `C`;
- a **main lasso** `L0`, plus one **witness lasso** for every boxed subformula guessed false (at
  most one more than the number of boxes; lassos may be shared but sharing is not implemented —
  see `semantic/certificate.py`'s "Extension point" note);
- each lasso given as `(back, mid, fwd)` segments, a subset of `C` (a **label**) at every
  position, with positions left of the origin repeating `back` and positions at or after `mid`'s
  length repeating `fwd`.

A certificate must satisfy four conditions at every lasso and every position (`docs/ADEQUACY.md`
section 1 has the full statement; this is the informal shape):

1. **Local coherence (C1)**: `⊥` is never in a label; `a → b`, `Box(χ)`, `g Until e`, and `g Since
   e` are each in a label exactly when their defining biconditional holds there. Atoms are
   deliberately unconstrained — the search is free to choose them, and Lemma 4's atom case
   (`docs/ADEQUACY.md`) shows this is sound, not a gap.
2. **Fulfilment (C2)**: every `Until`/`Since` obligation in a label has an actual later/earlier
   witness position with the guard holding throughout — this is what stops (C1)'s fixpoint law
   from being satisfied by infinite postponement.
3. **Box faithfulness (C3)**: a box guessed true has its argument in every label of every lasso; a
   box guessed false has some position of some lasso omitting it.
4. **Target (C4)**: some position of the main lasso carries every premise and no conclusion.

### The Certified Model

The certificate denotes the `ShiftSet` whose carrier is the disjoint union of the lassos'
`(index, position)` points, with the shift `(i, t) ⇒_x (i, t + x)` as the task relation for every
integer `x`, and an atom true at `(i, t)` exactly when it is in that position's label. Seriality,
compositionality, Limit, and Saturation hold **by construction** of this carrier, not by an
asserted axiom — see `docs/ADEQUACY.md`'s Lemma 1. Its possible worlds are exactly the lasso
orbits (Lemma 2), so `\\Box` ranges over exactly the certified histories, and the model has
infinitely many world states and infinite durations. `docs/ADEQUACY.md` proves the (SOUND)
theorem: whenever the search reports a certificate, the certified model genuinely refutes the
inference.

**Soundness is unconditional; completeness is not claimed.** ModelChecker's own soundness does
not depend on any open theorem — (SOUND) is proved in full in `docs/ADEQUACY.md`. The converse
direction (every ℤ-refutable inference has a certificate within some length bound) is the open
"compression lemma" of a separate Lean development, and it determines only whether "no
certificate found within bounds" carries information — it never licenses reporting validity. This
theory never reports validity for exactly this reason (D8): "no certificate found" is always
rendered as a bounded-search fact, never as a proof.

Independent of that open direction, every model this theory reports is checked twice: once by the
Z3 constraints that produced it, and once more by a pure-Python re-checker
(`semantic/certificate.py`'s `recheck`) that re-verifies all four conditions from the extracted
labels alone, with no access to the Z3 model object. A verdict other than "countermodel" raises
immediately — an encoder bug becomes a loud rejection, never a false report.

### Sample Output

A countermodel (`BM_CM_1`, `\\Future A ⊭ \\Box A`), as printed by `dev_cli.py` (the
`Verification:` line's wording depends on whether an independent checker resolved — see
`docs/SETTINGS.md`'s "Certificate Verification"):

```
EXAMPLE BM_CM_1: there is a countermodel.

Search bounds: back=2, mid=1, fwd=2 (2 lassos: 1 main + 1 reserved witness)

Semantic Theory: Bimodal

Premise:
1. \Future A

Conclusion:
2. \Box A

Solver Run Time: 0.0012 seconds

========================================
Histories:  (one row per lasso: (t:atoms) states joined by ⟹, … marks the periodic back/fwd segments, | separates back | mid | fwd, [ ] marks the evaluation point)
  L0  main                … [-2:A] ⟹ (-1:A) | (0:A) | (+1:A) ⟹ (+2:A) …
  L1  witness for \Box A  … (-2:∅) ⟹ (-1:∅) | (0:∅) | (+1:∅) ⟹ (+2:∅) …

Box guesses:
  \Box A  false  falsified at L1, t=-2

Evaluation point: L0 at t=-2
Verification: independently checked -- Lean constructed a WitnessFamily.Refutes term for this certificate by applying a compile-time kernel-checked implication to four run-time decisions (acceptance: entailment, checkout 908922e779e7)

INTERPRETED PREMISE:

1.  |\Future A| = < {0}, {1} >  (True at L0, t=-2)
      |A| = < {0}, {1} >  (True at L0, t=-2)

INTERPRETED CONCLUSION:

2.  |\Box A| = < {}, {0, 1} >  (False at L0, t=-2)
      |A| = < {0}, {1} >  (True at L0, t=-2)
```

`Search bounds` reports the segment lengths and how many lassos the search allocated (the main
lasso plus one reserved witness per boxed subformula). Each `Histories` row is one lasso as a
time-labelled arrow chain: every state is `(t:atoms)` — the signed time and the label's atoms
(`A`, `{A,B}`, or `∅` for an empty label) — adjacent states within the periodic `back` and
`fwd` segments are joined by `⟹`, `|` separates `back | mid | fwd` (an empty `mid` collapses
to a single `|`), `…` marks that the `back` segment repeats leftward and the `fwd` segment
rightward forever, and `[ ]` marks the evaluation point on the main lasso. The columns are
padded so equal times line up across rows. Here `A` holds throughout `L0`, so `\Future A` holds
at `t=-2`. The role column says what each lasso does in *this* certificate — `L1` is the
`witness for \Box A` because its label omits `A` everywhere — and the `Box guesses` table names
the concrete `(lasso, t)` at which each false box is falsified, read from the certificate itself.
Formulas print in the notation you wrote them in. On a pipe or with `NO_COLOR` set the output
is plain text; on a terminal the evaluation point, reserved rows, and guess values are colored.
Pass `-a` for a time-aligned table view instead of one arrow chain per lasso (see
`docs/SETTINGS.md`).

A no-certificate case (`BM_TH_1`, `\\Box A ⊨ \\Future A`):

```
EXAMPLE BM_TH_1: there is no countermodel.

Search bounds: back=2, mid=1, fwd=2 (2 lassos: 1 main + 1 reserved witness)

Semantic Theory: Bimodal

Premise:
1. \Box A

Conclusion:
2. \Future A

Solver Run Time: 0.0026 seconds

========================================
Histories:
  No certificate found within the configured bounds (back=2, mid=1, fwd=2). This is not a validity claim (docs/ADEQUACY.md section 7.4).
```

The explicit "not a validity claim" wording is D8 (see [The Certificate Search](#the-certificate-search)
above): an unsatisfiable search within the configured bounds is a fact about the bounds, never a
proof.

## Model Iteration

The bimodal theory supports finding multiple certificates through the `BimodalModelIterator`
class:

```python
from model_checker.theory_lib.bimodal import iterate_example

# Find up to 3 distinct certificates
models = iterate_example(example, max_iterations=3)

for i, model in enumerate(models):
    print(f"Certificate {i+1}:")
    model.print_certificate()
```

Successive certificates are required to differ in at least one label bit or box guess (a blocking
clause built directly against the previous solved model), and isomorphism detection/exclusion is
rotation/permutation-invariant over the certificate's own symmetry group -- a certificate that is
only a rotation of an earlier one's `back`/`fwd` segments, or a permutation of its witness
lassos, is treated as the same model, not reported again. See `docs/ITERATE.md` for the full
story, including `_check_model_isomorphism`/`_create_non_isomorphic_constraint`'s three
shared-iterator extension points and `semantic/symmetry.py`'s group definition.

## Development Status

**This theory is gating again.** The `development` marker that previously quarantined every test
under `tests/` from release-gating CI has been removed: the certificate redesign restored the
speed and semantic-alignment aims that motivated the marker in the first place (see
`code/docs/core/TESTING_GUIDE.md` section 8.14 for the marker's history and its retirement
record).

Run the suite:

```bash
cd code && PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/ -v
```

See [`tests/README.md`](tests/README.md) for the full running guide.

## Known Limitations

- **Determinism, not branching**: certified frames have no branching at a shared state (lassos
  never share positions); this is without loss for the current language (Z-frame validity equals
  validity over recurrence-free Z-frames), but a future stability-modal extension would need
  branching witness families, which is open research and not promised here.
- **Discrete time only**: dense/continuous time is out of scope — see `docs/ARCHITECTURE.md`'s
  "Why ℤ-time only" for the structural reason (a finite carrier over a dense order collapses
  every small-duration fibre to a singleton).
- **`iterate: N > 1`**: the shared-framework extension points this theory needs (`_pin_theory_
  specific_values`, `_build_exclusion_constraints`, `_check_model_isomorphism`) are wired in and
  exercised by a real, non-mocked live test; isomorphism rejection during iteration is
  rotation/permutation-invariant over the certificate's symmetry group (rotating each lasso's
  `back`/`fwd` segments, permuting witness-lasso indices), not merely exact-difference; see
  [docs/ITERATE.md](docs/ITERATE.md).
- **No fixed-frame model-checking mode**: checking a given finite digraph directly (rather than
  searching for a certificate) is a distinct, currently out-of-scope feature.

## Adequacy

`docs/ADEQUACY.md` states and proves the (SOUND) soundness correspondence between the
witness-family certificate design implemented in this package and the paper's task semantics, and
states the open adequacy (converse) direction without asserting it. `docs/ARCHITECTURE.md` carries
forward the theorem statement, the four lemmas, and the Lean citation table for quick reference;
`docs/ADEQUACY.md` is the fuller treatment.

## References

For more information on bimodal logics and related topics, see:

- `docs/ARCHITECTURE.md` for the certificate design, the two-phase constraint emission, and the
  (SOUND) theorem
- `docs/ADEQUACY.md` for the full soundness proof and the open adequacy direction
- The test suite in [`tests/`](tests/), documented in [`tests/README.md`](tests/README.md)
- The differential oracle in `oracle/bimodal_logic/`, documented in its own
  [`README.md`](../../../../../oracle/bimodal_logic/README.md)
