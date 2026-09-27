# Bimodal Theory API Reference

This document provides API documentation for the bimodal theory implementation in ModelChecker
under the witness-family certificate design. See `../README.md` and `ARCHITECTURE.md` for the
design these classes and functions implement.

## Table of Contents

- [Overview](#overview)
- [Core Functions](#core-functions)
- [Classes](#classes)
- [The Formula ADT and Certificate Datatypes](#the-formula-adt-and-certificate-datatypes)
- [Operators](#operators)
- [Model Iteration](#model-iteration)
- [Type Definitions](#type-definitions)
- [Examples](#examples)
- [Error Handling](#error-handling)

## Overview

The bimodal theory API searches for **witness-family certificates**: a Boolean box guess plus a
small family of labelled bi-infinite lassos, satisfying four conditions (C1-C4), which denote an
infinite certified model by construction. It combines:

- **Temporal operators** for reasoning about time (past/future/until/since)
- **Modal operators** for reasoning about possibility/necessity, decided by a box guess plus,
  when guessed false, a witness lasso
- **A pure-Python re-checker** (`certificate.recheck`) that independently verifies every found
  certificate before it is reported

All code examples use LaTeX notation (e.g., `\\Box`, `\\Future`) as required by the ModelChecker
parser.

## Core Functions

### `get_theory(config=None)`

Get the bimodal theory configuration object.

**Parameters:**
- `config` (optional): accepted for cross-theory signature uniformity and always ignored — bimodal
  has no subtheory decomposition to restrict to (unlike logos's `subtheories=` keyword)

**Returns:**
- dict: `{"semantics": BimodalSemantics, "proposition": BimodalProposition, "model":
  BimodalStructure, "operators": bimodal_operators}`

**Example:**
```python
from model_checker.theory_lib import bimodal

theory = bimodal.get_theory()
```

### `get_examples()`

Get the curated `example_range` dictionary (25 of the 53 total example formulas, the default
demonstration set).

### `get_test_examples()`

Get the full `test_example_range` (aliasing `unit_tests`, 53 examples), used by the test
framework.

### `print_example_report()`

Print a summary report (active vs. total example counts, broken down by countermodel/theorem and
by category) to stdout.

## Classes

### `BimodalSemantics`

Owns the certificate search's settings, the quantifier-free Z3 variable layer, and the two-phase
constraint emission. Module: `semantic/core.py`.

**Inherits from:** `SemanticDefaults`

**Key Attributes:**
- `back`, `fwd` (int): exact cyclic periods of the lasso's back/fwd segments, not maxima; `mid`
  (int): a genuine maximum, the one direct-read segment length — see
  [SETTINGS.md](SETTINGS.md)
- `max_witnesses` (int or `None`): optional cap on distinct witness-lasso allocation
- `N` (int, always `0`), `all_states` (list, always `[]`): vestigial attributes the shared
  framework reads unconditionally (`models/structure.py`); the certificate encoding has no
  world-count/state notion, so these are fixed placeholders, not live settings
- `witness_registry` (`WitnessRegistry`): the Z3 variable layer
- `constraint_generator` (`WitnessConstraintGenerator`): the (C1)/(C4) constraint builders

**Key Methods:**

#### `__init__(self, settings)`
Initialize from a settings dict carrying `back`/`mid`/`fwd`/`max_witnesses`/`max_time`/
`expectation`/`iterate`/`solver`.

#### `true_at(self, sentence, eval_point)` / `false_at(self, sentence, eval_point)`
Evaluate whether a sentence is true/false at an evaluation point.

**Parameters:**
- `sentence`: the sentence to evaluate
- `eval_point` (dict): `{"lasso": int, "position": int}` — **not** `{"world", "time"}`, the
  retired encoding's shape

**Returns:**
- a Z3 `BoolRef` that is a direct label-membership lookup (`witness_registry.bit(...)`), never a
  quantified formula

#### `finalize_certificate(self)`
Phase 2 of the two-phase constraint emission (see `ARCHITECTURE.md`): appends box faithfulness,
the exactly-one target-selector constraint, and every lasso's local-coherence/fulfilment
constraints to `self.frame_constraints` in place. Idempotent (guarded by
`self._certificate_finalized`); called once from `BimodalStructure._setup_solver`.

#### `extract_certificate(self, z3_model)`
Build the `WitnessFamily` and target time a satisfying `z3_model` denotes. Must be called after
`finalize_certificate()` and after a satisfiable solve.

**Returns:**
- `(family, target_time)`: `family` is a `WitnessFamily`; callers must independently re-check it
  via `certificate.recheck` before treating it as a countermodel (obligation S3, see
  `ARCHITECTURE.md`) — `BimodalStructure.__init__` is the caller that does this.

#### `export_certificate_json(self, family, target_time)`
Serialize `family` to the certificate wire format (`WitnessFamily.to_json`), using this search's
own recorded premise/conclusion formulas.

### `BimodalProposition`

Computes truth values directly from a found certificate's labels — no recursion through operator
`find_truth_condition` methods (none are defined any more). Module: `semantic/proposition.py`.

**Inherits from:** `PropositionDefaults`

**Key Attributes:**
- `sentence`: the sentence this proposition represents
- `extension` (dict): `{lasso_index: (true_positions, false_positions)}` — **not** the retired
  `{world_id: (true_times, false_times)}` shape (the keys are lasso indices, not world IDs)

**Key Methods:**

#### `__init__(self, sentence, model_structure, eval_lasso='main', eval_position='now')`
Create a proposition for the given sentence. Note the parameter names: `eval_lasso`/
`eval_position`, not the retired `eval_world`/`eval_time`.

#### `find_extension(self)`
Compute `{lasso_index: (true_positions, false_positions)}` directly from certificate labels.

**Returns:**
- `Dict[int, Tuple[List[int], List[int]]]`

#### `truth_value_at(self, eval_lasso, eval_position)`
Check whether the proposition is true at a specific `(lasso, position)` point.

**Parameters:**
- `eval_lasso` (int): lasso index
- `eval_position` (int): position on that lasso

**Returns:**
- `Optional[bool]`: `True`/`False`/`None` (undetermined — no certificate, or the position falls
  outside the checked window)

### `BimodalStructure`

Manages certificate extraction, the independent re-check, and printing. Module: `semantic/model.py`.

**Inherits from:** `ModelDefaults`

**Key Attributes:**
- `certificate` (`WitnessFamily` or `None`): `None` until (and unless) a satisfying, independently
  re-checked certificate is found — **never** set from an unverified extraction (D8, obligation
  S3)
- `target_time` (`int` or `None`): the target position on the main lasso
- `main_point` (dict): `{"lasso": 0, "position": target_time}` — the evaluation point

**Key Methods:**

#### `print_certificate(self, output=sys.__stdout__)`
Print every lasso in the found certificate, the boxed-subformula table with each guess, and each
false box's witness history and position — or the explicit "no certificate found... this is not a
validity claim" message if `self.certificate is None`.

#### `print_evaluation(self, output=sys.__stdout__)`
Print the evaluation point (main lasso and target position), or the no-certificate message.

#### `print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__)`
Print the complete model report: info header, certificate, evaluation point, interpreted
premises/conclusions, and the raw Z3 model if requested.

#### `save_to(self, example_name, theory_name, include_constraints, output)`
Save all model elements to `output`, including the satisfiable constraint set if requested.

## The Formula ADT and Certificate Datatypes

These types (module `semantic/formula.py` and `semantic/certificate.py`) are structurally
identical to BimodalLogic's own Lean types (`FormalSystem.Syntax.Formula`,
`WitnessFamily/Basic.lean`'s `LabelledLasso`/`WitnessFamily`), by design — see
`ARCHITECTURE.md`'s "The Certificate Search."

### `Formula` (and its six constructors: `Atom`, `Bot`, `Imp`, `Box`, `Untl`, `Snce`)

The label domain. `Untl`/`Snce` are **guard-first** (`(guard, event)`), matching
ModelChecker's own `UntilOperator`/`SinceOperator` argument order (ModelChecker was previously
event-first; normalized to guard-first for cross-repository uniformity — see
`semantic/formula.py`'s module docstring).

#### `subformula_closure(formula)` / `closure_of(context)`
Compute the subformula closure of one formula, or the union of closures over a list of formulas
(premises plus conclusions) — the label domain `C` a certificate search is fixed against.

#### `translate(sentence)`
Translate a ModelChecker sentence into a `Formula`. Positional identity for `Until`/`Since` — no
argument swap.

#### `to_json(formula)` / `from_json(obj)`
The wire codec: tag vocabulary `atom`/`bot`/`imp`/`box`/`untl`/`snce`, matching BimodalLogic's
`BimodalTools/DataExport.lean`/`JsonParse.lean`. `to_json` raises `ValueError` on any `Atom` with a
non-`None` `fresh_index` — fresh atoms are never exported, matching the Lean side's own
`Atom.freshIndex`-dropping behavior.

### `LabelledLasso`

A `(back, mid, fwd)` triple of label tuples. `.label(t)` decodes any integer position to its
label; `.nb`/`.nm`/`.nf` give the three segment lengths.

### `WitnessFamily`

A box guess (`bx_of(chi)`) plus a non-empty tuple of `LabelledLasso`s (`.main` is `lassos[0]`).

#### `WitnessFamily.to_json(self, premises, conclusions, target_time)`
Serialize to the fixed external wire contract:
```json
{"target": {"premises": [...], "conclusions": [...], "time": 0},
 "bx":     [[<formula>, true], [<formula>, false], ...],
 "lassos": [{"back": [<label>, ...], "mid": [<label>, ...], "fwd": [<label>, ...]}, ...]}
```
`bx` is sparse (an unlisted formula reads as `false`); `target.time` is always emitted explicitly,
even when `0`.

### `recheck(family, premises, conclusions, target_time)`

The independent pure-Python re-checker (no Z3 model access). Returns
`{"status": "countermodel", "time": target_time}` on success, or
`{"status": "rejected", "failed": [...]}` naming the first of (C1)-(C4), or a structural check,
that fails.

### `recheck_json(raw)`

The JSON-boundary wrapper around `recheck`: decodes a raw wire-format `dict`, and reports
`{"status": "error", ...}` for input that fails the *protocol* (missing `target`/`target.time`),
distinct from `"rejected"` for input that parses but fails a *condition*.

### `WitnessRegistry`

The Z3 variable layer (module `semantic/witness_registry.py`).

#### `bit(self, lasso, t, formula)`
The Boolean Z3 variable for "does `formula` belong to the label at position `t` of `lasso`" —
shared across every position that maps to the same slot via `wrap`.

#### `guess(self, formula)`
The Boolean box-guess variable `bx(formula)`.

#### `allocate_witness_lasso(self, box_formula)`
Hand out (memoized) the witness-lasso index for a boxed subformula.

#### `wrap(self, t)`
Map an integer position to its slot index (`0 <= result < back + mid + fwd`).

### `WitnessConstraintGenerator`

The quantifier-free constraint generators for all four conditions (module
`semantic/witness_constraints.py`): `local_coherence_constraints(lasso)`,
`fulfilment_constraints(lasso)`, `box_faithfulness_constraints(lassos)`,
`target_constraints(premises, conclusions)`, and the one-hot selector `sel(t)`.

## Operators

### Extensional Operators

| Operator | Symbol | LaTeX | Arity | Primitive? |
|----------|--------|-------|-------|-------|
| NegationOperator | ¬ | `\\neg` | 1 | primitive |
| AndOperator | ∧ | `\\wedge` | 2 | primitive |
| OrOperator | ∨ | `\\vee` | 2 | primitive |
| ConditionalOperator | → | `\\rightarrow` | 2 | defined (via `\\neg`/`\\vee`) |
| BiconditionalOperator | ↔ | `\\leftrightarrow` | 2 | defined |

### Extremal Operators

| Operator | Symbol | LaTeX | Arity | Primitive? |
|----------|--------|-------|-------|-------|
| BotOperator | ⊥ | `\\bot` | 0 | primitive |
| TopOperator | ⊤ | `\\top` | 0 | defined (via `\\neg \\bot`) |

### Modal Operators

| Operator | Symbol | LaTeX | Arity | Primitive? |
|----------|--------|-------|-------|-------|
| NecessityOperator | □ | `\\Box` | 1 | primitive — box guess plus, when false, a witness lasso |
| DefPossibilityOperator | ◇ | `\\Diamond` | 1 | defined (via `\\neg \\Box \\neg`) |

### Temporal Operators

| Operator | Symbol | LaTeX | Arity | Primitive? |
|----------|--------|-------|-------|-------|
| FutureOperator | ⏵ | `\\Future` | 1 | primitive (via `\\Until`) |
| PastOperator | ⏴ | `\\Past` | 1 | primitive (via `\\Since`) |
| UntilOperator | U | `\\Until` | 2 | primitive, guard-first internally |
| SinceOperator | S | `\\Since` | 2 | primitive, guard-first internally |
| DefFutureOperator | ⏵ | `\\future` | 1 | defined — true at *some* future time |
| DefPastOperator | ⏴ | `\\past` | 1 | defined — true at *some* past time |
| DefNextOperator | — | `\\next` | 1 | defined — true at the immediately following position |
| DefPrevOperator | — | `\\prev` | 1 | defined — true at the immediately preceding position |

### Operator Usage Examples

```python
# Temporal necessity: "It is necessary that p will always be true"
formula1 = "\\Box \\Future p"

# Modal future: "In the future, p will be necessary"
formula2 = "\\Future \\Box p"

# Combined: "It's possible that p was true in the past"
formula3 = "\\Diamond \\Past p"

# Guard-first until: "p holds throughout, until q occurs"
formula4 = "(p \\Until q)"

# See examples.py for complete working implementations
```

## Model Iteration

### `iterate_example(example, max_iterations=None)`

Find multiple distinct certificates for a bimodal theory example.

**Returns:**
- list: list of `BimodalStructure` instances, each with its own `.certificate`

**Example:**
```python
from model_checker.theory_lib.bimodal.iterate import iterate_example

models = iterate_example(example, max_iterations=5)
for i, model in enumerate(models):
    print(f"Certificate {i+1}:")
    model.print_certificate()
```

### `iterate_example_generator(example, max_iterations=None)`

Generator version of `iterate_example`, yielding each `BimodalStructure` incrementally.

### `BimodalModelIterator`

**Inherits from:** `BaseModelIterator`

**Key Methods:**
- `_calculate_differences(new_structure, previous_structure)`: report label- and guess-level
  differences (not the retired world-array differences)
- `_create_difference_constraint(previous_models)`: a blocking clause over label bits and box
  guesses
- `_create_non_isomorphic_constraint(isomorphic_model)`: excludes every recheck-valid element of
  `isomorphic_model`'s rotation/permutation orbit (`semantic/symmetry.py`), not just its exact bit
  pattern — the live loop's actual escape-from-isomorphism constraint when `_check_model_
  isomorphism` reports a match; see `ITERATE.md`
- `_check_model_isomorphism(new_structure, new_model)`: opts out of the shared graph-based
  isomorphism check permanently (`ModelGraph` is never constructed for this theory), but performs
  its own real detection via `symmetry.certificate_orbit_key`, an orbit-invariant canonical key
  over the certificate's rotation/permutation symmetry group
- `display_model_differences(model_structure, output=sys.stdout)`: format label/guess differences

## Type Definitions

### Positions
- Integer positions on a lasso, unbounded in both directions (`ℤ`)
- Type: `int`

### Lasso Indices
- Non-negative integers; `0` is always the main lasso
- Type: `int` (0, 1, 2, ...)

### Evaluation Points
```python
eval_point = {
    "lasso": 0,      # Lasso index (int)
    "position": 0    # Position on that lasso (int)
}
```

### Labels
- A label is a `FrozenSet[Formula]` — the subset of the closure `C` true at a position
- `LabelledLasso.label(t)` decodes any position to its label

## Examples

### Basic Theory Usage

```python
from model_checker.theory_lib import bimodal

theory = bimodal.get_theory()

# Theory provides access to:
# - Semantics: BimodalSemantics class
# - Model: BimodalStructure class
# - Propositions: BimodalProposition class
# - Operators: temporal and modal operators

# See examples.py for complete working implementations
```

### Conceptual Formula Examples

```python
# Temporal necessity: "Necessarily p implies always p in the future"
premise = "\\Box p"
conclusion = "\\Future p"

# Complex bimodal reasoning
premises = ["\\Diamond \\Future p", "\\Box \\Past q"]
conclusion = "\\Future \\Diamond (p \\wedge q)"

# Model iteration patterns
formula = "\\Diamond p \\vee \\Diamond q"

# See examples.py for complete implementation with settings:
# {"back": 2, "mid": 1, "fwd": 2, "max_time": 10}
```

### Certificate Access

```python
# After a satisfiable solve:
model.print_certificate()

for i, lasso in enumerate(model.certificate.lassos):
    print(f"L{i}: back={lasso.back} mid={lasso.mid} fwd={lasso.fwd}")

# Use model iteration for multiple certificates
models = iterate_example(example)
print(f"Found {len(models)} distinct certificates")
```

## Error Handling

### Common Exceptions

#### `ModelConstructionError`
Raised immediately if a satisfying Z3 model's extracted `WitnessFamily` fails the independent
pure-Python re-check (obligation S3) — an encoder bug becomes a loud rejection, never a silently
reported false countermodel.

#### `ValueError`
- Missing required settings
- `LabelledLasso` constructed with an empty `back` or `fwd` segment
- `to_json` called on a formula carrying a fresh-indexed atom

#### `z3.Z3Exception`
- Solver timeout (increase `max_time`)
- Unsatisfiable constraints (reported as "no certificate found," never as an error — see D8 in
  `ARCHITECTURE.md`)

### Error Handling Example

```python
try:
    theory = bimodal.get_theory()
    settings = {"back": 1, "mid": 0, "fwd": 1, "max_time": 1}
except ValueError as e:
    print(f"Configuration error: {e}")
except z3.Z3Exception as e:
    print(f"Solver error: {e}")
    settings["max_time"] = 10
```

### Debugging Tips

1. **Enable Z3 output**: set `"print_z3": True` in settings
2. **Check constraints**: set `"print_constraints": True`
3. **Choose `back`/`fwd` as a multiple of the needed period**: some formulas need a longer
   periodic pattern, but `back`/`fwd` are exact periods, not maxima — a larger non-multiple can
   lose a countermodel a smaller value found; `mid` may be raised freely, and none of the three is
   a larger `N`/`M` (which no longer exist). See [SETTINGS.md](SETTINGS.md).
4. **Re-check independently**: `certificate.recheck(family, premises, conclusions, target_time)`
   can be called directly against any certificate for debugging, outside a Z3 solve entirely

## See Also

- [User Guide](USER_GUIDE.md) - Practical usage patterns
- [Architecture](ARCHITECTURE.md) - Implementation details and the (SOUND) theorem
- [Adequacy](ADEQUACY.md) - The full soundness proof
- [Settings Reference](SETTINGS.md) - Configuration options
- [Model Iteration](ITERATE.md) - Finding multiple certificates
