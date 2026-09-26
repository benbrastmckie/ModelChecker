# Bimodal Theory Model Iteration Guide

This guide explains how to find multiple distinct witness-family certificates for bimodal logic
formulas using the model iteration feature, and states plainly what is and is not guaranteed by
it.

## Table of Contents

- [Overview](#overview)
- [Basic Usage](#basic-usage)
- [Configuration](#configuration)
- [Understanding Results](#understanding-results)
- [How Model Diversity Is Actually Enforced](#how-model-diversity-is-actually-enforced)
- [Performance Tips](#performance-tips)
- [Troubleshooting](#troubleshooting)
- [See Also](#see-also)

## Overview

Model iteration searches for additional witness-family certificates that satisfy the same
premises and violate the same conclusions as the first. This module was rewritten around the
certificate encoding's own variables — label bits and box guesses — rather than the retired
encoding's world histories, task relations, and time-shift tables. See
`ARCHITECTURE.md`'s "Model Iteration" section and `iterate.py`'s own module docstring for the full
technical account this guide summarizes.

**Read [How Model Diversity Is Actually Enforced](#how-model-diversity-is-actually-enforced)
before relying on `iterate: N > 1`.** This redesign narrows iteration's diversity guarantee on
purpose: distinctness is exact-bit/guess difference, not rotation/permutation invariance (see
that section, and the ["Repeated (rotated) certificates"](#repeated-rotated-certificates)
troubleshooting entry).

## Basic Usage

### Simple Iteration (N = 1, the safe case)

```python
from model_checker import BuildExample
from model_checker.theory_lib import bimodal
from model_checker.theory_lib.bimodal.iterate import iterate_example

theory = bimodal.get_theory()

example = BuildExample("modal_temporal", theory, [
    ["\\Box p"],
    ["\\Future \\Box p"],
    {"back": 2, "mid": 1, "fwd": 2, "iterate": 1}
])

models = iterate_example(example, max_iterations=1)
print(f"Found {len(models)} certificate(s)")
models[0].print_certificate()
```

### Requesting more than one certificate

```python
models = iterate_example(example, max_iterations=3)
print(f"Found {len(models)} certificate(s)")
for model in models:
    if hasattr(model, 'print_model_differences'):
        model.print_model_differences()
```

Returns up to three pairwise-distinct certificates (fewer if the settings admit fewer than three
— see the ["No additional certificates found"](#no-additional-certificates-found) troubleshooting
entry). Distinctness is enforced by a genuine Z3 blocking clause over the certificate's own
label bits and box guesses — see
[How Model Diversity Is Actually Enforced](#how-model-diversity-is-actually-enforced).

## Configuration

### Iteration Settings

```python
settings = {
    "back": 2,
    "mid": 1,
    "fwd": 2,
    "iterate": 3,       # Number of distinct certificates to search for
    "max_time": 10,
}
```

### Difference Detection

`BimodalModelIterator._calculate_differences` reports differences in exactly two things now:

1. **Label bits**: which closure formulas were added to or removed from a lasso's label at a
   given position
2. **Box guesses**: which boxed subformulas changed their guessed value between models

The retired encoding's five categories (world histories, truth conditions, task relations, time
intervals, time-shift relations) no longer apply — there are no world arrays or time-shift tables
to diff any more; a "model," under this encoding, *is* a label/guess assignment.

## Understanding Results

### Displayed Differences

`display_model_differences` prints label and guess differences directly:

```
=== DIFFERENCES FROM PREVIOUS MODEL ===

Label Changes:
  L0, position -1: + Box(A)
  L1, position 0: - A

Box Guess Changes:
  Box(A): False -> True
```

### Interpreting Bimodal Differences

- A **label change** means a closure formula's membership at a `(lasso, position slot)` flipped.
- A **box guess change** means a boxed subformula's global truth value (by box faithfulness, C3)
  flipped between the two certificates.

## How Model Diversity Is Actually Enforced

`BaseModelIterator.iterate()`/`iterate_generator()` (`model_checker/iterate/core.py`) reaches
`BimodalModelIterator`'s own `_create_difference_constraint` through a polymorphic extension
point: `_build_exclusion_constraints` calls it directly (with the full list of previously-found
models) and hands the result to the solver as the live loop's actual exclusion constraint. This
is not merely interface parity or a standalone helper — it is the mechanism the live
`iterate: N > 1` search enforces distinctness with.

The shared framework's other two extension points matter here too:
`_pin_theory_specific_values` pins every certificate variable (label bit, box guess) of a newly
found model into the fresh solve that builds its `ModelStructure`, and `_check_model_isomorphism`
is overridden to always report "not isomorphic" for this theory — the shared graph-based
isomorphism check is built from `z3_world_states`, which the certificate encoding never
populates, so two bimodal models would otherwise always produce two empty graphs and be
(falsely) reported isomorphic. See `iterate.py`'s own module docstring, and
`model_checker/iterate/README.md`'s Extension Guide, for the full three-hook contract shared
across all four theories.

**Distinctness is exact-bit/guess difference, not rotation/permutation invariance.**
`_create_non_isomorphic_constraint` (used when the shared framework's generic escape path is
composed in for other theories — moot for bimodal specifically, since `_check_model_isomorphism`
above never reports an isomorphic hit for this theory to escape from) and
`_create_difference_constraint` both reject only exact label-bit/box-guess equality. A fully
symmetry-aware rejection would need to enumerate the rotation group action on each lasso's
periodic `back`/`fwd` segments together with witness-lasso relabelings; this redesign implements
the simpler exact-bit/guess difference instead — sufficient to guarantee the *next* certificate is
not bit-for-bit identical to a previous one, but not sufficient to guarantee it is not a rotation
of one. A follow-on task should implement the full symmetry-aware rejection using
`WitnessRegistry.wrap`'s existing slot arithmetic to enumerate rotations — see
["Repeated (rotated) certificates"](#repeated-rotated-certificates) below.

## Performance Tips

### 1. Start with the default segment lengths

```python
settings = {"back": 2, "mid": 1, "fwd": 2, "iterate": 1}
```

Raise `back`/`mid`/`fwd` only if a specific formula's refutation needs a longer period than the
defaults allow — every one of the theory's 53 examples decides at the defaults in well under
50ms.

### 2. Use appropriate timeouts

```python
settings = {"max_time": 10}
```

### 3. Enable debug logging

```python
import logging
logging.getLogger('model_checker.theory_lib.bimodal.iterate').setLevel(logging.DEBUG)
```

## Troubleshooting

### No additional certificates found

- Raise `back`/`mid`/`fwd` for more structural variety in the periodic segments.
- Raise `max_witnesses` if the formula has several boxed subformulas.
- Check whether your formula heavily constrains the label assignment — a highly determined
  formula may genuinely admit very few distinct certificates. The live loop terminates cleanly
  once the admitted space is exhausted (a `"solver returned unsat"` debug message), rather than
  hanging or looping forever.

### Repeated (rotated) certificates

- Expected under the current exact-difference rejection (see
  [How Model Diversity Is Actually Enforced](#how-model-diversity-is-actually-enforced)); this is
  not a bug to work around locally, it is the documented scope of this redesign's iteration
  support.

## See Also

- [API Reference](API_REFERENCE.md#model-iteration) - API documentation
- [Architecture](ARCHITECTURE.md#model-iteration) - Implementation details
- [User Guide](USER_GUIDE.md) - General usage patterns
- [Settings Reference](SETTINGS.md) - Configuration options
