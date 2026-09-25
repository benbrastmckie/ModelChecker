# Bimodal Theory Model Iteration Guide

This guide explains how to find multiple distinct witness-family certificates for bimodal logic
formulas using the model iteration feature, and states plainly what is and is not currently
guaranteed by it.

## Table of Contents

- [Overview](#overview)
- [Basic Usage](#basic-usage)
- [Configuration](#configuration)
- [Understanding Results](#understanding-results)
- [How Model Diversity Is Actually Enforced](#how-model-diversity-is-actually-enforced)
- [A Live Limitation: `iterate: N > 1` Currently Crashes](#a-live-limitation-iterate-n--1-currently-crashes)
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

**Read this whole document, especially the limitation section below, before relying on
`iterate: N > 1` for anything beyond N=1.** This redesign narrowed iteration's scope on purpose
(see [How Model Diversity Is Actually Enforced](#how-model-diversity-is-actually-enforced)) and,
independently, exposed a pre-existing framework gap that currently makes `iterate: N > 1` fail
outright through the standard `dev_cli.py`/`model-checker` CLI path
(see [A Live Limitation](#a-live-limitation-iterate-n--1-currently-crashes)). Neither is
speculative; both are demonstrated below.

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
```

As of this writing, this call **raises** rather than returning up to three certificates — see
[A Live Limitation](#a-live-limitation-iterate-n--1-currently-crashes). It is documented here in
its intended shape so the gap is visible against what the API is meant to do, not silently
omitted.

## Configuration

### Iteration Settings

```python
settings = {
    "back": 2,
    "mid": 1,
    "fwd": 2,
    "iterate": 1,       # Safe; see the limitation below for N > 1
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

`BaseModelIterator.iterate()`/`iterate_generator()` (`model_checker/iterate/core.py`) never call
`BimodalModelIterator`'s own `_create_difference_constraint`/`_create_non_isomorphic_constraint`
directly. They delegate to a composed, theory-agnostic `ConstraintGenerator`
(`model_checker/iterate/constraints.py`), constructed unconditionally in
`BaseModelIterator.__init__` and not overridable per theory. That generator's own exclusion logic
is entirely gated on `hasattr(semantics, 'is_world')` — true of the other three theories (which
keep a bitvector world-state predicate), **false of bimodal by design**: D3/D4 deliberately have no
state-existence predicate at all, because the certified carrier is `{0,...,k} x Z`, not a set of
enumerated states.

**Consequence**: for bimodal, the generic framework path contributes *no* active exclusion
constraint. `BimodalModelIterator._create_difference_constraint`/
`_create_non_isomorphic_constraint` exist for interface parity with the other three theories and
for direct, standalone use — they are exercised directly by
`tests/integration/test_iterate.py` — but are not invoked by the live search loop.

`_create_non_isomorphic_constraint` is additionally **simplified to exact difference, not
rotation/permutation invariance**: a fully symmetry-aware rejection would need to enumerate the
rotation group action on each lasso's periodic `back`/`fwd` segments together with witness-lasso
relabelings. This redesign implements the simpler exact-bit/guess difference shared with
`_create_difference_constraint` instead — sufficient to guarantee the *next* certificate is not
bit-for-bit identical, but not sufficient to guarantee it is not a rotation of a previous one.

Both points are recorded, not silently descoped, in the implementation plan's own Phase 15
section: a future task should (1) close the shared `ConstraintGenerator` extension-point gap with
its own cross-theory regression plan, and (2) implement the full rotation/permutation-invariant
rejection once (1) is in place, using `WitnessRegistry.wrap`'s existing slot arithmetic to
enumerate rotations.

## A Live Limitation: `iterate: N > 1` Currently Crashes

Beyond the scope narrowing above, direct testing of the standard `dev_cli.py`/`model-checker` CLI
path (`iterate: 3` set on an example) surfaces a sharper, pre-existing framework gap:
`model_checker/iterate/models.py`'s `build_new_model_structure` — the shared routine every
theory's iterator uses to build each successor model — contains

```python
for state in range(2**semantics.N):
    is_world_val = z3_model.eval(semantics.is_world(state), model_completion=True)
    ...
```

with **no `hasattr` guard**, unlike its neighboring `possible`/`verify`/`falsify` blocks in the
same function (which are each guarded). Bimodal's `BimodalSemantics` fixes `N = 0` (D3: a
vestigial attribute the shared framework reads unconditionally) and defines no `is_world` method
at all (D3/D4: the certificate encoding has no state-existence predicate). `range(2**0)` is `[0]`,
so this loop body runs exactly once and immediately raises:

```
AttributeError: 'BimodalSemantics' object has no attribute 'is_world'
```

which the framework wraps as `ModelExtractionError: Failed to extract model 1: ...`. This was
reproduced directly (`dev_cli.py` against a countermodel example with `"iterate": 3` in its
settings): the first certificate is found and printed normally, and the attempt to build the
*second* one fails with exactly this error, aborting the run.

**Why this was not caught by the 366/366-green test suite**: no example in `examples.py` sets
`iterate` above its default of `1`, and `max_iterations == 1` short-circuits before this code path
is ever reached. `tests/integration/test_iterate.py` exercises `BimodalModelIterator`'s own
methods directly (deliberately, per its own module docstring) rather than driving a live
`iterate: N > 1` run end to end, for exactly the scope-narrowing reason above — but that same
choice is why this second, independent crash was not previously surfaced against the live path.

**Scope of the fix**: `model_checker/iterate/models.py` is shared framework code all four theories
depend on; adding a `hasattr(semantics, 'is_world')` guard around this block (mirroring its own
`possible`/`verify` neighbors) is the natural fix, but it is cross-theory code requiring its own
regression coverage across all four theories, not a bimodal-only change. It is recorded here as a
known, reproduced limitation — not fixed as part of this documentation pass — for the same reason
the `ConstraintGenerator` gap above was left for a follow-on task.

**Practical guidance**: use `iterate: 1` (the default) until this is fixed. `iterate_example`/
`iterate_example_generator`'s programmatic API is unaffected for `max_iterations=1` and is exactly
as reliable as a single ordinary solve.

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

### `AttributeError: 'BimodalSemantics' object has no attribute 'is_world'`

This is the crash documented above. Set `iterate: 1` (or omit the setting; `1` is the default).

### No additional certificates found (once the crash above is fixed upstream)

- Raise `back`/`mid`/`fwd` for more structural variety in the periodic segments.
- Raise `max_witnesses` if the formula has several boxed subformulas.
- Check whether your formula heavily constrains the label assignment — a highly determined
  formula may genuinely admit very few distinct certificates.

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
