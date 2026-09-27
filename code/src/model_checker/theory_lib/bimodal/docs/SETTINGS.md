# Bimodal Theory Settings Documentation

This document describes all available settings for the bimodal theory implementation in
ModelChecker under the witness-family certificate design. See `../README.md` and
`ARCHITECTURE.md` for the design these settings configure.

## Overview

The bimodal theory searches for a **witness-family certificate**: a box guess plus a small family
of labelled bi-infinite lassos, quantifier-free in Z3's own encoding. Settings control the maximum
size of that searched family, the witness-lasso budget, and the standard solver/testing knobs
every theory shares. There is no model dimension setting analogous to the retired `N` (a fixed
number of world states) or `M` (a fixed window of times): the certified model is infinite by
construction, and these settings bound only how large a *search* the solver is asked to perform.

## Example Settings

### Segment-Length Settings

- **`back`** (integer, default: `2`): the *exact* cyclic period of a lasso's `back` segment — the
  labels strictly before position `0`, repeated cyclically leftward forever with period `back`, not
  an upper bound on that period. Must be positive (`LabelledLasso.back_ne`).

- **`mid`** (integer, default: `1`): maximum length of a lasso's `mid` segment — the labels at
  positions `[0, mid)`, read directly (not repeated). May be `0`. Unlike `back`/`fwd` below, `mid`
  is read directly rather than folded by a period, so it genuinely is a maximum and pads freely.

- **`fwd`** (integer, default: `2`): the *exact* cyclic period of a lasso's `fwd` segment — the
  labels at positions `mid` and beyond, repeated cyclically rightward forever with period `fwd`,
  not an upper bound on that period. Must be positive (`LabelledLasso.fwd_ne`).

Together, `back + mid + fwd` is the number of distinct Z3 label-bit variables allocated per
`(lasso, closure formula)` pair (`WitnessRegistry`'s slot arithmetic). `WitnessRegistry.wrap()`
folds a back position by `t % back` and a forward position by `(t - mid) % fwd`, so a lasso family
whose true back-period is `nb'` (or fwd-period `nf'`) is representable at configured `back = nb`
(or `fwd = nf`) **if and only if `nb'` divides `nb`** (respectively `nf'` divides `nf`). Raising
`back` or `fwd` therefore does **not** monotonically enlarge the search: it changes *which* periods
are representable, and can discard a family a smaller value represented. `mid` is not affected —
positions `[0, mid)` are read directly with no modulo, so raising `mid` does monotonically enlarge
the search. Measured against the live search: one formula is SAT at `(back, mid, fwd) = (3, 1, 3)`
and at `(6, 1, 6)`, but genuinely UNSAT (`timeout=False`, sub-second runtimes, not a timeout) at
`(4, 1, 4)` and `(5, 1, 5)` — exactly as `6 divides 3` and `6 divides 6` while `6` divides neither
`4` nor `5` predicts.

### Witness Budget

- **`max_witnesses`** (integer or `None`, default: `None`): optional cap on the number of distinct
  witness-lasso indices `WitnessRegistry.allocate_witness_lasso` will ever hand out. `None` (the
  default) is uncapped — one witness lasso per boxed subformula guessed false. Lower this only to
  bound solver cost on formulas with many boxed subformulas; it can make the search
  under-complete for that formula (fewer witness lassos than false boxes need is unsatisfiable by
  construction, not merely slow).

### Solver Settings

- **`max_time`** (number, default: `1`): maximum time in seconds for the Z3 solver to search for a
  certificate.

- **`expectation`** (boolean, default: `True`): expected result for testing — `True` if a
  certificate should be found, `False` if the search should report none.

- **`iterate`** (integer, default: `1`): number of distinct certificates to search for. See
  `ITERATE.md` for what "distinct" means under this encoding (exact label/guess difference, not
  full isomorphism rejection).

- **`solver`** (string, default: `'z3'`): solver backend, `'z3'` or `'cvc5'`.

## General Settings

The bimodal theory defines **no** bimodal-specific general (display) setting. The retired
`align_vertically` option no longer applies: the certificate printer shows each lasso as a single
`(back)^w | mid | (fwd)^w` line (see `../README.md`'s "Sample Output"), so there is no vertical/
horizontal layout choice to make. All standard general settings (`print_constraints`, `print_z3`,
`save_output`, `maximize`, etc.) apply unchanged; see the
[main settings documentation](../../settings/README.md).

## Usage Examples

### Default (small) search

```python
bimodal_default_settings = {
    'back': 2,
    'mid': 1,
    'fwd': 2,
    'max_time': 1,
}
```

### Formula needing a longer periodic segment

```python
bimodal_longer_period_settings = {
    'back': 3,
    'mid': 2,
    'fwd': 3,
    'max_time': 10,
}
```

Note: `3` here is a multiple of the period `3` this illustration targets, not simply "larger than
`2`". See the Segment-Length Settings explanation above — raising `back`/`fwd` without regard to
divisibility can lose a countermodel a smaller value found.

### Formula with several boxed subformulas, witness budget bounded

```python
bimodal_bounded_witness_settings = {
    'back': 2,
    'mid': 1,
    'fwd': 2,
    'max_witnesses': 4,
    'max_time': 10,
}
```

### Expecting no certificate (a theorem)

```python
bimodal_theorem_settings = {
    'back': 2,
    'mid': 1,
    'fwd': 2,
    'expectation': False,  # Expect no certificate within these bounds
    'max_time': 5,
}
```

## Theory-Specific Behavior

1. **Segment-length search, not a fixed model size**: `back`/`mid`/`fwd` bound how much periodic
   label data the solver may allocate per lasso; the model a found certificate denotes is always
   infinite (see `ARCHITECTURE.md`).
2. **Witness lassos are allocated on demand**: one is requested only when a boxed subformula is
   guessed false; `max_witnesses` caps that allocation.
3. **No task-transition setting**: the shift relation between `(lasso, position)` points holds by
   construction of the certified `ShiftSet`, not via an asserted transition axiom, so there is no
   analogue of the retired `task_restriction`/`task_minimization` constraints to toggle.

## Tips and Best Practices

1. **Start with the defaults** (`back=2, mid=1, fwd=2`): every one of the theory's 53 examples,
   including the previously-excluded MF axiom and BX7 linearity theorems, decides correctly at
   these defaults in well under 50ms.
2. **Choose `back`/`fwd` as a multiple of the period needed, don't just raise them**: because
   `back`/`fwd` are exact periods, not maxima, a larger value is not automatically at least as good
   as a smaller one — it must be a multiple of the period the refutation needs, or the family that
   period represents is lost. When the needed period isn't known in advance, try several candidate
   lengths rather than a single larger one. `mid` has no such constraint and may be raised freely
   (it is not a world/time count either way — `N`/`M` no longer exist).
3. **Use `max_witnesses` only to bound cost, not to force a specific witness structure**: an
   overly small cap makes the search under-complete rather than simply faster.
4. **`iterate` finds distinct label/guess assignments, not guaranteed non-isomorphic models**: see
   `ITERATE.md` before relying on `iterate: N` for exhaustive exploration.

## See Also

- [General Settings Documentation](../../settings/README.md)
- [Bimodal Theory README](../README.md)
- [Architecture](ARCHITECTURE.md)
- [Adequacy](ADEQUACY.md)
