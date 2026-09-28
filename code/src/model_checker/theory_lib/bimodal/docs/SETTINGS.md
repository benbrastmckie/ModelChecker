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

- **`verify`** (string, default: `'auto'`): item 1's output gate
  (item 1's output gate) — see "## Certificate Verification" below for the
  full contract.

## Certificate Verification

The mandatory Python re-check (`semantic/model.py`'s `recheck` guard, always on, not controlled
by this setting) decides `(C1)`-`(C4)` against this repository's own code before a certificate is
ever reported — but it cannot catch a defect shared between the Z3 encoder and `recheck` itself,
since both are this repository's code. `verify` controls a *second*, independent leg: a
standalone Lean-built `check_certificate` binary (`semantic/checker.py`), run against the same
certificate. Measured cost of that second leg when the binary is invoked directly: **~50ms**, not
the ~2.2s a `lake exe check_certificate` invocation would cost — see `semantic/checker.py`'s
module docstring for the measurement and why it invokes the built binary directly rather than
through `lake`.

### The three values

- **`'off'`**: no independent check is attempted at all — the checker is never even asked to
  resolve. The mandatory Python re-check still runs (it is unconditional, not part of this
  setting). Fastest option; equivalent to today's behavior before this setting existed.
- **`'auto'`** (the default): the independent check runs whenever a checker resolves. The
  countermodel is *always* reported — absence of a checker never fails a solve — labelled
  according to whether the independent leg ran.
- **`'required'`**: a countermodel that cannot be independently checked is **withheld**: model
  construction raises an error instead of reporting it, naming how to obtain a checker (see
  "Availability" below).

An unknown value is rejected immediately when the example is built (fail-fast), not once a solve
is under way.

### The three output states

Exactly the wording `semantic/model.py`'s `print_certificate`/`print_evaluation` render, on the
`Verification:` line:

1. **Independently checked** (`verify` in `{'auto', 'required'}`, a checker resolved and
   answered): *"independently checked — Lean constructed a `WitnessFamily.Refutes` term for this
   certificate by applying a compile-time kernel-checked implication to four run-time decisions
   (acceptance: `entailment`\[, checkout `<HEAD>`\])"*. This is deliberately **not** worded as "a
   kernel-checked proof for this particular certificate" — that phrase belongs to a reserved
   third `Acceptance` value (per-certificate kernel checking by re-elaboration) that nothing this
   checker produces today; see `BimodalTools/CertificateImport.lean`'s `Acceptance` docstring.
   `acceptance` is one of `decided` (four `Decidable` instances returned `true`) or `entailment`
   (Lean additionally constructed the compile-time implication term); the optional `checkout`
   suffix records the `BIMODAL_LOGIC_PATH` checkout's HEAD commit as **provenance**, not as an
   enforcement mechanism (see "Availability" below for why).
2. **Python-re-checked only** (`verify: 'auto'`, no checker resolved): *"re-checked by this
   repository's own pure-Python decision procedures only (no independent checker available:
   `<reason>`)"*. This is the mandatory re-check's own result, reported honestly as not
   independently corroborated — **not** a weaker claim about the countermodel itself. See
   `docs/ADEQUACY.md` section 7.4's "An unchecked countermodel is not a validity claim either".
3. **Independent check skipped** (`verify: 'off'`): *"independent check skipped ('verify':
   'off'); re-checked by this repository's own pure-Python decision procedures only"*.

`verify: 'required'` never reaches state 2: a countermodel that would otherwise render state 2 is
withheld instead, with an error naming the unavailability reason and how to obtain a checker.

### Availability — no Lean toolchain required

Only a **checker binary** is required to reach state 1 above, never a Lean toolchain. Measured
for comparison: a full BimodalLogic checkout with its Lean toolchain occupies roughly 17GB
(`~/.elan`) plus 9.2GB (`.lake/packages`) — against a checker binary that ships in a wheel whose
*other* contents alone are 1.14MiB. `semantic/checker.py`'s resolver tries, in order:

1. **`BIMODAL_CHECKER_BIN`** — an explicit path to a standalone checker binary. The most direct
   route: obtain a `check_certificate` binary from wherever it is distributed (see the
   certificate-wire hardening task's own packaging decision for the release-artifact route this
   repository does not itself publish) and point this variable at it.
2. **The per-user cache location**: `$XDG_CACHE_HOME/model_checker/bimodal/check_certificate`
   (`~/.cache/model_checker/bimodal/check_certificate` when `XDG_CACHE_HOME` is unset) — the
   location an out-of-band installer would populate, checked automatically with no configuration.
3. **A `BIMODAL_LOGIC_PATH` checkout** (or `~/Projects/BimodalLogic` when unset), at
   `.lake/build/bin/check_certificate`, invoked directly. This route *does* need the checkout to
   have been built once (`lake build check_certificate` inside it), which does need the Lean
   toolchain — it exists for BimodalLogic developers working against a live checkout, not as the
   recommended path for an ordinary user.
4. Unavailable — `verify: 'auto'` reports state 2 above; `verify: 'required'` withholds.

**Optional integrity pinning**: when a SHA-256 digest is configured — the `BIMODAL_CHECKER_SHA256`
environment variable, or a `<binary>.sha256` file beside a cached or explicit binary — a resolved
binary whose digest does not match is refused before it is even invoked. Absent any configured
digest, no check is performed; this is the hook an out-of-band artifact-distribution route needs,
not a new requirement on every user.

**Why a commit pin is not the enforcement mechanism**: a checkout resolution's `checkout` field
(state 1 above) records that checkout's HEAD commit as provenance only. A commit pin cannot
prevent a checkout from being rebuilt at a different, incompatible commit; the **capability
handshake** can and does — a resolved binary is accepted only if its response to a trivial probe
certificate carries `status: "countermodel"`, an `acceptance` value in the known vocabulary, and
an `echo` matching the bytes sent bytewise. See `semantic/checker.py`'s module docstring for the
full handshake contract.

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
