# Search Period Coverage: the divisor-period gap, three routes, and the decision

This document records a decision about the certificate search's coverage of back/forward periods
below a configured bound: what the gap is, three routes considered for closing it, why one is
recommended, and the staged path for building it. It extends `ADEQUACY.md` section 7.1's item
(iii-a) rather than restating that section's proof obligations.

## 1. The fact

`WitnessRegistry.wrap()` (`semantic/witness_registry.py`) maps a position `t < 0` to slot
`t % back`, and symmetrically maps a position `t >= mid` to slot
`back + mid + ((t - mid) % fwd)`. Two positions therefore share a slot -- and so are backed by
the identical Z3 Boolean via `bit()` -- exactly when they are a multiple of `back` (or `fwd`)
apart. The direct consequence: **a family whose back-period is `p` is representable at a
configured `back = n` if and only if `p` divides `n`.** The same holds for `fwd`/forward-period;
`mid` has no periodicity at all (it is a direct-read segment, `label(t) = mid[t]` for
`0 <= t < mid`), so it never participates in this gap.

This makes the searched space **non-monotone** in `back`/`fwd`: raising `back` from `4` to `5`
does not enlarge what is representable in any uniform sense, because divisibility is not
monotone. A period-3 family is representable at `back = 3` and `back = 6` (`3 | 3`, `3 | 6`) but
genuinely unrepresentable -- not merely unsearched, but forced to a direct label conflict, hence
UNSAT rather than inconclusive -- at `back = 4` and `back = 5` (`3 \nmid 4`, `3 \nmid 5`).

**Where this is now pinned as a machine-checked fact**, at two levels:

- `tests/unit/test_witness_registry.py`'s `TestWrapFoldsByExactPeriod` pins the arithmetic
  directly (`wrap()`'s divisor behaviour) and the resulting identity/non-identity of the `bit()`
  Booleans it backs.
- `tests/integration/test_search_period_coverage.py` pins the end-to-end consequence: a period-3
  premise chain SAT at `(back, mid, fwd) = (3, 1, 3)` and `(6, 1, 6)`, genuinely UNSAT
  (`timeout is False` at every point) at `(2, 1, 2)`, `(4, 1, 4)` and `(5, 1, 5)`; a period-2
  chain gives the counterpart direction, SAT at `(2, 1, 2)` and UNSAT at `(3, 1, 3)`, so the
  phenomenon is shown in both directions rather than by one formula that happens to divide out
  favourably.

Neither test module is a claim of encoding *incompleteness* in `ADEQUACY.md` section 7.3's sense:
the encoder faithfully encodes the label family at the segment lengths it is configured with. The
gap is in what those lengths *mean* as a proxy for "every family up to bound `n`", which is the
question `ADEQUACY.md` section 7.1's condition (iii) asks.

## 2. Two corrections to the question as posed

**(1) "Union over the divisors of a bound" is already today's behaviour at a single bound, not a
change.** At a fixed `back = n`, the search already represents every family whose period divides
`n` -- that is exactly what `wrap()`'s modular arithmetic does. The literal request "cover all
divisor-periods up to each bound" is trivially true for the single bound `n` itself, since every
`p <= n` that matters is a divisor of *some* value in `[1, n]`... but not necessarily of `n`.
The version that actually changes behaviour is the **bounded sweep**: search every
`back' in [1, back]` (and independently `fwd' in [1, fwd]`), not merely the one configured
`back`. That sweep is what section 3 below recommends; "union over divisors of the bound" is
loose language for it and should not be read as already-satisfied by the single-bound case.

**(2) Neither candidate route touches the certificate wire format or the Lean-side re-checker.**
`LabelledLasso.nb`/`nm`/`nf` (`semantic/certificate.py`) are `len(self.back)`/`len(self.mid)`/
`len(self.fwd)` -- properties derived from the *exported label arrays' actual lengths* at
serialization time, never from the search's configured `back`/`mid`/`fwd` settings directly.
`recheck`'s windows (`_coherence_window`, `_box_window`) are computed from those same
per-lasso `nb`/`nm`/`nf` properties. A route that changes how the search is configured or run
changes nothing about what gets exported or how the wire format's consumer re-derives its
windows -- both already take segment lengths from the emitted certificate, not from the search's
settings. This closes a cost line the original question raised for routes (b) and (c) alike:
neither has a wire-format or Lean-re-checker cost.

## 3. Three routes compared

**(a) Leave exact-period semantics; document and rely on a user-facing rule.** Cost: zero
implementation. Buys: nothing beyond what is already true. `ADEQUACY.md` section 7.1's condition
(iii) stays undischargeable as worded ("a demonstration that this repository's search
*represents* the compressed family at the configured `back`/`fwd`/`mid`") -- documentation alone
cannot make a representation claim true. This route was already effectively in place before this
task (the gap was described in prose, in `ADEQUACY.md` §7.1 and the discovering task's report,
with no regression pin); the pins added by this task close the "documented but unverified"
half of that gap, but do not close condition (iii) itself.

**(b) Bounded sweep: search `back' in [1, back] x fwd' in [1, fwd]` with `mid` fixed, take the
union of verdicts.** `mid` needs no sweep at all -- it is not periodic, so every `mid' <= mid`
already searched is not a distinct case, and sweeping it would only re-run the identical
direct-read segment at a shorter length for no additional coverage. This makes the sweep
**quadratic**, `O(back * fwd)` solver calls, not cubic in the three settings together. Every
call is:

- built with the existing `WitnessRegistry(back', mid, fwd', closure)` constructor, unchanged;
- encoded with the existing `WitnessConstraintGenerator`, unchanged -- (C1)-(C4) and the one-hot
  `sel` target selector are untouched line-for-line, since the sweep varies only the *lengths*
  passed to construction, never the generator's clause shapes;
- independently re-checked by the existing `certificate.recheck`, unchanged, since (per section 2
  above) `recheck` reads lengths from the emitted certificate, not from search settings.

Cost: a new sweep driver (not part of this task -- see section 5) plus `O(back * fwd)` times the
per-call solve cost, run at each call's own `(back', mid, fwd')` triple rather than the single
configured one. Buys: condition (iii)'s representation claim becomes true by construction --
every period `p <= back` (respectively `<= fwd`) is representable at *some* call in the sweep,
because `p` divides itself, so the call at `back' = p` covers it.

**(c) Reformulate the encoding so a bound means "period at most n" directly.** Rather than one
fixed period, encode a single call whose satisfying assignments range over every lasso with
`nb' <= back` -- effectively unioning the period lengths inside one Z3 instance instead of across
several. Cost: `WitnessRegistry` would need new selector variables (which of the `back`-many
candidate periods a lasso "actually" uses) and `WitnessConstraintGenerator` would need new
clauses relating those selectors to which `wrap()` arithmetic applies -- both (C1)-(C4)'s clause
shapes and the one-hot `sel` selector's completeness argument would need to be re-derived and
re-verified against `ADEQUACY.md` section 7.3's exhaustive-enumeration test, since they are
calibrated against the *current* fixed-period `wrap()` today. As established in section 2, this
route does **not** touch the certificate wire format or the Lean re-checker either -- that cost
line, present in the task description's original framing, does not hold for either (b) or (c).
Buys: the same representational coverage as (b), concentrated into one harder Z3 instance instead
of several easy ones, for the same asymptotic search space.

## 4. The decision: route (b), the bounded sweep

Route (b) is recommended. Proportionality argument: `ADEQUACY.md` section 7.2's frame-class gap
(A0) permanently caps what any certificate search can claim -- ℤ-time validity, never the paper's
full generality -- and section 7.1's compression obligation (A1) is `[NOT STARTED]`. Discharging
condition (iii) via route (b) costs zero changes to `WitnessRegistry`, `WitnessConstraintGenerator`
or `certificate.py`, and leaves every existing completeness argument for (C1)-(C4) and the one-hot
`sel` selector intact. Route (c) buys nothing route (b) does not, at the cost of new clause shapes
in three modules and a re-established encoding-completeness argument, for the identical
asymptotic search space -- concentrating the same work into one harder instance is not a win when
the permanent A0 ceiling and the still-open A1 already bound how much condition (iii)'s discharge
is worth. Route (a) is declined outright: it cannot discharge a representation claim by
documentation alone.

### The asymmetric cost that gates any default-behaviour change

The sweep's early-exit behaviour is asymmetric between SAT and UNSAT-seeking examples. A
countermodel-seeking example (the common case: `expectation: True`, looking for *some* certificate)
can stop the sweep at the first `(back', fwd')` call that returns SAT -- often the very first
call, at `back' = fwd' = 1`. A **theorem-style example** (`expectation: False`, asserting no
certificate exists at any period up to the bound) has no such early exit: it must run every one
of the `back * fwd` calls to UNSAT before the sweep as a whole can report UNSAT, paying the full
multiplicative cost on every run. This is the single fact that must be measured -- against the
existing 53-example suite, with particular attention to its theorem-style examples -- before any
sweep-driven behaviour ships as a default, and it is recorded here as the named blocking
measurement rather than left implicit.

## 5. Staged path (not built by this task)

1. Build the sweep driver: a function that takes a closure, premises/conclusions and
   `(back, mid, fwd)`, runs `WitnessRegistry`/`WitnessConstraintGenerator`/solve at every
   `(back', mid, fwd')` for `back' in [1, back]`, `fwd' in [1, fwd]`, and returns the union
   verdict (SAT as soon as any call is SAT; UNSAT only once every call is UNSAT with no timeout).
2. Expose it as an **opt-in** setting (e.g. a `search_mode` value), never a changed default --
   the asymmetric theorem-side cost (section 4) makes an unconditional default change a regression
   for exactly the example shape most likely to rely on a negative result.
3. Benchmark the driver against the 53-example suite, with explicit attention to theorem-style
   (`expectation: False`) examples and their wall-clock multiplier.
4. Once benchmarked, re-derive `ADEQUACY.md` section 7.1 condition (iii) as discharged under the
   sweep -- update (iii-a) to record the sweep as built rather than merely named -- contingent on
   A1 (the compression bound) having landed, since (iii) is stated relative to that bound.
5. Respect the two-phase certificate-emission idempotency guard (`finalize_certificate`'s
   documented idempotence, `semantic/core.py`) when constructing more than one
   `WitnessRegistry` per solve inside the sweep driver -- each `(back', mid, fwd')` call needs
   its own registry construction, not a shared, mutated one.

## Open obligations

- The sweep driver itself (staged path step 1).
- The opt-in setting exposing it (step 2).
- The benchmark against the 53-example suite, with particular attention to the theorem-side
  multiplicative cost (step 3).
- Re-deriving `ADEQUACY.md` section 7.1 condition (iii) as discharged, once A1 lands (step 4).
- Respecting the two-phase certificate-emission idempotency guard when the driver constructs more
  than one registry per solve (step 5).
