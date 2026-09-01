# The `task_restriction` Verdict

**Status**: audit-only (no changes to `core.py`, `operators.py`, or `examples.py`). This document
is self-contained: it does not require the companion ledger
(`01_frame_class_and_verdict_ledger.md`) to state its own claim or its own grounds, though it
cross-references that document's Phase 2 findings where relevant.

**Verdict**: `task_restriction` remains an **independent gap**. It is not subsumed by asserting
*Seriality* and *Interpolation* — the two frame axioms the companion audit's Phase 2 concludes
must actually be added to `build_frame_constraints` (see "Stated against the corrected axiom set"
below) — and should not be treated as redundant once those two axioms land. `task_restriction` was
not enabled in the course of this audit and remains disabled.

## 1. What the constraint would assert

`task_restriction` is written but disabled in `core.py`, at the constraint definition
`code/src/model_checker/theory_lib/bimodal/semantic/core.py:807`–`835`, preceded by a soundness
analysis comment at `core.py:747`–`806` and left commented out of the returned constraint list at
`core.py:858` (`# task_restriction,     # restricts task_rel to lawful histories`). Informally, for
every triple `(s, d, u)` the abstract `task_rel` relation makes true, it demands a *witness*: some
enumerated world `w` and time `t` such that `w`'s history is in state `s` at `t` and in state `u`
at `t + d`:

```
forall s, d, u.  task_rel(s, d, u)  ->  exists w, t.  is_world(w) and w(t) = s and w(t+d) = u
```

It was disabled for solver-performance reasons: the comment records that at three or more worlds
the nested `ForAll`/`Exists` alternation causes MBQI timeouts.

## 2. Why it grounds something the frame axioms do not

`task_restriction` couples two structurally separate pieces of the encoding: the free,
uninterpreted ternary relation `task_rel` (the abstract `\Rightarrow` of the paper's frame), and
the finite enumeration `is_world`/`world_function` the Z3 solver actually builds for a given
model. Every one of the paper's `def:frame` axioms — *Seriality*, *Interpolation*, *Limit*,
*Spherical*, plus the definitional `converse` convention and the (stronger-than-required)
`nullity_identity` biconditional — is stated **purely over the abstract relation**. Confirmed by
inspection:

- Their Z3-encoding analogues (`build_nullity_identity_constraint`, `build_converse_constraint`,
  `build_forward_comp_constraint`, `core.py:280`–`394`) reference only `task_rel`, universally- or
  existentially-quantified world *states* (`z3.BitVec` terms), and durations — never `is_world` or
  `world_function`.
- Their Lean statements (`Serial`, `Interpolates`, `Spherical`, `TaskFrame.lean`'s `def:frame`
  fields, re-confirmed in the companion audit's Phase 1) are all predicates over a bare relation
  `R : W → D → W → Prop` on the carrier `W` — they have no vocabulary for "the solver's enumerated
  world-ID set" at all, because that enumeration is a ModelChecker implementation device with no
  counterpart in the paper's abstract frame `(W, \D, \Rightarrow)`.

Asserting all four missing/free axioms would therefore only ever constrain `task_rel` as an
abstract relation on the raw `BitVec[N]` state space. It supplies no mechanism forcing every
`task_rel` triple to correspond to some enumerated world's slice — that correspondence is exactly,
and only, what `task_restriction` states.

The same holds transitively for `thm:extension` itself, including under the companion audit's
Phase 2 correction that *Limit* and *Spherical* are free rather than newly asserted: it is a
statement about the *abstract* structure `(W, \D, \Rightarrow)` — "every partial history is
extended by some total world history [in the abstract sense the paper defines `H_\F` by]" — not a
claim that a *specific finite Z3 model's* `is_world` enumeration must contain a witness for every
triple that model's `task_rel` happens to satisfy. `thm:extension` and `task_restriction` answer
genuinely different questions: the former is about existence of members of `H_\F` in the abstract
frame; the latter is about self-consistency between two separate structures *within one
already-built Z3 model*. Nothing about narrowing which relations count as valid `task_rel`
instances (which is all a frame axiom does) bears on whether a *given* Z3 model's `is_world`
enumeration happens to witness every triple that model's `task_rel` satisfies.

## 3. Stated against the corrected axiom set

The companion audit's Phase 2 (`01_frame_class_and_verdict_ledger.md`, Section 1.2a) corrects the
premise this verdict is stated against: of the four axioms `thm:extension`'s proof chain consumes,
only *Seriality* and *Interpolation* must actually be newly asserted in ModelChecker;
*Limit* and *Spherical* are already free, discharged by `TaskFrame.limit_of_succOrder` and
`TaskFrame.spherical_of_finite` respectively against ModelChecker's existing encoding. This
verdict is stated against that corrected set, not against an unqualified "four missing axioms":
**even if only Seriality and Interpolation are added — nothing else — the gap `task_restriction`
addresses is untouched**, because (Section 2 above) it is untouched by *any* subset of the
`def:frame` axioms, all of which are abstract-relation-only. The verdict does not depend on how
many of the four axioms end up asserted versus free; it depends only on the structural fact that
none of the four axioms mention `is_world` or `world_function`, which Phase 2 does not disturb.

## 4. Consequence for the existing soundness analysis

The soundness analysis comment (`core.py:751`–`801`) claims that phantom `task_rel` triples — ones
with no witnessing world — do not affect operator truth values, because the `\Box`/`\Future`/
`\Past` truth conditions read only `is_world` and `world_function` array contents. Confirmed by
inspection for this audit: `grep -n "task_rel" operators.py` returns **zero matches** in the
entire file — `NecessityOperator.true_at`/`false_at`, `FutureOperator.true_at`/`false_at`, and
`PastOperator.true_at`/`false_at` (`operators.py:508`, `562`, `691`, `713`, `862`, `891`) never
reference `task_rel` at all, directly or indirectly; `NecessityOperator.true_at` quantifies
`other_world` guarded only by `semantics.is_world(other_world)` before recursing into
`semantics.true_at` at that world and the same eval time, and the tense operators route through
`semantics.ForAllTime`/`ExistsTime`, themselves guarded by `is_valid_time` and world-history array
lookups, never by `task_rel`.

Adding Seriality/Interpolation (or, per the corrected set, citing Limit/Spherical as free) does
not change what role `task_rel` plays in the truth-condition machinery — it still plays none — and
does not newly ground any triple in a concrete world, since grounding is exactly what
`task_restriction` alone would supply and none of the four axioms substitute for it. So the
existing comment's SAT/UNSAT-asymmetry conclusion — a SAT result may not transfer to the grounded
class (a `task_rel` triple used by a countermodel might have no witnessing world, so the
countermodel's story about *why* the formula is false may not correspond to any world history);
an UNSAT result *does* transfer (if no model satisfies the constraints including a phantom-tolerant
`task_rel`, none satisfies them under the strictly more restrictive grounded `task_rel` either) —
**stands, independent of this audit's other findings**.

## 5. Disposition

`task_restriction` was not enabled in the course of this audit and remains disabled, per the
task's non-goals. It should continue to be tracked as a separate, standing gap rather than
something the interpolation/seriality follow-on work (or a future certification effort building
on `thm:extension`) will incidentally close. A future task that wants to ground `task_rel` in
concrete world histories — for example, to strengthen a certification argument beyond what
`thm:extension`'s abstract existence claim provides — must address `task_restriction` (or an
equivalent grounding device) on its own terms, independent of how many `def:frame` axioms are
asserted.

## Cross-reference

See `01_frame_class_and_verdict_ledger.md`, Section 3, for the ledger's own (now-reduced) summary
pointer to this document, and Section 1.2a for the corrected asserted-vs-free axiom set this
verdict is stated against.
