# Research Report: Task #192

**Task**: 192 - A2 proof-vs-implementation gap report
**Started**: 2026-09-26T16:31:00Z
**Completed**: 2026-09-26T17:10:00Z
**Effort**: research (documentation-only deliverable; no source/test changes)
**Dependencies**: None
**Sources/Inputs**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (sections 1, 2, 5.2, 5.3, 6.1-6.3, 7.3, 7.4)
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` (whole document; this task builds on and does not restate it)
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` (module docstring and all four constraint emitters)
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` (`_coherence_window`, `_box_window`, `_scan_forward_bound`, `_scan_backward_bound`, `recheck`)
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (`finalize_certificate`, `_premise_behavior`, `_conclusion_behavior`, `extract_certificate`)
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py` (`target_window`, `bit`, `wrap`)
- `code/src/model_checker/theory_lib/bimodal/semantic/proposition.py` (`proposition_constraints`)
- `code/src/model_checker/models/constraints.py`, `code/src/model_checker/models/structure.py` (`_setup_solver`, constraint groups)
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`, `tests/fixtures/certificates/04_window_discriminator_coherence.json`
**Artifacts**: this report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **Core thesis, sharpened to a category argument.** `ADEQUACY.md` §5.3 states that the honest
  discharge of the periodicity obligation for the *re-checker* is a differential test, not a
  proof, because "what a re-checker implementation must additionally satisfy... is not something
  a proof discharges for a specific piece of Python code." The same argument transfers to the
  *encoder* verbatim, and this report develops **why** it transfers: a Lean theorem is a claim
  about mathematical objects (functions on `ℤ`, `Decidable` instances); "this file, run by this
  CPython interpreter against this `z3-solver` version, emits a term set logically equivalent to
  (C1)-(C4)" is a claim about a *running program*, and nothing in the Lean development speaks to
  that claim unless the program is *derived from* the theorem by a proof-preserving
  transformation (extraction, verified compilation, or reflection) — none of which exists here.
  This is the same gap CompCert closes for C compilation and that this codebase closes nowhere
  for its Z3 encoder.
- **The emitted-constraint surface is wider than "four condition emitters."** There are (at
  least) **seven emission call sites**, feeding **four solver-visible groups**, with two
  cross-cutting subtleties not previously documented: the target-selector's constraints are split
  across two different phases (early, per-premise/per-conclusion, and late, the exactly-one
  clause), and `finalize_certificate()`'s correctness depends on a call-order invariant
  (`ModelConstraints.__init__` translates every premise/conclusion before reading
  `frame_constraints`) that is enforced by the *caller*, not by `BimodalSemantics` itself.
- **The one-hot `sel` selector (D5) is provably conservative by an elementary argument presented
  here for the first time** — but the argument is itself informal, and this report uses that fact
  as a live illustration of its own thesis: even a correct pen-and-paper conservativity argument
  does not verify the ~20 lines of Python (`witness_constraints.py:137-164`) that are supposed to
  implement it.
- **`WitnessRegistry.target_window()` and `certificate._box_window`** compute the numerically
  identical range `[-nb, nm+nf)` from two independent one-line definitions in two different
  modules — the one place left where encoder and re-checker could silently diverge on a window,
  by construction rather than by oversight (`target_window` also serves the selector, which
  `_box_window` has no reason to know about).
- **The historical defect is not hypothetical.** `witness_constraints.py`'s module docstring
  documents a real, shipped bug of exactly the class this report is about: local coherence was
  once generated over the narrow `target_window()` instead of the proved wide
  `_coherence_window`, requires `nb=2` to exhibit, and was caught by the re-checker's fail-fast
  differential (ADEQUACY.md §6.2), never by a proof and never by the standing A2-triangle test —
  which fixes `back=mid=fwd=1` and is therefore, provably, blind to it.
- **The trust-base corollary (ADDENDUM).** Because (C1)-(C4) are decidable, S3 is discharged by
  *deciding* the antecedent on every reported certificate, twice, independently — not by proving
  the producer correct. The Z3 encoder, the decoder, and Z3 itself are consequently **outside the
  soundness trust base**: an encoder defect can only cost completeness (a silent, honest "no
  certificate found") or trigger a loud rejection; it cannot manufacture a false countermodel
  report. This is why S4 (the translation), not A2 (encoding completeness), is the weakest joint
  in the direction already asserted.
- **Recommendation**: place the companion document at
  `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` (or equivalent name chosen at plan
  time), cross-referenced from `ADEQUACY.md` §7.3, building on and citing `TRUST_PIPELINE.md`
  rather than restating it. Section 8 of this report gives a complete draft structure and content
  outline the implementation phase can transcribe directly.

## Context & Scope

`ADEQUACY.md` proves the mathematics; `TRUST_PIPELINE.md` (already written, in the same
directory) walks the pipeline stage-by-stage and already states the trust-base corollary, names
the emitted-constraint surface, the one-hot selector, and the independently-defined window, and
recounts the historical narrow-window defect — all at summary depth. Per the dispatch's SCOPE
NOTE, this task's remaining scope is the **deep treatment**:

1. The full category argument for *why* a proof about mathematics cannot discharge a claim about
   what a specific piece of running Python emits (not just the assertion that it can't).
2. The complete enumeration of the emitted-constraint surface, with **each emitter's clause
   shape** written out (not just named).
3. The per-route analysis of what actually closing the gap would require, route by route.

This report does not re-derive `ADEQUACY.md`'s theorems or repeat `TRUST_PIPELINE.md`'s summary
prose; it cites both and adds the depth named above. No source or test files were changed to
produce it (documentation-only task, per the dispatch).

## Findings

### A. The category argument

`ADEQUACY.md` §5.3's own phrasing is the template: "what a re-checker implementation must
additionally satisfy — that it correctly implements the finite-window reduction it is credited
with — is not something a proof discharges for a specific piece of Python (or any other) code."
Unpacked, the argument has three steps:

1. **What the Lean theorems are about.** `coherent_iff_window`, `fulfil_iff_window`,
   `mem_all_iff_window`, `scan_forward`, `scan_backward` (`ADEQUACY.md` §5.2's table) are
   statements in the Lean type theory about mathematical functions: `LabelledLasso`, its decoding
   `lab` (via `Periodic.unrollOf`), and the `Decidable` instances built from the window collapses.
   They are machine-checked, sorry-free, and quantify over every `t : ℤ`.
2. **What "the encoder is correct" would have to mean.** For the theorems to certify anything
   about `witness_constraints.py` and `core.py:finalize_certificate`, there would need to be a
   proof-preserving link between the mathematical objects and the artifact that actually runs:
   either (a) the Python is *extracted* from a verified specification (so the theorem transports
   along the extraction), (b) the Python is verified directly against a formal semantics of the
   host language and the Z3 Python API (so a new theorem is proved *about the code*), or (c) the
   Python is checked by *reflection* inside the same kernel that proved the theorems (so the
   kernel itself certifies the translation). None of (a), (b), (c) exists in this repository, nor
   does anything resembling them exist for any Z3-emitting module here.
3. **Why "the theorems are sorry-free" therefore says nothing about the encoder.** A theorem's
   soundness is a property of a derivation in a formal system; a running program's behavior is a
   property of an interpreter, a compiled library (`z3-solver`'s C/C++ core), and a specific
   source file, none of which the theorem's statement or proof mentions. This is exactly the
   distinction a compiler-correctness project like CompCert exists to close for C compilation —
   and precisely the distinction this codebase leaves open for its own Z3 encoder. Absent one of
   (a)-(c), the strongest available evidence about the encoder is empirical: it is *decided*
   (never assumed) whether a given run's output satisfies (C1)-(C4), and it is *tested* against a
   bounded enumeration whether the encoder's aggregate verdict agrees with that decision procedure
   (§F, §G below). Both are strong, but neither is a proof, and neither generalizes past its
   own corpus/bound — the defining property of evidence rather than theorem, per
   `TRUST_PIPELINE.md`'s own four-kind table.

A useful self-check for this argument, developed in §D below: even a *correct, informal*
mathematical argument about what a constraint generator's output means (the `sel` conservativity
argument this report gives) does not itself verify the Python that is supposed to implement it —
the same gap recurs one level down, which is evidence the category distinction is not an artifact
of this report's framing but a structural fact about the relationship between proofs and code.

### B. What IS machine-checked, and what is not

**Machine-checked (Lean, sorry-free), per `ADEQUACY.md` §5.2:**

| Result | Lean location | What it establishes |
|---|---|---|
| `coherent_iff_window` | `Metalogic/Decidability/WitnessFamily/Decide.lean:335` | Local coherence over all `t:ℤ` collapses to a check over `[-2nb, nm+2nf)` |
| `fulfil_iff_window` | `Decide.lean:743` | Fulfilment collapses to the same wide window |
| `mem_all_iff_window` | `Decide.lean:809` (lasso), `:883` (family) | Box faithfulness collapses to the narrower `[-nb, nm+nf)` |
| `scan_forward` | `Decide.lean:192` | The forward witness-scan bound `max(t,nm)+nf` is exact |
| `scan_backward` | `Decide.lean:212` | The backward witness-scan bound `min(t,0)-nb` is exact |

The `Decidable` instances (`decidableLocalCoherentLab`, `decidableFulfillingLab`,
`decidableBoxFaithful`, `decidableTarget`, `Decide.lean:865,878,923,927`) are built from exactly
these collapses, computationally (no `Classical`), and are what `lake exe check_certificate`
runs.

**Structurally, not merely coincidentally, aligned with the re-checker:** `certificate.py`'s
`_coherence_window` (`certificate.py:210-213`), `_box_window` (`:216-218`),
`_scan_forward_bound` (`:221-223`), `_scan_backward_bound` (`:226-228`) are one-line
transcriptions of the theorem statements above, and `witness_constraints.py` **imports all four
directly** (`witness_constraints.py:44`, `from .certificate import _box_window,
_coherence_window, _scan_backward_bound, _scan_forward_bound`). This means the encoder and the
Python re-checker (`certificate.recheck`, `certificate.py:358`) share one definition per bound —
there is no second copy to drift, for these four. That is a structurally stronger guarantee than
a proof of agreement between two independently-written functions, because the failure mode
("the two definitions disagree") is not merely proved absent, it is *impossible by construction*.

**What is not machine-checked, and is the actual subject of this report:**

- That `witness_constraints.py`'s four constraint-emitting methods, as Python code, assemble
  Z3 term objects whose conjunction is logically equivalent (over the closure and the imported
  windows) to (C1)-(C4) as `ADEQUACY.md` §1 states them. The *windows* are shared by import; the
  *clause shapes* built from them (§C below) are hand-written Python with no corresponding Lean
  artifact and no extraction step.
- That `finalize_certificate()`'s assembly order, `_active_lassos` bookkeeping, and mutation of
  `frame_constraints` in place (§C, item 7 below) preserve that equivalence once premises,
  conclusions, and boxed subformulas are folded in.
- That the one-hot `sel` selector (§D) — structure genuinely absent from (C1)-(C4) — does not
  itself add or remove models relative to (C4)'s existential statement.
- That `WitnessRegistry.target_window()` (§E), independently defined rather than imported,
  continues to agree numerically with `_box_window` under any future edit to either.

Each of these is a claim about a *specific artifact's* behavior, not a mathematical statement, and
per §A none of them inherits strength from the Lean theorems beyond the four literally-shared
window/bound definitions.

### C. The complete emitted-constraint surface, emitter by emitter

The dispatch names "the four condition emitters" as a starting enumeration and asks for the full
surface. Tracing every path from `ModelConstraints.__init__` (`models/constraints.py:52-101`)
through `ModelStructure._setup_solver` (`models/structure.py:162-194`) to what Z3 actually
receives gives **seven emission call sites**, not four, collapsing into **four solver-visible
groups**:

**1. `local_coherence_constraints(lasso)` — (C1)** (`witness_constraints.py:92-101`, invoked once
per active lasso from `finalize_certificate`, `core.py:314-317`). For every `t` in the **wide**
window `_coherence_window(registry)` (`[-2nb, nm+2nf)`) and every `f` in the closure, emits (via
`_coherence_clause_at`, `:103-131`):

| Formula shape | Clause |
|---|---|
| `Atom` | none — deliberately unconstrained |
| `Bot` | `Not(bit(t, f))` |
| `Imp(a,b)` | `bit(t,f) == Or(Not(bit(t,a)), bit(t,b))` |
| `Box(child)` | `bit(t,f) == guess(child)` |
| `Untl(event,guard)` | `bit(t,f) == Or(bit(t+1,event), And(bit(t+1,guard), bit(t+1,f)))` |
| `Snce(event,guard)` | mirror at `t-1` |

**2. `fulfilment_constraints(lasso)` — (C2)** (`witness_constraints.py:178-206`, invoked once per
active lasso from `finalize_certificate`, `core.py:318-320`). For every `t` in the same wide
window and every `Untl`/`Snce` closure member:

- `Untl`: `Implies(bit(t,f), Or_{s=t+1}^{hi}( And(bit(s,event), bit(r,guard) for r in (t+1,s)) ))`
  with `hi = _scan_forward_bound(registry, t)`.
- `Snce`: the mirror, `lo = _scan_backward_bound(registry, t)`, scanning `s` from `t-1` down to
  `lo`.

**3. `box_faithfulness_constraints(lassos)` — (C3)** (`witness_constraints.py:218-241`, invoked
**once**, jointly across every active lasso, from `finalize_certificate`, `core.py:322-324`). For
every boxed closure member `Box(child)`, over the **narrow** window `_box_window(registry)`
(`[-nb, nm+nf)`):
- `Implies(guess(child), And(bit(i,t,child) for i in lassos for t in window))`
- `Implies(Not(guess(child)), Or(Not(bit(i,t,child)) for i in lassos for t in window))`

**4. `target_constraints([], [])` — (C4), exactly-one clause only** (`witness_constraints.py:146-
164`, invoked from `finalize_certificate` with **empty** premise/conclusion lists,
`core.py:326-328`). Over `registry.target_window()`: `Or(*sels)` and `AtMost(*sels, 1)` where
`sels = [sel(t) for t in window]`. The per-`t` guarded implications this same method can also
produce are **not** emitted here — see item 6.

**5/6. `_premise_behavior(premise)` / `_conclusion_behavior(conclusion)` — the other half of
(C4)** (`core.py:222-249`), invoked **once per premise/conclusion**, but **earlier**: from
`ModelConstraints.__init__` (`models/constraints.py:75`, `self.instantiate(...)`, which triggers
translation) — this runs *before* `BimodalStructure._setup_solver` (and therefore
`finalize_certificate`) ever executes. Each call emits, over `registry.target_window()`:
`And(Implies(sel(t), bit(0,t,tr(premise))) for t in window)` (premises) or
`And(Implies(sel(t), Not(bit(0,t,tr(conclusion)))) for t in window)` (conclusions). Each call also
has the **side effect** `_register_closure(formula)` (`core.py:218-219`), which grows
`self._known_closure` — the very closure that `finalize_certificate()` later reads
(`core.py:305-306`, `closure = self._known_closure`). **This is the call-order invariant flagged
in §B**: `finalize_certificate`'s guard (`self._certificate_finalized`) only prevents a *second*
call; nothing in `BimodalSemantics` prevents a premature *first* call before every premise and
conclusion has been translated. Correctness of "the closure is complete when `finalize_certificate`
runs" is guaranteed only by `ModelConstraints.__init__`'s fixed call order, external to the class
whose correctness depends on it.

**7. `proposition_constraints(sentence_letter)` — currently vacuous**
(`semantic/proposition.py:110-113`, invoked once per sentence letter from
`ModelConstraints.__init__:84-89`). Returns `[]` unconditionally: D4 removed `contingent`/
`disjoint` from settings, and atoms are deliberately unconstrained by design
(`proposition.py`'s module docstring, citing `ADEQUACY.md` Lemma 4's atom case as an identity, not
a clause to assert). It is nonetheless part of the surface "no extra constraint" ranges over: it
is a live hook `ModelConstraints` calls unconditionally, and any future settings change that
reintroduces per-atom constraints would flow back through exactly this path without touching
`finalize_certificate` at all.

**Assembly into what Z3 actually sees** (`models/structure.py:184-190`): the seven call sites
above collapse into exactly four solver-visible groups —
`(model_constraints.frame_constraints, "frame")` [items 1-4], `(model_constraints.model_constraints,
"model")` [item 7], `(model_constraints.premise_constraints, "premises")` [item 5],
`(model_constraints.conclusion_constraints, "conclusions")` [item 6] — each `assert_tracked`
individually for unsat-core extraction. `ModelConstraints.__init__:80` reads
`self.semantics.frame_constraints` **by reference** at construction time, while
`finalize_certificate` (called later, from `BimodalStructure`'s `_setup_solver` override,
`semantic/model.py:106-113`) still mutates the *same* list object in place
(`self.frame_constraints.extend(...)`, never `self.frame_constraints = ...`,
`core.py:314-329`) — this reference/mutation contract is what lets a two-phase design work at
all, and is itself one more thing that is true of this specific object graph by construction, not
by proof.

**Net correction to "four condition emitters":** the encoder's actual attack surface is seven
call sites (four inside `finalize_certificate`, two invoked earlier and separately per formula,
one vacuous-but-live hook), assembled through a reference-mutation contract, gated by an
externally-enforced call-order invariant. "No extra constraint" is a claim about the conjunction
of all seven, not about four self-contained functions.

### D. The one-hot `sel` selector: structure absent from (C1)-(C4), and a conservativity sketch

`ADEQUACY.md` §1 states (C4) as: `∀γ∈Γ. γ∈L₀(t₀) ∧ ∀σ∈Δ. σ∉L₀(t₀)` for *some* `t₀∈ℤ` — a bare
existential. Decision D5 (`core.py:39-42`) implements this with a **one-hot selector**: fresh
Boolean variables `sel(t)` (`witness_constraints.py:137-144`, memoized per position), an
exactly-one cardinality constraint, and guarded implications. Nothing resembling `sel` appears in
(C1)-(C4)'s statement, in the window-collapse theorems, or in the `Decidable` instances the Lean
side decides — it is pure encoding machinery, and the dispatch is correct that it is not "covered"
by the four conditions' own proofs. It needs its own argument, which this report supplies:

**Claim (selector conservativity).** Adding the `sel` machinery to an encoding of (C1)-(C3)
changes neither its satisfiability nor the set of certificates a satisfying assignment can
witness, relative to (C4)'s bare existential.

**Argument sketch:**
1. **The reduction from `∃t₀∈ℤ` to `∃ slot` is an identity, not a step that can fail.**
   `WitnessRegistry.bit(lasso, t, f)` returns the *same* Z3 variable for every `t` sharing a slot
   under `wrap` (`witness_registry.py:124-131`) — by definition, not by an argument that needs
   checking per formula. So "premises hold and conclusions fail at `t₀`" is already, for any
   fixed `t₀`, identical to the same statement about `t₀`'s representative slot; `target_window()`
   enumerates each slot exactly once. This step costs nothing to verify beyond reading `wrap`'s
   definition.
2. **The guarded implications are vacuous when `sel(t)` is false.** `Implies(sel(t), ...)` places
   no constraint on `bit(0,t,·)` unless `sel(t)` is true. So adding these clauses is a
   Skolemization of the existential — a standard, sound-and-complete "witness variable" encoding
   of `∃x. P(x)` as `∃ fresh s. (s → P(w)) ∧ s`, which changes satisfiability only if the
   Skolem variable itself is over-constrained (step 3).
3. **`Or(*sels)` (at-least-one) exactly restates the existential; `AtMost(*sels,1)` costs nothing
   extra.** If some family satisfying (C1)-(C3) makes (C4) true at one or more slots, choosing
   `sel(t*) := true` for exactly one such slot and `false` elsewhere satisfies both the exactly-one
   cardinality constraint and every guarded implication (the false slots' implications are
   vacuous; only the constraints raise no requirement on slots where `sel` is false). Conversely,
   any assignment with some `sel(t*)` true forces, via the implications, that premises hold and
   conclusions fail at `t*`'s slot — recovering (C4) directly. Neither direction is lost.

**What this argument is, and is not.** It is a correct, self-contained mathematical argument
about what the `sel`-augmented clause set means, written down here for the first time in this
codebase's documentation. It is **not** machine-checked, and per §A it does **not** verify that
`witness_constraints.py:137-164` — the actual Python implementing `sel`, `target_constraints`,
and their call sites in `_premise_behavior`/`_conclusion_behavior` — computes the terms this
argument is about (an off-by-one in `target_window()`'s bounds, a swapped `Implies` polarity
between premise and conclusion, or a stale memo in `self._sel` would each violate the
implementation while leaving this argument's premises intact and undetectable by it). This is the
report's own recursive illustration of §A's category point: even a correct informal proof about
constraint *meaning* does not discharge a claim about constraint *code*. Task 194 (already
recorded in `specs/state.json` as project 194, "close_a2_selector_and_window_drift_gaps") is
where this argument would be turned into an executable check.

### E. The one remaining independently-defined window

Three of the four window/bound functions the encoder needs are literally shared by import
(§B). The exception: `WitnessRegistry.target_window()` (`witness_registry.py:170-173`,
`range(-self.nb, self.nm + self.nf)`) and `certificate._box_window` (`certificate.py:216-218`,
`range(-lasso.nb, lasso.nm + lasso.nf)`) compute the **numerically identical** range from **two
separately written one-line formulas** in two different modules, with no shared call between
them. `certificate.py`'s own comment (visible at the site of `_box_window`'s definition, cited
verbatim in `TRUST_PIPELINE.md`) records the split as deliberate: `target_window` is reused by the
selector (§D), which has no natural place in `certificate.py`'s re-checker vocabulary, while
`_box_window` exists specifically to match `mem_all_iff_window`'s bound.

**Why this is worth naming precisely rather than folding into "the encoder is unverified" in
general:** this is a case where the two definitions currently agree, are simple enough that they
are unlikely to *silently* drift by accident today, and yet are exactly the shape of the
historical defect this report documents next (§F) — a place where "the wide/narrow window
distinction" is duplicated by hand rather than shared. If a future Lean-side revision widened or
narrowed `mem_all_iff_window`'s bound (e.g. to accommodate the stability modal work
`TRUST_PIPELINE.md`'s closing section describes as blocked-but-routed), `_box_window` would need
updating, and nothing would force a corresponding update to `target_window()` — reintroducing,
this time at the selector rather than at local coherence, precisely the class of defect §F
describes. This is the report's second illustration that "unshared window" is not an abstract
risk category but a concrete, presently-latent instance of the same failure mode that has already
occurred once.

### F. The historical defect as concrete evidence, and the standing test's blindness to it

`witness_constraints.py`'s module docstring (quoted at length; see "Why one representative
position per slot is NOT enough (corrected)", `witness_constraints.py:16-38`) records, as a fact
about this repository's own history rather than a hypothetical:

- **The defect.** An earlier version of `local_coherence_constraints` asserted the (C1)
  biconditional only over `registry.target_window()` (the narrow window, one representative
  position per slot), reasoning — falsely — that `bit`'s slot-sharing made a single representative
  clause automatically cover every position sharing that slot.
- **Why the reasoning was false.** For the two slots adjacent to `mid` (the last `back` slot and
  the first `fwd` slot), a position `t` sharing a slot does *not* imply its neighbour `t+1` (or
  `t-1`) shares a *fixed* slot across every occurrence — at `nb=2`, slot `back[1]` recurs at every
  odd-magnitude negative position (`t=-1,-3,-5,...`), but `t+1` lands in `mid` only at `t=-1` and
  back in `back[0]` (a *different* slot, generally a different truth value) at `t=-3,-5,...`. A
  single clause written at the `t=-1` representative therefore left the `t=-3` (and deeper)
  requirement completely unconstrained.
- **Minimum reproducing case.** The counterexample requires `nb=2` — it does not exist, by
  construction, at `nb=1`.
- **How it was caught.** Not by any proof, and not (per the docstring) by a dedicated unit test at
  the time — by the **pure-Python re-checker's wide-window scan** disagreeing with the encoder's
  narrow-window construction, i.e. exactly the §6.2 fail-fast differential `ADEQUACY.md` names as
  the mechanism standing between an encoder bug and a false report. The fixture
  `tests/fixtures/certificates/04_window_discriminator_coherence.json` — named
  "window_discriminator" and shaped as the `ADEQUACY.md` §5.3 differential corpus's item 2 ("a
  family failing (C1) or (C2) only at a position outside `[-nb,nm+nf)` but inside
  `[-2nb,nm+2nf)`") — is this codebase's permanent regression fixture for the *re-checker's* side
  of that distinction, though it targets the general window-collapse property rather than
  reproducing the historical encoder defect's exact `nb=2` shape.
- **The fix.** `local_coherence_constraints` now asserts the biconditional at *every* position in
  the wide window (`_coherence_window`), matching what fulfilment already did from the start
  (Phase 8) and matching the Lean-proved bound exactly.

**Why the standing A2-triangle test cannot see this defect class.**
`tests/integration/test_certificate_a2_triangle.py`'s Tier 1 is exhaustive — but only at
`back=mid=fwd=1` (`ADEQUACY.md` §7.3's stated test, and the module's own docstring). The
historical defect provably requires `nb=2` to exhibit (the module docstring's own words: "The
counterexample: with `nb=2`..."). So the standing exhaustive test, run today, would pass whether
or not this exact defect (or its analogue in a different emitter) were reintroduced — not because
the test is weak in general, but because its regime is, **by the same argument that explains the
original bug**, structurally blind to the one class of defect known to have actually occurred.
This is not a hypothetical gap in coverage; it is a **provable** gap, derivable from the
docstring's own counterexample construction, and it is the concrete justification for project 193
("extend_a2_triangle_grid_to_nb_nf_2") already recorded in `specs/state.json`.

### G. What a bounded exhaustive test does and does not establish

The A2-triangle test (`ADEQUACY.md` §7.3) is, **within its own region**, a decision, not a sample:
at `back=mid=fwd=1` and `|C|≤4`, it enumerates *every* candidate, so agreement of legs (i) and
(iii) across all of them is a complete case analysis over that finite space, not a statistical
inference from it. This is stronger than an arbitrary property test and should be stated as such.

But two limits are equally exact, not matters of degree:

1. **Nothing about the result transfers to a larger closure or wider window without re-running
   the enumeration there.** Exhaustiveness is a property of the specific `(back, mid, fwd, |C|)`
   tuple tested; §F shows concretely that a real defect can be invisible at one tuple and present
   at another with no continuous "coverage" connecting them — there is no monotonicity argument
   available (a defect need not get *more* likely to be caught as the grid widens in every
   dimension; it can be undetectable below a threshold and detectable at or above it, as `nb=2`
   demonstrates).
2. **Passing the test never certifies A2 as a theorem, even for the tested region, in the sense
   §A requires.** "Every candidate at this closure/length was checked and agreed" is an
   empirical fact about one test run against one version of the encoder, the re-checker, and (for
   Tier 2) `lake exe check_certificate` on this machine. A future refactor of any of the three
   could silently break the property the test currently observes; the test would then fail on its
   next run (which is exactly its intended purpose), but a passing run today says nothing about
   code not yet written. This is `TRUST_PIPELINE.md`'s "Property-tested: checked on generated or
   enumerated inputs... Evidence, bounded by what was enumerated" category, applied honestly to
   its strongest instance in this codebase.

Put together: the A2-triangle test is the best evidence this repository has for encoding
completeness at small closures, and it is complete evidence *there*. It is not, and cannot by its
nature become, a substitute for §A's missing proof-preserving link between the Lean theorems and
the running Python.

### H. The trust-base consequence of S3 (ADDENDUM)

`ADEQUACY.md` §2 states S3 as: "Whatever the search reports satisfies (C1)-(C4)," discharged "by
*deciding* the antecedent on every reported countermodel, independently, twice." Because (C1)-(C4)
collapse to finite, decidable windows (§5), this is not merely convenient — it is the design's
load-bearing property, restated precisely: **nothing in this repository has to prove the Z3
encoder correct**, because every individual output is checked, not trusted.

Tracing the consequence through §6.2's four-step verification exhaustively:

- **Encoder under-constrains or constrains wrongly** → Z3 returns something that fails to decode
  into a valid certificate, or decodes into one failing (C1)-(C4) → the pure-Python re-checker's
  fail-fast step (`ADEQUACY.md` §6.2 step 3) rejects, raising rather than reporting → a loud
  failure, never a false positive.
- **Encoder over-constrains** → Z3 returns UNSAT where a countermodel exists → the tool reports
  "no certificate found within these bounds" — which `ADEQUACY.md` §7.4 (the never-report-validity
  rule) already establishes is never a validity claim, so this cost lands entirely on
  **completeness** (A2), never on soundness.

There is no third branch: an encoder defect cannot produce a Z3-satisfying model that *also*
passes the independent re-check without genuinely denoting a certificate satisfying (C1)-(C4),
because passing the re-check *is* what "satisfying (C1)-(C4)" means, decided directly, not
inferred from the encoder's intent. **Consequently the Z3 encoder, the decoder, and Z3 itself are
not in the soundness trust base at all.** Collecting `ADEQUACY.md`'s statements (§2's obligation
table and §6's trust-base discussion): the soundness trust base is exactly **Lean's kernel** (for
S1), **the S2 transcription audit**, **the re-checker implementation** (mitigated, not eliminated,
by the dual Python/Lean check), and **the translation** (S4). This is also why **S4, not A2, is
the weakest joint** in the direction already asserted: A2's failure mode is bounded and
self-announcing (a completeness cost or a loud rejection); S4's is not — `ADEQUACY.md` §6.3
records that a translation defect is invisible to the Python/Lean round-trip by construction
(both sides consume the same already-translated `Formula`), and the box half of the translation
has no property-test coverage at all (`oracle/bimodal_logic/ground_truth.py`'s adjudicator covers
only the tense primitives).

One further honesty point the ADDENDUM asks to be stated explicitly: a `countermodel` verdict —
from the Python re-checker, from `lake exe check_certificate`, or from their agreement — says only
that the four `Decidable` instances returned `true` on the family rebuilt from the wire input. It
is **not a kernel-checked proof for that particular certificate**; `ADEQUACY.md` §6.2 makes this
comparison explicit against the tableau bridge's own `"gates"` field, and it is worth restating
here because it is easy to misread "decided by theorems" as "proved by the kernel for this
instance" — it is not; only S1 (`joint_countermodel`) is a proof, and it is a proof of the
*implication* "(C1)-(C4) ⟹ a paper countermodel exists," applied to whatever the decision
procedures certify holds of the specific rebuilt family.

### I. Per-route analysis: what closing the gap would actually require

Given §A's category argument, "closing the gap" cannot mean "prove the encoder correct" without
first creating one of the three link types §A names. Route by route:

| Route | What it would require | What it would buy | Cost/status |
|---|---|---|---|
| **(a) Extraction** | Specify the constraint generators in Lean (or another proof assistant) as functions over `LabelledLasso`/closure data, prove they emit exactly (C1)-(C4)'s conjunction, extract to Python (or another host the search can call) | Removes the encoder from "unverified" entirely; the extracted code *is* the theorem, executably | Large: needs a verified extraction pipeline targeting whatever calls into `z3-solver`'s Python bindings, or a rewrite of the search to consume an extracted term set directly. Not started; no infrastructure exists for it here. |
| **(b) Direct verification** | Formalize a semantics for the relevant Python subset and the Z3 API surface used, then prove `witness_constraints.py`/`core.py`'s actual source (not a model of it) meets the (C1)-(C4) specification | Same end state as (a) without requiring a rewrite | Arguably larger: verifying real Python against a real library's semantics is a substantial, novel undertaking with no existing tooling referenced anywhere in this codebase. |
| **(c) Reflection** | Encode the constraint-generation *algorithm* inside Lean's own kernel and have the kernel evaluate it, so the kernel's evaluation of the algorithm on a given input *is* the Python's job, checked by construction | Strongest option that reuses existing Lean infrastructure | Would still require re-implementing the generators in Lean (or `#eval`-able Lean) and does not, by itself, verify that the *actual deployed* Python matches that Lean re-implementation — reintroducing a translation obligation of its own (a second S4-shaped gap). |
| **(d) Widen the differential grid** (project 193) | Extend the A2-triangle test to `nb=nf=2`, the regime the one known defect lived in | Directly closes the *specific* blind spot §F identifies; highest empirical value per hour, per `TRUST_PIPELINE.md`'s own "What remains" table | Bounded engineering cost, already scoped as a separate task; remains evidence, not proof, per §G. |
| **(e) Selector conservativity + window sharing** (project 194) | Turn §D's argument into an executable check (e.g. a property test asserting satisfiability with some `sel[t]` true iff a re-checker-accepted family exists with target `t`), and either share `target_window`/`_box_window`'s definition or assert their agreement across the configured range | Removes both currently-informal/currently-latent items from "undocumented gap" to "checked gap" | Small, already scoped; still evidence-shaped once done, per §A — a test that the selector behaves as argued is not a proof that it always will. |
| **(f) Consume a proof-producing checker** (`TRUST_PIPELINE.md`'s own "What remains") | Make Lean's accepting branch construct `joint_countermodel` directly from a decided hypothesis, and compare a Lean-side echo of the parsed wire against the bytes sent | Removes the **re-checker** (not the encoder) from the trust base | Named in `TRUST_PIPELINE.md` as Lean-side future work; does not by itself touch the encoder side this report is about. |

**Honest ranking.** Routes (a)-(c) are the only ones that would satisfy §A's category argument on
its own terms — they alone create the missing proof-preserving link. All are substantial,
unstarted, and not currently scoped by any task in `specs/state.json`. Routes (d)-(e) are
concrete, already-scoped, and valuable, but per §G they strengthen the *evidence* for A2 within a
larger or better-understood region; they do not and cannot become a proof, however far the grid is
widened, because a finite enumeration is definitionally bounded by what it enumerates. Route (f)
addresses a different trust-base member (the re-checker, S3's own second leg) rather than the
encoder this report is scoped to.

## Decisions

- **Placement**: the companion document belongs alongside `ADEQUACY.md` in
  `code/src/model_checker/theory_lib/bimodal/docs/`, cross-referenced from `ADEQUACY.md` §7.3 (the
  A2 section), per the task description. A suggested filename is `A2_GAP.md`, chosen at plan time
  to avoid colliding with `TRUST_PIPELINE.md`'s existing name and to signal the narrower,
  A2-specific scope this task covers relative to that document's pipeline-wide summary.
- **Relationship to `TRUST_PIPELINE.md`**: the new document should open with an explicit pointer
  ("this document assumes and extends `TRUST_PIPELINE.md`'s Stage 2 discussion and the trust-base
  section; it does not restate them") and should not duplicate that document's summary-level
  prose — matching the dispatch's SCOPE NOTE.
- **Content to carry into the companion doc**: sections A-I above are written at a depth suitable
  for direct transcription; the planner/implementer should treat this report as the content draft
  rather than re-deriving it, adjusting only prose style to match `docs/`'s existing register
  (`ADEQUACY.md`/`TRUST_PIPELINE.md`'s terse, table-heavy, citation-precise style).
- **No source or test changes**: confirmed in scope by the task description ("Documentation only:
  no source or test changes"); this report likewise made none — every file:line citation above
  was produced by reading, not editing.

## Risks & Mitigations

- **Risk**: the companion document, if written loosely, could be read as claiming the encoder
  *is* verified (misreading "structurally aligned via shared imports" as "proved correct"). —
  **Mitigation**: §B's table above is written to keep "machine-checked" and "structurally shared
  by import" visually and terminologically distinct from "not machine-checked," and the companion
  doc should preserve that distinction as sharply.
- **Risk**: restating `TRUST_PIPELINE.md`'s summary content wholesale, defeating the SCOPE NOTE's
  purpose. — **Mitigation**: this report cites rather than restates `TRUST_PIPELINE.md` throughout
  and adds only the three deep-treatment layers the SCOPE NOTE names (§A, §C's full clause-shape
  enumeration, §I's per-route table).
- **Risk**: the selector-conservativity argument (§D) or the window-independence note (§E) reading
  as more settled than they are, given they are presented here for the first time. —
  **Mitigation**: both sections explicitly flag their own status (informal, unverified,
  recursively subject to §A) rather than presenting them as closed.

## Context Extension Recommendations

- **Topic**: none identified beyond what is already covered by `ADEQUACY.md`, `TRUST_PIPELINE.md`,
  and this repository's own docs. This is a `markdown`/`documentation` task within an existing,
  well-documented theory package; no gap in `.claude/context/` was found during this research that
  would generalize beyond this one task.

## Appendix

### Search queries / exploration used

- `grep -n "^#" ADEQUACY.md` / `TRUST_PIPELINE.md` (section maps)
- `grep -n "^    def \|^class " witness_constraints.py` (emitter inventory)
- `grep -n "def _coherence_window\|def _box_window\|..." certificate.py -A 15` (window/bound bodies)
- `grep -n "def target_window" -A 20 witness_registry.py`
- `grep -n "proposition_constraints\|frame_constraints" models/constraints.py`
- `grep -n "_setup_solver\|all_constraints\|solver.add" models/structure.py`
- `find ... -iname "*a2_triangle*" -o -iname "*lean_agreement*"`
- Direct reads of `core.py:1-400` (D3-D9 decision comments, `finalize_certificate`,
  `_premise_behavior`/`_conclusion_behavior`, `extract_certificate`)
- Direct read of `test_certificate_a2_triangle.py`'s module docstring and
  `tests/fixtures/certificates/04_window_discriminator_coherence.json`

### Key file:line references (for the implementer)

- `witness_constraints.py:16-38` — module docstring, the historical defect narrative
- `witness_constraints.py:92-131` — (C1) `local_coherence_constraints`/`_coherence_clause_at`
- `witness_constraints.py:137-164` — (C4) `sel`/`target_constraints`
- `witness_constraints.py:178-206` — (C2) `fulfilment_constraints`
- `witness_constraints.py:218-241` — (C3) `box_faithfulness_constraints`
- `certificate.py:210-228` — `_coherence_window`, `_box_window`, `_scan_forward_bound`,
  `_scan_backward_bound`
- `core.py:39-42, 279-329` — D5 comment; `finalize_certificate`
- `core.py:222-249` — `_premise_behavior`/`_conclusion_behavior`
- `core.py:340-395` — `extract_certificate`
- `witness_registry.py:124-131, 170-173` — `wrap`, `target_window`
- `models/constraints.py:52-101` — `ModelConstraints.__init__`, `all_constraints` assembly
- `models/structure.py:162-194` — `_setup_solver`, the four tracked constraint groups
- `proposition.py:27-32, 110-113` — `proposition_constraints`'s vacuity, by design (D4)
- `ADEQUACY.md:33-88` (§1-2), `:342-483` (§5-6.3), `:593-619` (§7.3-7.4)
- `TRUST_PIPELINE.md` (whole document; cited throughout, not restated)
