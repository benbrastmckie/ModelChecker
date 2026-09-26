# The A2 Gap: Why the Encoder's Correctness Is Not a Theorem

## 1. What this document is

`ADEQUACY.md` states and proves the mathematics: the (SOUND) theorem in full, and the (ADEQ)
direction's three components plus one permanent limit, `A2` (encoding completeness) among them.
`TRUST_PIPELINE.md` walks the whole pipeline stage by stage and already states, at summary depth,
the trust-base corollary that follows from obligation S3, names the full emitted-constraint
surface, the one-hot selector, the window- and bound-sharing between encoder and re-checker, and
the historical narrow-window defect. This document assumes both and restates neither; it is the deep treatment
those two documents point at but do not themselves give: the full category argument for *why* a
Lean theorem cannot discharge a claim about what a specific piece of running Python emits, the
complete emitted-constraint surface with each emitter's clause shape written out, and a per-route
analysis of what actually closing the gap would require.

The thesis is inherited directly, and transferred one component over, from `ADEQUACY.md` section
5.3's own sentence about the periodicity obligation for the re-checker: what a re-checker
implementation must additionally satisfy — that it correctly implements the finite-window
reduction it is credited with — "is not something a proof discharges for a specific piece of
Python (or any other) code." Section 2 below states, argument and all, why that same sentence
holds verbatim for the *encoder*: what is missing for A2 is not mathematics — the mathematics is
proved, sorry-free, in `ADEQUACY.md` section 5 — but a proof that the running Python emits what
that mathematics specifies.

This document extends `ADEQUACY.md` sections 5.2, 5.3 and 7.3, and `TRUST_PIPELINE.md`'s Stage 2
and trust-base discussion. It does not re-derive `ADEQUACY.md`'s theorems, lemmas or Lean citation
table, and it does not restate `TRUST_PIPELINE.md`'s summary-level content; every claim already
made there is cited and then extended, never re-explained from scratch.

## 2. The category argument

`ADEQUACY.md` section 5.3's template, unpacked, has three steps.

**Step 1 — what the Lean theorems are about.** `coherent_iff_window`, `fulfil_iff_window`,
`mem_all_iff_window`, `scan_forward` and `scan_backward` (`ADEQUACY.md` section 5.2's table) are
statements in Lean's type theory about mathematical objects: `LabelledLasso`, its decoding
function `lab`, and the `Decidable` instances built from the window collapses those theorems
establish. They are machine-checked, sorry-free, and universally quantified over every `t : ℤ`.
Nothing in their statement or proof mentions an interpreter, a compiled library, or a source file.

**Step 2 — what "the encoder is correct" would have to mean.** For those theorems to certify
anything about `semantic/witness_constraints.py` and `semantic/core.py`'s `finalize_certificate`,
there would need to be a proof-preserving link between the mathematical objects the theorems are
about and the artifact that actually runs. There are exactly three such links, and this repository
has none of them:

- **(a) Extraction.** The Python is mechanically extracted from a verified specification, so the
  theorem transports along the extraction step.
- **(b) Direct verification.** The Python is verified directly against a formal semantics of the
  host language (CPython) and the Z3 Python API's actual behavior, producing a new theorem *about
  the code itself*.
- **(c) Reflection.** The Python's algorithm is re-encoded inside the same kernel that proved the
  Lean theorems, and the kernel evaluates it, so the kernel's evaluation of the algorithm on a
  given input *is* the check.

**Step 3 — why sorry-freeness therefore says nothing about the encoder.** A theorem's soundness is
a property of a derivation in a formal system. A running program's behavior is a property of an
interpreter, a compiled library (`z3-solver`'s C/C++ core), and a specific source file — none of
which the Lean statement or proof mentions, absent one of (a)–(c). This is exactly the distinction
a compiler-correctness project like CompCert exists to close for C compilation: CompCert's theorem
is not "the C standard is a sound type system," it is "this specific compiler, as compiled code,
preserves the semantics of the programs it translates" — a claim about an artifact, proved by
relating the artifact to a formal semantics of its input and output languages. This codebase
closes that gap nowhere for its own Z3 encoder. Absent (a), (b) or (c), the strongest available
evidence about the encoder is empirical: it is *decided*, never assumed, whether a given run's
output satisfies (C1)–(C4) (section 9 below), and it is *tested* against a bounded enumeration
whether the encoder's aggregate verdict agrees with that decision procedure (sections 7–8 below).
Both are strong. Neither is a proof, and neither generalizes past its own corpus or bound —
`TRUST_PIPELINE.md`'s own distinction between "theorem" and "property-tested" evidence, restated
here for its sharpest instance.

**A recursive self-check.** Section 5 below gives a correct, self-contained, informal
conservativity argument for the one-hot selector — recorded in this codebase's documentation for
the first time. That argument does not itself verify the Python that is supposed to implement it.
The gap recurs one level down, inside this very document: even a correct pen-and-paper argument
about what a constraint generator's output *means* does not discharge a claim about what the
constraint-generating *code* does. This is not a flaw in section 5's argument; it is evidence that
the category distinction above is a structural fact about the relationship between proofs and
code, not an artifact of this document's framing.

## 3. What is machine-checked, what is shared by import, what is neither

**(i) Machine-checked in Lean, sorry-free.** `coherent_iff_window`, `fulfil_iff_window`,
`mem_all_iff_window`, `scan_forward`, `scan_backward` (`ADEQUACY.md` section 5.2), and the four
`Decidable` instances built computationally from exactly these collapses (`decidableLocalCoherentLab`,
`decidableFulfillingLab`, `decidableBoxFaithful`, `decidableTarget`) — the instances
`lake exe check_certificate` runs. These are statements about mathematical functions, proved once
and for all, independent of any Python.

**(ii) Structurally shared by import — stronger than a proof of agreement, because there is no
second definition.** `semantic/witness_constraints.py` imports `_box_window`, `_coherence_window`,
`_scan_backward_bound` and `_scan_forward_bound` directly from `semantic/certificate.py`
(`from .certificate import _box_window, _coherence_window, _scan_backward_bound,
_scan_forward_bound`). The encoder and the pure-Python re-checker (`semantic/certificate.py`'s
`recheck`) therefore share one Python definition per bound. As of this writing,
`WitnessRegistry.target_window()` — the position window the one-hot selector uses — has also been
made to delegate directly to `_box_window` rather than recompute the same range independently
(section 6 records why this mattered and what changed). All four window/bound functions the
encoder needs are consequently shared by import; none is independently defined. This is not a
proof that independent definitions agree; it is the stronger fact that there is only one
definition to begin with, so "the two disagree" is not merely proved absent — it is impossible by
construction.

**(iii) Neither machine-checked nor shared — the actual subject of this document.** That the
clause shapes built from those windows (section 4), `finalize_certificate()`'s assembly order and
its in-place mutation of `frame_constraints` (section 4), and the one-hot selector's own clause
shapes and conservativity argument (section 5) together assemble a Z3 term set logically
equivalent to (C1)–(C4). Each of these is a claim about a *specific artifact's* behavior; per
section 2, none of them inherits strength from the Lean theorems beyond the four literally-shared
window and bound definitions in (ii). Sharing a window's *definition*, per (ii), removes the
window itself from this list; it does not verify the clauses built from it, which is why the
selector's own argument (section 5) remains here even after its window no longer does.

## 4. The emitted-constraint surface, emitter by emitter

`TRUST_PIPELINE.md`'s Stage 2 names "the four condition emitters" as a starting enumeration. The
full surface — everything "no extra constraint" in `ADEQUACY.md` section 7.3's A2 statement
quantifies over — is wider: tracing every path from `model_checker/models/constraints.py`'s
`ModelConstraints.__init__` through `model_checker/models/structure.py`'s `_setup_solver` to what
Z3 actually receives gives **eight emission call sites** — seven reachable from a single solve, plus
one more reachable only when iterating — collapsing into **four solver-visible tracked groups**.

**(1) `local_coherence_constraints(lasso)` — (C1).** Invoked once per active lasso, from
`finalize_certificate`. For every position `t` in the **wide** window `_coherence_window(registry)`
and every closure member `f`, `_coherence_clause_at` emits:

| Formula shape | Clause |
|---|---|
| `Atom` | none — deliberately unconstrained (`ADEQUACY.md` Lemma 4's atom case is an identity) |
| `Bot` | `Not(bit(t, f))` |
| `Imp(a, b)` | `bit(t, f) == Or(Not(bit(t, a)), bit(t, b))` |
| `Box(child)` | `bit(t, f) == guess(child)` |
| `Untl(event, guard)` | `bit(t, f) == Or(bit(t+1, event), And(bit(t+1, guard), bit(t+1, f)))` |
| `Snce(event, guard)` | the mirror, at `t-1` |

**(2) `fulfilment_constraints(lasso)` — (C2).** Invoked once per active lasso, from
`finalize_certificate`. For every `t` in the same **wide** window and every `Untl`/`Snce` closure
member: `Untl` emits `Implies(bit(t, f), Or_{s=t+1}^{hi}(And(bit(s, event),
*[bit(r, guard) for r in (t+1, s)])))` with `hi = _scan_forward_bound(registry, t)`; `Snce`
emits the mirror, scanning down from `t-1` to `lo = _scan_backward_bound(registry, t)`.

**(3) `box_faithfulness_constraints(lassos)` — (C3).** Invoked **once**, jointly across every
active lasso, from `finalize_certificate`. For every boxed closure member `Box(child)`, over the
**narrow** window `_box_window(registry)`: `Implies(guess(child), And(bit(i, t, child) for i in
lassos for t in window))` and `Implies(Not(guess(child)), Or(Not(bit(i, t, child)) for i in
lassos for t in window))`.

**(4) `target_constraints([], [])` — (C4), exactly-one clause only.** Invoked from
`finalize_certificate` with **empty** premise and conclusion lists. Over
`registry.target_window()`: `Or(*sels)` and `AtMost(*sels, 1)`, where `sels = [sel(t) for t in
window]`. The per-`t` guarded implications this same method can also produce are **not** emitted
here — they come from call sites (5) and (6).

**(5)/(6) `_premise_behavior(premise)` / `_conclusion_behavior(conclusion)` — the other half of
(C4).** Invoked **once per premise/conclusion**, but **earlier**: from `ModelConstraints.__init__`
(via `self.instantiate(...)`, which triggers translation), which runs *before*
`BimodalStructure._setup_solver` — and therefore `finalize_certificate` — ever executes. Each call
emits, over `registry.target_window()`: `And(Implies(sel(t), bit(0, t, tr(premise))) for t in
window)` for a premise, or `And(Implies(sel(t), Not(bit(0, t, tr(conclusion)))) for t in window)`
for a conclusion — opposite polarity, same window. Each call also has the side effect
`_register_closure(formula)`, which grows `self._known_closure` — the very closure
`finalize_certificate()` later reads.

**This is the call-order invariant.** `finalize_certificate`'s guard (`self._certificate_finalized`)
prevents only a *second* call; nothing in `BimodalSemantics` prevents a premature *first* call
before every premise and conclusion has been translated. That "the closure is complete when
`finalize_certificate` runs" holds at all is guaranteed only by `ModelConstraints.__init__`'s fixed
call order — `self.instantiate(...)` and the premise/conclusion translations that follow it run to
completion before `ModelStructure` (and therefore `_setup_solver`) is ever constructed — a fact
external to the class whose correctness depends on it.

**(7) `proposition_constraints(sentence_letter)` — currently vacuous, but live.** Invoked once per
sentence letter, unconditionally, from `ModelConstraints.__init__`. Returns `[]` unconditionally:
atoms are deliberately unconstrained by design (`ADEQUACY.md` Lemma 4's atom case being an
identity, not a clause to assert). It is nonetheless part of the surface "no extra constraint"
ranges over, because `ModelConstraints` calls it unconditionally, and any future settings change
reintroducing per-atom constraints would flow through exactly this path without touching
`finalize_certificate` at all.

**(8) `IterativeModelSearch._pin_theory_specific_values` (`iterate.py:190`) — model-iteration
pinning, outside the single-solve path.** Invoked once per requested next model, from the shared
iteration engine's `build_new_model_structure` hook, on a freshly-constructed semantics instance,
after that instance's own `finalize_certificate()` has already run once (called defensively at
`iterate.py:231` to allocate every bit/guess/lasso before pinning). For every `_bits`/`_guesses`
Z3 variable and every `sel(t)` for `t in registry.target_window()`, evaluates the variable
against the previous model and appends the resulting unit literal (`var` or `Not(var)`) directly
to `semantics.frame_constraints` (`iterate.py:266`, `:280`) — bypassing the shared engine's
`all_constraints` path, which `models/structure.py`'s `_setup_solver` never reads. This path
emits no (C1)-(C4) content of its own; it pins previously-derived values so a rebuilt structure
reflects the model the search actually found, rather than an unconstrained re-solve.

**Assembly into what Z3 actually sees.** The seven single-solve call sites above collapse into
exactly four solver-visible tracked groups, each `assert_tracked` individually for unsat-core
extraction: `(model_constraints.frame_constraints, "frame")` — call sites (1)–(4); `(model_constraints.model_constraints,
"model")` — call site (7); `(model_constraints.premise_constraints, "premises")` — call site (5);
`(model_constraints.conclusion_constraints, "conclusions")` — call site (6). Call site (8) also
lands in the `frame` group when it runs, but outside this single-solve assembly: it appends
directly to `semantics.frame_constraints` from a later, iteration-only pass, after this assembly
has already completed once on that instance.
`ModelConstraints.__init__` reads `self.semantics.frame_constraints` **by reference** at
construction time (`self.frame_constraints = self.semantics.frame_constraints`), while
`finalize_certificate` — called later, from `BimodalStructure`'s `_setup_solver` override — still
mutates the *same* list object in place (`self.frame_constraints.extend(...)`, never
`self.frame_constraints = ...`). This reference-mutation contract is what lets the two-phase
design work at all, and is itself true of this specific object graph by construction, not by
proof.

**Net correction.** The encoder's actual attack surface is seven single-solve-reachable call
sites — four inside `finalize_certificate`, two invoked earlier and separately per formula, one
vacuous-but-live hook — plus one more (model-iteration pinning, call site (8)) reachable only when
iterating, all assembled through a reference-mutation contract and gated by an
externally-enforced call-order invariant. "No extra constraint" (`ADEQUACY.md` section 7.3) is a
claim about the conjunction of all eight when iterating, and the seven single-solve-reachable
sites otherwise, not about four self-contained functions.

## 5. The one-hot selector (D5)

`ADEQUACY.md` section 1 states (C4) as a bare existential: `∀γ∈Γ. γ∈L₀(t₀) ∧ ∀σ∈Δ. σ∉L₀(t₀)` for
*some* `t₀ ∈ ℤ`. Decision D5 implements it with a one-hot selector: fresh Boolean variables
`sel(t)` (`semantic/witness_constraints.py`, memoized per position), an exactly-one cardinality
constraint, and guarded implications (section 4, call sites (4)–(6)). Nothing resembling `sel`
appears in (C1)–(C4)'s statement, in the window-collapse theorems, or in the `Decidable` instances
the Lean side decides — it is pure encoding machinery, structure genuinely absent from the four
conditions' own proofs, and it needs its own argument.

**Claim (selector conservativity).** Adding the `sel` machinery to an encoding of (C1)–(C3)
changes neither its satisfiability nor the set of certificates a satisfying assignment can
witness, relative to (C4)'s bare existential.

**Argument, in three steps.**

1. **The reduction from `∃t₀∈ℤ` to `∃ slot` is an identity, not a step that can fail.**
   `WitnessRegistry.bit(lasso, t, f)` returns the *same* Z3 variable for every `t` sharing a slot
   under `wrap` — by definition, not by an argument that needs checking per formula. So "premises
   hold and conclusions fail at `t₀`" is already, for any fixed `t₀`, identical to the same
   statement about `t₀`'s representative slot, and `target_window()` enumerates each slot exactly
   once.
2. **The guarded implications are vacuous when `sel(t)` is false.** `Implies(sel(t), ...)` places
   no constraint on `bit(0, t, ·)` unless `sel(t)` is true. Adding these clauses is a
   Skolemization of the existential — a standard, sound-and-complete "witness variable" encoding
   of `∃x. P(x)` as `∃ fresh s. (s → P(w)) ∧ s`, which changes satisfiability only if the Skolem
   variable itself is over-constrained (step 3).
3. **`Or(*sels)` exactly restates the existential; `AtMost(*sels, 1)` costs nothing extra.** If
   some family satisfying (C1)–(C3) makes (C4) true at one or more slots, choosing `sel(t*) :=
   true` for exactly one such slot and `false` elsewhere satisfies the exactly-one constraint and
   every guarded implication — the false slots' implications are vacuous, and only the slots where
   `sel` is false raise no requirement. Conversely, any assignment with some `sel(t*)` true forces,
   via the implications, that premises hold and conclusions fail at `t*`'s slot, recovering (C4)
   directly. Neither direction is lost.

**Status.** This argument is correct and self-contained. As of this writing it is also recorded,
concurrently and independently, in `ADEQUACY.md` section 7.3, and it is now pinned by a property
test — `TestSelectorConservativity` (`tests/unit/test_witness_constraints.py`) — which isolates
`target_constraints` alone (no (C1)–(C3)) and checks, for a swept range of hand-built families,
that its aggregate and per-position satisfiability with some `sel[t]` true agree exactly with
`certificate._target_holds`'s independent decision of (C4), never re-deriving the expected verdict
inline. This raises the argument from *informal and unverified* to `TRUST_PIPELINE.md`'s
*property-tested* — checked on generated inputs, evidence bounded by what was generated — but,
per section 2, a passing property test is still not the same thing as **machine-checked**: it is
not a Lean theorem, and it does not verify the Python for every input, only for the family the
test happens to build. Concrete violations this argument, and the test that now pins it, would
still not see if introduced *outside* what the test constructs: an off-by-one in
`target_window()`'s bounds that shifted every generated family identically, a swapped `Implies`
polarity between premise and conclusion paired with a matching sign error in the test's own
expectation, or a defect confined to code paths the test's parametrization does not exercise. This
is section 2's category point recurring one level down, now in a sharper form: even a passing
property test about constraint *behavior* is evidence about the cases it tried, not a proof that
covers every case, and it remains one level short of what section 2 means by machine-checked.

## 6. The one remaining independently-defined window

This section records a gap that existed at earlier points in this codebase's history and has
since been closed by sharing rather than left open — the closure itself illustrates section 10's
routes (d)/(e), not section 2's routes (a)–(c), and is recorded here for that reason.

**The gap, as it stood.** `WitnessRegistry.target_window()` and `certificate._box_window` computed
the numerically identical range `[-nb, nm+nf)` from two separately written one-line formulas in
two different modules, with no shared call between them — the one place left where encoder and
re-checker could silently diverge on a window, by construction rather than by oversight.
`certificate.py`'s own comment recorded the split as deliberate: `target_window` was reused by the
selector (section 5), which had no natural place in `certificate.py`'s re-checker vocabulary,
while `_box_window` existed specifically to match `mem_all_iff_window`'s bound.

**Why this was worth naming precisely, rather than folding into "the encoder is unverified" in
general.** The two definitions agreed and were simple enough that they were unlikely to *silently*
drift by accident — and yet this was exactly the shape of the historical defect the next section
documents: a wide/narrow window distinction duplicated by hand instead of shared. Had a future
Lean-side revision moved `mem_all_iff_window`'s bound, `_box_window` would have needed updating,
with nothing forcing a corresponding update to `target_window()` — reintroducing, this time at the
selector rather than at local coherence, precisely the class of defect section 7 describes.

**Current state.** `WitnessRegistry.target_window()` now delegates directly to
`certificate._box_window` rather than recomputing the same range independently.
`certificate.py`'s own comment records the technical justification: the selector's own
conservativity argument (section 5) requires exactly the same one-representative-position-per-slot
window that box faithfulness's proof already establishes, so sharing the definition is the
technically correct outcome, not merely a tidying. All four window/bound functions the encoder
needs are consequently shared by import; none is independently defined any longer.

**What this closure is, and is not.** It removes the specific latent-drift risk this section
named, and a regression test pinning the two windows' numerical agreement across a swept range of
segment lengths was added alongside it, so the closure is checked, not merely asserted in prose.
It is not, and does not purport to be, an instance of section 2's routes (a)–(c): the delegation
is one more Python assignment, exactly as trustworthy — and exactly as unverified in the sense
section 2 means — as everything else this document surveys, and the regression test is
property-tested evidence in `TRUST_PIPELINE.md`'s sense, not a proof. Sharing a definition is
strictly weaker than proving the shared value correct; it only removes the possibility of *two*
definitions disagreeing, which is section 3(ii)'s point, not a new proof-preserving link. What
remains open from the original two-part gap this section and section 5 together named is the
selector-conservativity argument's own executable check (section 5's status paragraph, section
10's remaining route), not the window.

## 7. The historical defect, and why the standing test cannot see it

`semantic/witness_constraints.py`'s module docstring records, as a fact about this repository's
own history rather than a hypothetical, a defect of exactly the class this document is about.

**The defect.** An earlier version of `local_coherence_constraints` asserted the (C1) biconditional
only over `registry.target_window()` — the narrow window, one representative position per slot —
reasoning that `bit`'s slot-sharing made a single representative clause automatically cover every
position sharing that slot.

**Why the reasoning was false.** For the two slots adjacent to `mid` (the last `back` slot and the
first `fwd` slot), a position `t` sharing a slot does not imply its neighbour `t+1` (or `t-1`)
shares a *fixed* slot across every occurrence. At `nb=2`, slot `back[1]` recurs at every
odd-magnitude negative position (`t = -1, -3, -5, ...`) — all sharing the identical `bit` term, by
`wrap`'s definition. But the neighbour an `Untl`/`Snce` clause at `t` needs is `bit(lasso, t+1,
·)` (or `t-1`), and `t+1`'s *slot* is not the same for every occurrence of `t`: at `t=-1`, `t+1=0`
lands in `mid`; at `t=-3, -5, ...`, `t+1` lands back in `back[0]` — a different slot, in general
holding a different truth value. A single clause written at the `t=-1` representative therefore
left the `t=-3` (and deeper) requirement completely unconstrained.

**Minimum reproducing case.** The counterexample requires `nb=2` — it does not exist, by
construction, at `nb=1`.

**How it was caught.** Not by any proof, and not, per the docstring, by a dedicated unit test at
the time — by the pure-Python re-checker's *wide*-window scan (`certificate.py`'s
`_coherence_window`, matching the Lean-proved `coherent_iff_window` bound) disagreeing with the
encoder's narrow-window construction — exactly `ADEQUACY.md` section 6.2's fail-fast differential,
the mechanism standing between an encoder bug and a false report. The fixture
`04_window_discriminator_coherence.json`, named "window discriminator" and shaped as `ADEQUACY.md`
section 5.3's differential corpus item 2 ("a family failing (C1) or (C2) only at a position
outside `[-nb, nm+nf)` but inside `[-2nb, nm+2nf)`"), is this codebase's permanent regression
fixture for the *re-checker's* side of that distinction — it targets the general window-collapse
property, and is not shaped to reproduce the historical encoder defect's exact `nb=2` construction.

**The fix.** `local_coherence_constraints` now asserts the biconditional at *every* position in the
wide window (`_coherence_window`), matching what fulfilment already did from the start and matching
the Lean-proved bound exactly.

**Why a fixed-`nb=1` exhaustive tier cannot see this defect class — and the current state of the
grid.** The historical defect provably requires `nb=2` to exhibit — the module docstring's own
construction. A Tier 1 exhaustive at `back = mid = fwd = 1` alone, run today, would pass whether
or not this exact defect, or its analogue in a different emitter, were reintroduced — not because
the test is weak in general, but because that regime is, by the same argument that explains the
original bug, structurally blind to the one class of defect known to have actually occurred. This
is a **provable** gap, derivable directly from the docstring's own counterexample construction,
not a suspected weakness.

As of this writing, `tests/integration/test_certificate_a2_triangle.py`'s Tier 1 no longer runs
`back = mid = fwd = 1` alone: it additionally covers `back = 2, mid = 1, fwd = 2` (production's
`DEFAULT_EXAMPLE_SETTINGS`) — the `nb = 2` regime the defect actually required — for both
box-free closures and for one size-2 boxed closure, closing the specific blind spot named above
for those closures. One residual gap remains, named honestly rather than silently dropped: a
pre-existing size-3 boxed closure stays `back = mid = fwd = 1`-only, because its `nb = nf = 2`
enumeration is on the order of 10.7 billion candidates — infeasible under the suite's per-test
time budget, a standing coverage gap rather than a defect. Widening that closure's grid, or any
future closure added to the suite, remains one of the concrete, bounded routes named in section
10 — the grid can always be widened further; the point of section 7's argument is that no fixed
grid, however wide, is a proof, only ever wider evidence (section 8).

## 8. What a bounded exhaustive test does and does not establish

Within its own region, the A2-triangle test (`ADEQUACY.md` section 7.3) is a **decision**, not a
sample: at each of its grid points — `back = mid = fwd = 1`, and, for most of its closures,
`back = 2, mid = 1, fwd = 2` — and `|C| ≤ 4`, it enumerates *every* candidate at that tuple, so
agreement of legs (i) and (iii) across all of them is a complete case analysis over that finite
space, not a statistical inference from it. This is stronger than an arbitrary property test and
should be stated as such.

Two limits are equally exact, not matters of degree.

1. **Nothing about the result transfers to a larger closure or wider window without re-running the
   enumeration there.** Exhaustiveness is a property of the specific `(back, mid, fwd, |C|)` tuple
   tested; section 7 shows concretely that a real defect can be invisible at one tuple and present
   at another with no continuous "coverage" connecting them — exactly why the grid now has two
   sizes rather than one, and exactly why the size-3 boxed closure's remaining `back = mid = fwd =
   1`-only coverage (section 7) is a real, named gap rather than a formality. There is no
   monotonicity argument available — a defect need not become more likely to be caught as the grid
   widens in every dimension; it can be undetectable below a threshold and detectable at or above
   it, as the historical `nb=2` defect demonstrates, and widening the grid at one closure says
   nothing about a closure not yet widened.
2. **Passing the test never certifies A2 as a theorem, even for the tested region, in the sense
   section 2 requires.** "Every candidate at this closure and these lengths was checked and agreed"
   is an empirical fact about one test run against one version of the encoder, the re-checker, and
   (for Tier 2) `lake exe check_certificate` on this machine. A future refactor of any of the three
   could silently break the property the test currently observes; the test would then fail on its
   next run, which is exactly its intended purpose, but a passing run today says nothing about code
   not yet written.

Put together: the A2-triangle test is the best evidence this repository has for encoding
completeness at small closures, and it is complete evidence *there*. It is `TRUST_PIPELINE.md`'s
"Property-tested: checked on generated or enumerated inputs... Evidence, bounded by what was
enumerated" category, applied honestly to its strongest instance in this codebase. It is not, and
cannot by its nature become, a substitute for section 2's missing proof-preserving link between
the Lean theorems and the running Python.

## 9. The trust-base consequence of S3

`ADEQUACY.md` section 2 states S3 as: whatever the search reports satisfies (C1)–(C4), discharged
by *deciding* the antecedent on every reported certificate, twice and independently
(`ADEQUACY.md` section 6.2). This is possible exactly because (C1)–(C4) are decidable — the four
conditions collapse to finite windows (section 5 of `ADEQUACY.md`) — and it is the design's
load-bearing property, not a convenience: nothing in this repository has to prove the Z3 encoder
correct, because every individual output is checked, not trusted.

**Tracing the consequence through the two failure branches, exhaustively.**

- **The encoder under-constrains, or constrains wrongly.** Z3 returns something that fails to
  decode into a valid certificate, or decodes into one failing (C1)–(C4). The pure-Python
  re-checker's fail-fast step (`ADEQUACY.md` section 6.2, step 3) rejects, raising rather than
  reporting — a loud failure, never a false positive.
- **The encoder over-constrains.** Z3 returns UNSAT where a countermodel exists. The tool reports
  "no certificate found within these bounds" — which `ADEQUACY.md` section 7.4's
  never-report-validity rule already establishes was never a validity claim. This cost lands
  entirely on **completeness** (A2), never on soundness.

**There is no third branch.** An encoder defect cannot produce a Z3-satisfying model that also
passes the independent re-check without genuinely denoting a certificate satisfying (C1)–(C4),
because passing the re-check *is* what "satisfying (C1)–(C4)" means, decided directly, rather than
inferred from the encoder's intent.

**Corollary: the trust base.** The Z3 encoder, the decoder, and Z3 itself are consequently **not
in the soundness trust base at all**. Collecting `ADEQUACY.md`'s obligation table (section 2) and
trust-base discussion, the soundness trust base is exactly: Lean's kernel (for S1); the S2
transcription audit; the re-checker implementation (mitigated, not eliminated, by the dual
Python/Lean check); and the translation (S4).

**Ranking corollary: S4, not A2, is the weakest joint** in the direction already asserted. A2's
failure mode is bounded and self-announcing — a completeness cost, or a loud rejection. S4's is
not: `ADEQUACY.md` section 6.3 records that a translation defect is invisible to the Python/Lean
round-trip by construction, because both sides consume the same already-translated `Formula`,
regardless of how thoroughly either half of the translation is separately tested. Both halves are
now property-tested directly (`tests/unit/test_formula.py`'s two
`TestTranslateTruthPreservation*` classes), including the box half, which
`oracle/bimodal_logic/ground_truth.py`'s brute-force adjudicator still cannot adjudicate on its
own — it declares only the five temporal primitive tags (`atom`, `bot`, `imp`, `untl`, `snce`) as
supported, and raises `GroundTruthUnsupported` for `box` by name in its own docstring, which is
exactly why the box half is covered directly in `test_formula.py` instead of being inherited from
it. S4 remains the weakest joint in kind (a translation defect stays structurally invisible to the
round-trip, and no Lean theorem covers either half), even though it is no longer uncovered by any
test.

**The honesty point.** A "countermodel" verdict — from the Python re-checker, from `lake exe
check_certificate`, or from their agreement — says only that the four `Decidable` instances
returned `true` on the family rebuilt from the wire input. It is **not a kernel-checked proof for
that particular certificate** — `ADEQUACY.md` section 6.2 makes this comparison explicit against
the tableau bridge's own `"gates"` field. Only the soundness theorem (`WitnessFamily.joint_countermodel`)
is a proof, and it is a proof of the *implication* "(C1)–(C4) ⟹ a paper countermodel exists,"
applied to whatever the decision procedures certify holds of the specific rebuilt family. This is
why the A2 gap is a **completeness** matter, not a soundness one: nothing above weakens (SOUND);
it is entirely why (SOUND) needs no encoder-correctness proof in the first place.

## 10. What closing the gap would require, route by route

Given section 2's category argument, "closing the gap" cannot mean "prove the encoder correct"
without first creating one of the three link types section 2 names.

| Route | What it would require | What it would buy | Cost / status |
|---|---|---|---|
| **(a) Extraction** | Specify the constraint generators in Lean (or another proof assistant) as functions over `LabelledLasso`/closure data, prove they emit exactly (C1)–(C4)'s conjunction, extract to Python or another host the search can call | Removes the encoder from "unverified" entirely; the extracted code *is* the theorem, executably | Large: needs a verified extraction pipeline targeting whatever calls into `z3-solver`'s Python bindings, or a rewrite of the search to consume an extracted term set directly. Not started; no infrastructure exists for it here. |
| **(b) Direct verification** | Formalize a semantics for the relevant Python subset and the Z3 API surface used, then prove `witness_constraints.py`/`core.py`'s actual source — not a model of it — meets the (C1)–(C4) specification | Same end state as (a) without requiring a rewrite | Arguably larger: verifying real Python against a real library's semantics is a substantial, novel undertaking with no existing tooling referenced anywhere in this codebase. |
| **(c) Reflection** | Encode the constraint-generation algorithm inside Lean's own kernel and have the kernel evaluate it, so the kernel's evaluation of the algorithm on a given input *is* the check | Strongest option that reuses existing Lean infrastructure | Would still require re-implementing the generators in Lean and does not, by itself, verify that the actual deployed Python matches that Lean re-implementation — reintroducing a translation obligation of its own, a second S4-shaped gap. |
| **(d) Widen the differential grid** | Extend the A2-triangle test to the `nb = 2` regime the one known defect lived in, for every closure in the suite | Directly closes the specific blind spot section 7 identifies; highest empirical value per hour of the bounded routes | As of this writing, done for the box-free closures and one size-2 boxed closure; the pre-existing size-3 boxed closure remains infeasible at `nb = nf = 2` (~10.7 billion candidates) under the suite's time budget — a named residual, not a defect. Remains evidence, not proof, per section 8, wherever it is done. |
| **(e) Selector conservativity, made executable** | Turn section 5's argument into an executable check: a property test asserting satisfiability with some `sel[t]` true iff the re-checker's own target decision holds, checked against that decision directly rather than a hand-derived expectation | Removes the selector argument from "informal and unverified" to "checked" | As of this writing, done: `TestSelectorConservativity` (section 5) pins exactly this, and the window-sharing half of this route (section 6) is closed as well. Still evidence-shaped, per section 2 — a passing property test that the selector behaves as argued is not a proof that it always will, for inputs the test does not generate. |
| **(f) Consume a proof-producing checker** | Make Lean's accepting branch construct `joint_countermodel` directly from a decided hypothesis, and compare a Lean-side echo of the parsed wire against the bytes sent | Removes the **re-checker** — not the encoder — from the trust base | Named in `TRUST_PIPELINE.md`'s "What remains" as Lean-side future work; does not by itself touch the encoder side this document is about. |

**Honest ranking.** Routes (a)–(c) are the only ones that would satisfy section 2's category
argument on its own terms — they alone create the missing proof-preserving link. All three are
substantial and unstarted. Routes (d) and (e) are concrete and valuable, but per section 8 they
strengthen the *evidence* for A2 within a larger or better-understood region; they do not and
cannot become a proof however far the grid is widened or the property test extended, because a
finite enumeration is definitionally bounded by what it enumerates and a property test by what it
generates — and this remains true even where both routes are now, as of this writing, mostly or
fully complete: (d)'s grid-widening for the box-free and size-2 boxed closures (section 7, with
the size-3 boxed closure named as the residual), and (e) in full — both the window-sharing and the
selector-conservativity test (sections 5, 6). Each closed a real, named gap, and none created a
proof-preserving link of the kind (a)–(c) name. Route (f) addresses a different trust-base member
— the re-checker, S3's own second leg — rather than the encoder this document is scoped to.

## 11. See also

- `ADEQUACY.md` — sections 5.2 and 5.3 (the proved re-check windows and the periodicity
  obligation this document's category argument transfers to the encoder), and section 7.3 (the A2
  statement and its deciding test).
- `TRUST_PIPELINE.md` — Stage 2 (the encoder's evidence-free-by-design status), and "The trust
  base" (what is and is not in it, and why the translation, not the encoder, is the weakest
  joint).
- `ARCHITECTURE.md` — the code: module layout, the two-phase constraint emission, and the
  independent re-check.
- `semantic/witness_constraints.py` — the constraint generators this document enumerates, and the
  module docstring recording the historical defect.
- `semantic/certificate.py` — the shared window and bound definitions, and the pure-Python
  re-checker.
- `semantic/core.py` — `finalize_certificate`, the call-order invariant, and decisions D5/D6.
- `semantic/witness_registry.py` — `wrap`, `bit`, and `target_window`.
