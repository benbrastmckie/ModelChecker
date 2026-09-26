# The Trust Pipeline: From a Typed Formula to a Paper Countermodel

## What this document is

`ADEQUACY.md` states and proves the mathematics. `ARCHITECTURE.md` describes the code. This
document is the connective tissue between them: it walks the pipeline **stage by stage**, and for
every stage names the component, the guarantee, and — crucially — **what kind of evidence** backs
that guarantee. It then states what is in the trust base, what is deliberately outside it, and
what work remains, here and in the Lean development.

It is a map, not a proof. Every mathematical claim below is stated and discharged in
`ADEQUACY.md`; this document cites rather than re-proves.

**Four kinds of evidence** are used throughout, and keeping them distinct is the point of the
document:

| Kind | Meaning | Strength |
|------|---------|----------|
| **Theorem** | Machine-checked in Lean, sorry-free | Strongest |
| **Decided per run** | Computed on the actual object, every time, by a decision procedure derived from theorems | Strong, and does not require trusting the producer |
| **Audit** | Established by human inspection | Irreducible where it spans the paper/formalism boundary |
| **Property-tested** | Checked on generated or enumerated inputs | Evidence, bounded by what was enumerated |

A claim's strength is the *weakest* link in its chain. That is why the sections below are ordered
by pipeline position rather than by importance: a reader needs to see where the weak links sit.

---

## The pipeline

```
   user's argument (Sentence objects)
     │
     │  (1) TRANSLATION            ← property-tested, and only partly
     ▼
   Formula (six primitives)
     │
     │  (2) ENCODING               ← not in the soundness trust base at all
     ▼
   Z3 constraint set ──── UNSAT ──▶ "no certificate within these bounds"
     │                              (never a validity claim)
    SAT
     │
     │  (3) DECODING               ← not in the soundness trust base
     ▼
   certificate (bx, lassos, target)
     │
     │  (4) RE-CHECK in Python     ← decided per run
     │  (5) RE-CHECK in Lean       ← decided per run, from theorems
     ▼
   conditions (C1)-(C4) hold
     │
     │  (6) S1: the agreement theorem   ← THEOREM
     ▼
   a paper countermodel exists ⟹ the inference is refuted
```

### Stage 1 — Translation (`Sentence` → `Formula`)

**Component.** The theory's own translation layer, invoked via `premise_behavior` /
`conclusion_behavior`.

**What it must do.** Eliminate every defined operator (`\neg`, `\wedge`, `\vee`, the derived tense
operators, `\next`, `\prev`) into the six primitives, and swap `Until`/`Since` arguments —
`UntilOperator.true_at` is event-first while Lean's `untl` is guard-first. The wire's named
`event`/`guard` fields make the wire itself order-free, so the swap hazard is **purely internal to
the translation code** and invisible downstream.

**Evidence: property-tested, and incompletely.** This is obligation **S4**, and `ADEQUACY.md`
§6.3 records that no Lean theorem covers it. Worse, a round-trip between the Python re-checker and
the Lean binary *cannot* detect a translation defect, because both consume the same
already-translated `Formula`. `oracle/bimodal_logic/ground_truth.py`'s brute-force adjudicator
covers only the **tense half** (five primitive tags, no box case).

**Why this is the most consequential weak link.** Condition (C4) is decided against
`target.premises` / `target.conclusions`. If the translation is wrong, every later stage
rigorously certifies a countermodel **to a different argument than the user asked about**. No
amount of rigor downstream repairs this, and it is the one stage whose failure is silent in both
directions.

### Stage 2 — Encoding (`Formula` → Z3 constraints)

**Component.** `semantic/witness_constraints.py`, with the assembled set reaching the solver via
`finalize_certificate()`'s in-place writes to `frame_constraints` (which `ModelConstraints` reads
*by reference*), plus `proposition_constraints`.

**Evidence: none required for soundness — by design.** This is the architectural payoff of the
whole certificate approach, and it is worth stating precisely:

> Because (C1)–(C4) are decidable, nothing in this repository has to prove the encoder correct.

Enumerate how an encoder defect can manifest and the asymmetry is total:

- **Under-constrains, or constrains wrongly** → Z3 returns something that fails to decode into a
  valid certificate → stage 4 or 5 rejects → a loud failure, never a false report.
- **Over-constrains** → Z3 returns UNSAT when a countermodel exists → the tool reports "no
  certificate within these bounds", which was never a validity claim.

So encoder defects cost **completeness** or raise an **error**. They cannot manufacture a false
"here is a countermodel". This is why encoding completeness (**A2**) belongs to the (ADEQ)
direction and never to (SOUND).

**What is nonetheless known about the encoder.** Three of the four window bounds are *shared by
import* — `witness_constraints.py` takes `_coherence_window`, `_box_window`,
`_scan_forward_bound` and `_scan_backward_bound` directly from `certificate.py`, so the encoder
and re-checker cannot drift on them. That is structurally stronger than a proof of agreement,
because there is no second definition to diverge. Two gaps remain: `WitnessRegistry.target_window()`
is independently defined (deliberately — it also serves the one-hot selector), and the one-hot
`sel` selector is structure absent from (C1)–(C4) entirely, so "exactly (C1)–(C4)" does not cover
it and it needs its own conservativity argument.

**A defect of exactly this class has occurred.** `witness_constraints.py`'s module docstring
records that local coherence was once generated over the narrow `target_window()` instead of the
proved wide `_coherence_window`. The counterexample requires `nb = 2`. It was caught by the §6.2
fail-fast re-check — *not* by any proof, and not by a test.

### Stage 3 — Decoding (Z3 model → certificate)

**Component.** `ModelBuilder` / the certificate extraction path.

**Evidence: none required — also by design.** A decoding defect can only produce an object that
fails the four conditions, which stage 4 rejects. It cannot produce a false acceptance, because
**the certificate's provenance is irrelevant to soundness**: once an object satisfies (C1)–(C4),
S1 applies to it, whether it came from Z3, a fuzzer, or a hand-written JSON file.

### Stage 4 — Re-check in Python

**Component.** `semantic/certificate.py`'s `recheck`, over §5.2's proved windows.

**Evidence: decided per run.** Not assumed, not proved-once-about-the-producer — *computed on the
actual object*, every time. The re-check reads the decoded certificate and does **not** consult
Z3's model object, so a wrong model cannot smuggle its wrongness through by being asked twice.

**The fail-fast step.** Any verdict but `countermodel` raises rather than reports. This is the
mechanism that converts "possible encoder bug" into "loud rejection".

### Stage 5 — Re-check in Lean

**Component.** `lake exe check_certificate`, built on the four `Decidable` instances, over the
wire contract documented in `ADEQUACY.md` §6.1.

**Evidence: decided per run, from theorems.** The `Decidable` instances are built from the window
collapses (`coherent_iff_window`, `fulfil_iff_window`, `mem_all_iff_window`, plus `scan_forward` /
`scan_backward`), and the module opens no `Classical` — the conditions are decided
*computationally*, not merely classically true or false.

**Why two re-checks, and why the asymmetry matters.** Stage 4 defends against the encoder; stage 5
defends against stage 4. The direction of blame is fixed **in advance**: the Lean predicates are
the contract, so disagreement is by definition a Python-side defect. That is what makes a
disagreement actionable rather than a stalemate between equals.

**What stage 5 does *not* give.** A `countermodel` verdict says the four `Decidable` instances
returned `true` on the family rebuilt from the wire input. It is **not a kernel-checked proof for
that particular certificate**. `ADEQUACY.md` §6.2 says so explicitly, and compares the honesty to
the tableau bridge's own `"gates"` field.

**Wire discipline worth knowing.** `target.time` is required with **no default**, because it is
(C4)'s existential witness and every other existential in a certificate is explicitly witnessed —
a defaulted `t` would leave the outermost existential the only unwitnessed one. Atom identity is
base-only, so a certificate carrying a fresh or Skolem atom is rejected outright. Output is one
line, never a validity claim, with `error` (failed the *protocol*) kept distinct from `rejected`
(parsed, but failed a *condition*).

### Stage 6 — The agreement theorem

**Component.** `WitnessFamily.joint_countermodel`
(`Metalogic/Decidability/WitnessFamily/Agreement.lean:232`).

**Evidence: theorem.** Machine-checked, sorry-free. Given (C1)–(C4), a paper countermodel exists
— a model with a nontrivial totally ordered abelian group of times and a task relation satisfying
Compositionality, Seriality, Limit and Saturation, together with a history and a time witnessing
the premises true and the conclusions false.

This is obligation **S1**, and it is the leg that makes everything else worth doing.

---

## The trust base

Collecting the above, the trust base for a reported countermodel is:

**In it:**
- Lean's kernel (for S1).
- The **transcription audit** (S2): that the Lean definitions transcribe the paper's. An audit,
  not a theorem — see below.
- The **re-checker implementation**, mitigated but not eliminated by the dual check.
- The **translation** (S4).

**Deliberately outside it:**
- **Z3.** Its verdicts are never taken as authority for a positive report.
- **The encoder.** Stage 2.
- **The decoder.** Stage 3.

That list is the single most useful thing to know about this design. It is also why the weakest
link is the *translation*, not the encoder — a fact that runs against intuition, since the encoder
is where the intricate window arithmetic lives.

---

## The other direction, and why it is not symmetric

Everything above concerns **(SOUND)**: a reported certificate entails a paper countermodel. The
converse, **(ADEQ)** — if a countermodel exists, the search finds it — decomposes into three
components and one permanent limit:

| | Claim | Status |
|---|---|---|
| **A0** | ℤ-time completeness does not imply completeness at every temporal order | **Permanent limit** |
| **A1** | Compression: a ℤ-time countermodel yields a certificate with lengths bounded by `f(|C|)` | **Open** — route named, owned by the Lean development |
| **A2** | Encoding completeness: a certificate within the lengths implies Z3 reports SAT | Provable and testable; partly tested |
| **A3** | Bound realization: configured lengths ≥ `f(|C|)` | **Vacuous** until A1 supplies `f` |

**The asymmetry is structural.** Stage 6 certifies a *positive* claim with a witness. (ADEQ) needs
to certify **absence**, and absence has no witness. Hence "no certificate found within these
bounds" is the strongest honest output, and the never-report-validity rule (`ADEQUACY.md` §7.4,
and `ARCHITECTURE.md`'s D8) exists to keep it that way.

**A0 is not a gap to be closed.** The search is, by design and permanently, silent on a nonempty
class of paper-invalid inferences. Even a fully discharged A1, A2 and A3 caps the strongest honest
claim at "ℤ-time valid".

### The standing test for A2

`tests/integration/test_certificate_a2_triangle.py` compares three verdicts — the Python
re-checker, the Lean binary, and whether the real Z3 encoding reports SAT — over an **exhaustive**
enumeration of every candidate at `back = mid = fwd = 1`, across three closures (two box-free, one
boxed, one of them UNSAT so the comparison is exercised in both directions).

Its value is **localization**: two legs agreeing tells you the checking is right; only the third
connects that to the search. Each disagreement pattern points at one component — checkers
disagreeing means a re-checker defect; both checkers accepting where Z3 says UNSAT means encoding
incompleteness; both rejecting where Z3 says SAT means encoding unsoundness.

Within its region this is a **decision**, not a sample. Outside it, nothing — and note that the one
A2 defect known to have occurred needs `nb = 2` to exhibit, so the test as it stands is blind to
exactly the bug that once happened.

---

## What remains

### In this repository

| Work | Why it matters |
|------|----------------|
| **Discharge S4** — verify the translation, or relocate the elimination into verified code | The weakest link in the direction already asserted. The box half has no coverage at all. Relocating deletes the obligation rather than testing it. |
| **Widen the A2 grid to `nb = nf = 2`** | The regime the one known A2 violation lived in. Highest value per hour on the (ADEQ) side. Measure the candidate count first: the single-box closure already reaches 1,572,864 candidates at `nb = nf = 1`. |
| **Selector conservativity, and the last unshared window** | The one-hot `sel` selector is outside (C1)–(C4), so an incompleteness could be misattributed to the encoder when the selector is the real over-constraint. `target_window()` is the last place encoder and re-checker can silently diverge. |
| **Consume a proof-producing checker; verify the parse** | Turns a `countermodel` verdict into a constructed entailment, and removes the Python re-checker from the trust base. Compare an echo of what Lean parsed against the bytes sent. |
| **Compute bounds from the closure (A3)** | Once `f` exists, set lengths from `|C|` and report "exhaustive at this closure" versus "bounded" honestly. Blocked until the Lean side supplies `f`. |
| **The stability modal** | See below. Blocked on four Lean-side results. |

### In the Lean development (`~/Projects/BimodalLogic`)

| Work | Why it matters |
|------|----------------|
| **Compression (A1)** and the verified bounded enumerator | A1 is the only genuinely open *mathematics* in the (ADEQ) chain. The enumerator matters independently: because the candidate space at the bound is finite and enumeration completeness is already proved there, **absence can be decided by verified code rather than by trusting Z3's UNSAT** — which dominates proving this repository's encoder correct. |
| **Proof-producing `check_certificate`** | Make the accepting branch *be* `joint_countermodel` applied to a decided hypothesis, so acceptance is Lean constructing the existence term. |
| **Canonical wire, total parser, round-trip theorem** | A parser defect means the verified side certifies a different certificate than the one exported. |
| **Lean-side translation with a truth-preservation theorem** | The other half of S4. |
| **Narrow the transcription audit (S2)** | Derive the paper's frame conditions as theorems where derivable, so the surface needing human inspection shrinks to the primitives. Cannot become a theorem; can be made small and explicit. |

A note on sequencing: the compression work is independent of everything else and is the long pole,
so it can proceed in parallel from the start. The translation work protects a claim already being
made, so it comes first among the rest.

---

## The stability modal

The stability modal (`⊡`) is out of scope throughout `ADEQUACY.md`, and this repository has no
such operator. The reason it cannot simply be added is counter-intuitive, and
`ADEQUACY.md`'s "Why the design is deterministic" states it precisely:

**The obstruction is not Limit or Saturation.** Saturation is free from subsingleton fibres, and
Limit is discharged trivially over ℤ. Those look like the load-bearing constraints and are not.

**It is Lemma 2 and the Box case of Lemma 4.** Determinism is exactly what makes
`ShiftSet.total_eq_orbit` true — every world history *is* one of the lasso orbits. Let two lassos
share a state, and a history can cross between them at that state: `total_eq_orbit` fails,
Corollary 2.2 (the frame's history set is exactly the certified histories) fails with it, and the
Box case fails, because **(C3) is calibrated against "every position of every lasso"** and stops
enumerating the history set once histories recombine. This is the same obstruction that the
refuted finite-presentation small-model hypothesis records for finite digraphs.

So supporting `⊡` requires **re-proving Lemma 2 and redesigning (C3)** — not weakening the
Limit/Saturation argument. On the Lean side, `⊡` collapses to the identity on deterministic frames
(`states_eq_of_deterministic`), so the current device is blind to it *by construction* and cannot
be extended by adding a truth clause. A decision procedure would need witness families that branch
at a shared state plus an agreement lemma over all walks of the resulting digraph.

One fact helps: `⊡`-truth is a function of the present world state alone (`stab_state_only`), so
the modal needs no history information beyond the state. The entire difficulty is that `□` must
then range over recombined histories.

Decidability for the larger language at integer time is currently **paper-level only** — a
translation into monadic second-order logic over the ω-branching tree plus an appeal to Rabin's
theorem that is *recalled, not held* — and it yields no finite certificate, no complexity bound,
and no basis for a `Decidable` instance, with the finite model property explicitly not obtained.
Establishing that provenance is therefore the gate on the whole line, not a formality.

---

## The honest ceiling

Three residuals remain after all the work above, and they are **not** alike:

1. **A0, the frame-class gap — permanent.** No work removes it. "No certificate found" never
   becomes "valid".
2. **S2, the transcription audit — permanent in kind.** It spans the boundary between an informal
   paper and a formalism, and nothing inside the formalism can discharge it. It can be narrowed
   and made explicit; it cannot become a theorem.
3. **The stability modal — open, but routed.** Unlike the first two, this is excluded *pending
   identified work*, not in principle. The obstruction is named, the required results are named,
   and a gate exists on whether the target is even known decidable.

Conflating the third with the first two would tell a reader the stability modal is impossible when
it is merely unbuilt. Conflating the first two with the third would promise a completeness the
frame class cannot deliver.

---

## See also

- `ADEQUACY.md` — the statements, the proofs, the Lean citation table, the obligations and
  components by name.
- `ARCHITECTURE.md` — the code: module layout, two-phase constraint emission, the independent
  re-check, never-reporting-validity.
- `ITERATE.md` — model iteration, and the orbit-quotienting that makes successive models genuinely
  distinct rather than rotations of one another.
- `../README.md` — the higher-level summary of the certificate search.
