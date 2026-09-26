# Implementation Plan: Task #192

- **Task**: 192 - A2 proof-vs-implementation gap companion report
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: specs/192_a2_proof_vs_implementation_gap_report/reports/01_a2-proof-implementation-gap.md
- **Artifacts**: plans/01_a2-gap-companion-document.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md,
  .claude/rules/no-task-references-in-deliverables.md, .claude/rules/artifact-formats.md
- **Type**: markdown
- **Lean Intent**: false

## Overview

Write one new document, `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md`, giving the
**deep treatment** of the A2 proof-versus-implementation gap: the full category argument for why a
proof about mathematics cannot discharge a claim about what a specific piece of running Python
emits, the complete emitted-constraint surface with each emitter's clause shape written out, and
the per-route analysis of what closing the gap would actually require. The document builds on and
cites `TRUST_PIPELINE.md` (already in the same directory) rather than restating its summary-level
content, and is cross-referenced from `ADEQUACY.md` section 7.3, the `docs/README.md` index, and
`TRUST_PIPELINE.md`'s "See also". Definition of done: the document exists with all eleven planned
sections, every code citation resolves to a live symbol, the four cross-reference edits are in
place, and no task-number citation appears anywhere in the deliverable. Documentation only: no
source or test file is edited.

### Research Integration

The research report is the content draft, not merely input. Its sections A-I map one-to-one onto
this plan's document sections and the implementer should transcribe them (adjusting prose register
only), not re-derive them:

| Report section | Document section | Phase |
|---|---|---|
| A - the category argument (3 steps, CompCert comparison) | 2 | 1 |
| B - machine-checked / shared-by-import / not | 3 | 1 |
| C - seven emission call sites, clause shapes, assembly, invariants | 4 | 2 |
| D - one-hot `sel` conservativity argument and its own limits | 5 | 3 |
| E - `target_window()` vs `_box_window` | 6 | 3 |
| F - historical local-coherence defect, standing test's blindness | 7 | 4 |
| G - what a bounded exhaustive test does and does not establish | 8 | 4 |
| H - the S3 trust-base consequence (ADDENDUM) | 9 | 5 |
| I - per-route table (a)-(f) and honest ranking | 10 | 5 |

Report findings that materially shape the plan beyond transcription:

- The emitted surface is **seven** call sites, not four (four inside `finalize_certificate`, the
  per-premise and per-conclusion behaviours invoked earlier from `ModelConstraints.__init__`, and
  the vacuous-but-live `proposition_constraints` hook), collapsing into four solver-visible
  tracked groups. Two cross-cutting subtleties must be stated explicitly: the selector's
  constraints are split across two phases, and `finalize_certificate()`'s correctness rests on a
  call-order invariant enforced by its caller, not by `BimodalSemantics`.
- The selector-conservativity argument and the window-independence note are presented in this
  codebase's documentation **for the first time** and must be flagged as informal and unverified,
  with the selector argument used as the report's own recursive illustration of the category point.
- The historical defect's blindness to the standing `back=mid=fwd=1` test is **provable** from the
  module docstring's own `nb=2` counterexample construction, and should be stated as provable
  rather than as a suspected coverage gap.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch and no ROADMAP.md was consulted.

## Goals & Non-Goals

**Goals**:
- Create `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` with the eleven sections fixed
  in Phase 1's outline, at the depth the research report's sections A-I already reach.
- Give the category argument in full: what the Lean theorems are about, what "the encoder is
  correct" would have to mean, the three proof-preserving link types (extraction, direct
  verification, reflection), and why none exists here.
- Enumerate the complete emitted-constraint surface with **each emitter's clause shape**, the
  assembly into the four tracked solver groups, the reference-mutation contract, and the
  externally-enforced call-order invariant.
- Separate three statuses sharply and visibly: machine-checked in Lean, structurally shared by
  import (stronger than a proof of agreement, weaker than a proof about the code), and not checked
  at all.
- Name the one-hot `sel` selector (decision D5) as structure genuinely absent from (C1)-(C4),
  supply its conservativity argument, and state what that argument does not establish.
- Record `WitnessRegistry.target_window()` as the one remaining independently-defined window and
  why the split is deliberate.
- Present the historical local-coherence defect as concrete evidence, including the `nb=2`
  minimum reproducing case, that it was caught by the fail-fast differential rather than by any
  proof, and that the standing A2-triangle test is provably blind to it.
- State honestly what a bounded exhaustive test does and does not establish.
- State the S3 trust-base consequence and its corollaries: the Z3 encoder, the decoder and Z3
  itself are outside the soundness trust base; the soundness trust base is Lean's kernel, the S2
  transcription audit, the re-checker implementation and the translation (S4); S4, not A2, is the
  weakest joint; and a "countermodel" verdict is not a kernel-checked proof for that certificate.
- Give the per-route analysis of what closing the gap would require, route by route, with an
  honest ranking.
- Wire the document into `ADEQUACY.md` section 7.3, `docs/README.md` (both the Quick Navigation
  bullet list and the Documentation Overview section), and `TRUST_PIPELINE.md`'s "See also".

**Non-Goals**:
- No source or test changes. Not one line of `semantic/`, `models/`, or `tests/` is edited.
- No restatement of `TRUST_PIPELINE.md`'s summary-level content (the trust-base corollary, the
  named emitted surface, the selector, the independent window, the historical defect narrative).
  Each is cited as established there and then extended, never re-explained from scratch.
- No re-derivation of `ADEQUACY.md`'s theorems, lemmas, or Lean citation table.
- No new tests, fixtures, or executable checks. Turning the selector argument into an executable
  check and widening the exhaustive grid are separately scoped work, referenced by description
  only (see the task-number prohibition in Risks below).
- No edits under `.claude/**` (this repository's deployed tree is a disposable deploy artifact).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Document read as claiming the encoder *is* verified (misreading "shared by import" as "proved correct") | H | M | Section 3 uses a three-status table with distinct column vocabulary; every "shared by import" claim is followed in the same paragraph by what it does not establish. Phase 1 verification re-reads section 3 specifically for this |
| Restating `TRUST_PIPELINE.md` and defeating the SCOPE NOTE | M | M | Phase 6 verification diffs the new document's claims against `TRUST_PIPELINE.md` Stage 2 and "The trust base" sections; every overlapping claim must appear as a citation plus an extension, never as a fresh explanation |
| Task-number citations leaking into the deliverable (the research report cites projects 193/194 by number; the document sits outside `specs/**` where such citations are prohibited) | H | H | Every route and follow-on reference is phrased by durable description ("widening the exhaustive grid to `nb = nf = 2`", "turning the selector argument into an executable check"), never by number. Phases 5 and 6 both grep the file for task/project-number patterns as a blocking verification step |
| Line-number citations rotting (the research report cites `file:line` throughout; the sibling docs cite symbols) | M | H | Citations are converted to module-path plus symbol name, matching `TRUST_PIPELINE.md`'s register. Line numbers are used nowhere in the new document. Each phase's verification greps the cited symbol in the cited module |
| Sibling tasks (193, 194, 196) dispatched this same cycle on this shared tree; 196 concerns S4 and may touch `ADEQUACY.md` | M | M | Re-read `ADEQUACY.md`, `docs/README.md` and `TRUST_PIPELINE.md` immediately before each edit; stage only this task's own hunks by explicit file list; never `git add -A`, a directory pathspec, or `git commit -am`; on observing a foreign commit or modification in these files, stop and report |
| Selector-conservativity argument or window-independence note reading as more settled than it is | M | M | Both sections close with an explicit status paragraph (informal, unverified, recursively subject to the category argument), transcribed from the report's own hedges |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel. This plan is fully sequential: phases 2-5
each append distinct sections to the single file phase 1 creates, so they must not run
concurrently even though their content is independent.

### Phase 1: Create A2_GAP.md — scope, the category argument, and the three-status table [COMPLETED]

**Goal**: The document exists at its final path with the full section outline fixed, and its first
three sections written: what this document is, the category argument, and the sharp separation of
machine-checked / shared-by-import / unchecked.

**Tasks**:
- [x] Re-read `TRUST_PIPELINE.md`'s "What this document is", Stage 2, and "The trust base"
      sections, plus `ADEQUACY.md` sections 5.2, 5.3 and 7.3, so the new document's opener can
      cite them precisely rather than paraphrase.
- [x] Create `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` with an H1 title and the
      eleven-section outline (as H2s) this plan fixes: (1) What this document is; (2) The category
      argument; (3) What is machine-checked, what is shared by import, what is neither; (4) The
      emitted-constraint surface, emitter by emitter; (5) The one-hot selector (D5); (6) The one
      remaining independently-defined window; (7) The historical defect, and why the standing test
      cannot see it; (8) What a bounded exhaustive test does and does not establish; (9) The
      trust-base consequence of S3; (10) What closing the gap would require, route by route;
      (11) See also.
- [x] Write section 1: this document extends `ADEQUACY.md` sections 5.2, 5.3 and 7.3 and assumes
      `TRUST_PIPELINE.md`'s Stage 2 and trust-base discussion; it does not restate either. State
      the thesis in one sentence: what is missing for A2 is not mathematics but a proof that the
      running Python emits what the mathematics specifies.
- [x] Write section 2, the category argument, in the report's three steps: what the Lean theorems
      are statements about (mathematical functions, `Decidable` instances, quantified over every
      `t : ℤ`); what "the encoder is correct" would have to mean (a proof-preserving link:
      extraction, direct verification against a formal semantics of the host language and the Z3
      API, or reflection inside the same kernel); why sorry-freeness therefore says nothing about
      the encoder (a derivation's soundness versus an interpreter's plus a compiled library's
      behaviour), with the CompCert comparison as the standard of what closing such a gap looks
      like. Quote `ADEQUACY.md` section 5.3's own sentence about the re-checker as the template
      being transferred to the encoder.
- [x] Write section 3 as a three-status presentation: (i) machine-checked in Lean, sorry-free —
      `coherent_iff_window`, `fulfil_iff_window`, `mem_all_iff_window`, `scan_forward`,
      `scan_backward`, and the four `Decidable` instances built from them; (ii) structurally
      shared by import — `witness_constraints.py` takes `_coherence_window`, `_box_window`,
      `_scan_forward_bound` and `_scan_backward_bound` directly from `certificate.py`, so encoder
      and re-checker cannot drift on those four bounds, which is stronger than a proof of
      agreement between two independent definitions because there is no second definition; (iii)
      neither — the clause shapes built from those windows, `finalize_certificate`'s assembly
      order and in-place mutation, the selector, and the independently-defined target window.
- [x] Ensure every code reference in these sections is module-path-plus-symbol, with no line
      numbers, matching `TRUST_PIPELINE.md`'s citation register.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: prose

**Verification**:
- `A2_GAP.md` exists, is non-empty, and contains exactly the eleven planned H2 headings
  (`grep -c '^## ' `).
- Every Lean identifier named in section 3 appears in `ADEQUACY.md` section 5.2's table
  (`grep -n 'coherent_iff_window\|fulfil_iff_window\|mem_all_iff_window\|scan_forward\|scan_backward' ADEQUACY.md`).
- The four shared bound names resolve in the live import:
  `grep -n 'from .certificate import' code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`
  names all four.
- No `file:line` citation form appears in the new file (`grep -nE '\.py:[0-9]+' A2_GAP.md` is
  empty).
- No task/project-number citation appears (`grep -nEi '\b(task|project) [0-9]+' A2_GAP.md` is
  empty).
- Diff read-through confirming every changed hunk is markdown prose in the new file only; `git
  status --short` shows exactly one new untracked file and no modified source file.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - created; sections 1-3 written, the
  remaining eight section headings present as stubs.

---

### Phase 2: Section 4 — the complete emitted-constraint surface, emitter by emitter [COMPLETED]

**Goal**: Section 4 enumerates every emission call site with its clause shape, the assembly into
the four tracked solver groups, the reference-mutation contract, and the call-order invariant —
the depth the SCOPE NOTE asks for beyond `TRUST_PIPELINE.md`'s naming of the surface.

**Tasks**:
- [x] Open with the correction: "the four condition emitters" undercounts; the surface "no extra
      constraint" quantifies over is seven call sites collapsing into four solver-visible groups.
- [x] Write the (C1) local-coherence emitter with its per-formula clause table (`Atom` —
      deliberately unconstrained; `Bot`; `Imp`; `Box`; `Untl` at `t+1`; `Snce` at `t-1`), stating
      that it ranges over the **wide** `_coherence_window` and over the whole closure.
- [x] Write the (C2) fulfilment emitter's clause shape for `Untl` and `Snce`, naming
      `_scan_forward_bound` / `_scan_backward_bound` as the scan limits and the same wide window
      as the position range.
- [x] Write the (C3) box-faithfulness emitter's two implications (guess true forces the child at
      every position of every active lasso; guess false forces some position to fail), noting it
      is emitted **once, jointly across lassos**, over the **narrow** `_box_window`.
- [x] Write the (C4) target emitter, and state explicitly that `finalize_certificate` invokes it
      with empty premise and conclusion lists so that only the at-least-one and at-most-one
      clauses are emitted there — the guarded per-position implications come from elsewhere.
- [x] Write the per-premise and per-conclusion behaviour call sites: their guarded-implication
      clause shapes over the target window, their opposite polarity, that they run **earlier**
      (during `ModelConstraints.__init__`'s translation, before `_setup_solver` and therefore
      before `finalize_certificate`), and their closure-registration side effect.
- [x] State the call-order invariant this creates: `finalize_certificate`'s guard prevents only a
      second call, so "the closure is complete when `finalize_certificate` runs" is guaranteed by
      `ModelConstraints.__init__`'s fixed call order — external to the class whose correctness
      depends on it.
- [x] Write the `proposition_constraints` hook: currently vacuous by design (atoms deliberately
      unconstrained, per `ADEQUACY.md` Lemma 4's atom case being an identity), yet part of the
      surface because `ModelConstraints` calls it unconditionally and any future settings change
      reintroducing per-atom constraints flows through it without touching `finalize_certificate`.
- [x] Write the assembly paragraph: the seven call sites reach Z3 as exactly four tracked groups
      (frame, model, premises, conclusions), each asserted individually for unsat-core extraction;
      `ModelConstraints` reads `frame_constraints` **by reference** at construction while
      `finalize_certificate` later `extend`s that same list object in place, never rebinding it —
      the contract that makes the two-phase design work, true of this object graph by
      construction rather than by proof.
- [x] Close with the net correction sentence: "no extra constraint" is a claim about the
      conjunction of all seven, assembled through a reference-mutation contract and gated by an
      externally-enforced call-order invariant.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: The surface is seven emission call sites collapsing into four
solver-visible tracked groups. Confirm at implementation time before writing the section, not
after: enumerate every call into a `*_constraints`/`*_behavior` emitter by grepping
`finalize_certificate` in `semantic/core.py`, the `self.instantiate` / premise / conclusion /
`proposition_constraints` calls in `models/constraints.py`, and the tracked-group assembly in
`models/structure.py`. If the live count differs from seven call sites or four groups, write the
observed count and record the divergence in the implementation summary rather than transcribing
the report's number.

**Verification**:
- Every emitter and helper named in the section resolves as a live symbol:
  `grep -n 'def local_coherence_constraints\|def _coherence_clause_at\|def fulfilment_constraints\|def box_faithfulness_constraints\|def target_constraints' semantic/witness_constraints.py`,
  `grep -n 'def _premise_behavior\|def _conclusion_behavior\|def finalize_certificate' semantic/core.py`,
  `grep -n 'def proposition_constraints' semantic/proposition.py`.
- The four tracked group names match the live assembly
  (`grep -n 'frame\|model\|premises\|conclusions' code/src/model_checker/models/structure.py` at
  the `_setup_solver` tracked-group site).
- The reference-mutation claim holds in the live code: `frame_constraints` is `extend`ed and never
  rebound in `finalize_certificate`
  (`grep -n 'frame_constraints' semantic/core.py` shows no `self.frame_constraints =`).
- No `file:line` citations and no task/project-number citations in the file (same two greps as
  Phase 1).
- Diff read-through confirming the only changed hunk is section 4 of `A2_GAP.md`.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - section 4 written.

---

### Phase 3: Sections 5 and 6 — the one-hot selector, and the last independently-defined window [COMPLETED]

**Goal**: The selector is named as structure genuinely absent from (C1)-(C4), given its own
conservativity argument with that argument's own limits stated; and `target_window()` is recorded
as the one remaining independently-defined window, with the deliberateness of the split and the
concrete latent risk both stated.

**Tasks**:
- [x] Write section 5's opening: `ADEQUACY.md` section 1 states (C4) as a bare existential over
      `t₀ ∈ ℤ`; decision D5 implements it with fresh one-hot `sel` variables, an exactly-one
      cardinality constraint, and guarded implications. Nothing resembling `sel` appears in
      (C1)-(C4), in the window-collapse theorems, or in the `Decidable` instances — so the four
      conditions' own proofs do not cover it and it needs its own argument.
- [x] Write the conservativity claim and its three-step argument: the reduction from `∃t₀ ∈ ℤ` to
      `∃ slot` is an identity because `bit` returns the same variable for every position sharing a
      slot under `wrap` and the target window enumerates each slot exactly once; the guarded
      implications are vacuous when `sel` is false, making the encoding a Skolemization; the
      at-least-one clause exactly restates the existential and the at-most-one clause costs
      nothing, with both directions spelled out.
- [x] Write the status paragraph: the argument is correct, self-contained, and recorded in this
      codebase's documentation for the first time — and it is not machine-checked and does not
      verify the Python that is supposed to implement it. Name concrete violations it would not
      see: an off-by-one in the target window's bounds, a swapped implication polarity between
      premise and conclusion, a stale selector memo. Tie this back to section 2 explicitly: even a
      correct informal proof about constraint *meaning* does not discharge a claim about
      constraint *code*, which is the category point recurring one level down.
- [x] Write section 6: `WitnessRegistry.target_window()` and `certificate._box_window` compute the
      numerically identical range from two separately written one-line formulas in two modules,
      with no shared call — the one window left where encoder and re-checker could silently
      diverge, by construction rather than by oversight. Record `certificate.py`'s own reason for
      the split: `target_window` also serves the selector, which has no place in the re-checker's
      vocabulary, while `_box_window` exists to match `mem_all_iff_window`'s bound.
- [x] State why this is worth naming precisely: the two agree today and are simple, yet this is
      exactly the shape of the historical defect (section 7) — a wide/narrow window distinction
      duplicated by hand. If a future Lean-side revision moved `mem_all_iff_window`'s bound,
      `_box_window` would need updating and nothing would force a matching update to
      `target_window()`, reintroducing the same defect class at the selector.
- [x] Reference the separately-scoped work that would close both items by description only —
      never by task or project number.
      *(deviation: altered — a concurrently-dispatched sibling task landed committed changes to
      `witness_registry.py`/`certificate.py` mid-implementation, delegating `target_window()`
      directly to `_box_window` and adding a swept-range regression test pinning their agreement.
      Section 6 was rewritten to describe the gap as closed (historical framing, matching section
      7's pattern) rather than document a now-false "independently defined" claim; section 3(ii)/
      (iii) and section 10's route (e) were updated to match. See the implementation summary.)*

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: prose

**Verification**:
- Selector symbols resolve: `grep -n '_sel\|def target_constraints\|AtMost' semantic/witness_constraints.py`.
- The slot-sharing and window claims hold in the live code:
  `grep -n 'def wrap\|def bit\|def target_window' semantic/witness_registry.py` and
  `grep -n 'def _box_window' -A 4 semantic/certificate.py` show the two ranges are written
  independently and agree numerically; if they do not agree, stop and report rather than
  documenting a false claim.
- Decision D5 is cited as it is named in the source (`grep -n 'D5' semantic/core.py`).
- No `file:line` citations and no task/project-number citations (same two greps as Phase 1) —
  this phase is the first that is tempted to cite a follow-on task, so the grep is blocking here.
- Diff read-through confirming the only changed hunks are sections 5 and 6.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - sections 5 and 6 written.

---

### Phase 4: Sections 7 and 8 — the historical defect, the test's provable blindness, and what a bounded exhaustive test establishes [COMPLETED]

**Goal**: The historical local-coherence defect is presented as concrete evidence that this defect
class is real, the standing A2-triangle test's blindness to it is shown to be provable rather than
suspected, and the limits of bounded exhaustive testing are stated exactly.

**Tasks**:
- [x] Re-read `witness_constraints.py`'s module docstring in full and
      `tests/integration/test_certificate_a2_triangle.py`'s module docstring, so the narrative is
      taken from the source rather than from the research report's paraphrase.
- [x] Write section 7's defect narrative: local coherence was once asserted only over the narrow
      target window on the false reasoning that slot-sharing made one representative clause cover
      every position sharing that slot; why the reasoning is false for the slots adjacent to
      `mid`, using the docstring's own construction; that the counterexample requires `nb = 2` and
      does not exist at `nb = 1`; that it was caught by the pure-Python re-checker's wide-window
      scan disagreeing with the encoder — `ADEQUACY.md` section 6.2's fail-fast differential —
      and not by any proof; and the fix, asserting the biconditional at every position of the wide
      `_coherence_window`, matching the Lean-proved bound.
- [x] Note the window-discriminator fixture as the permanent regression fixture for the
      re-checker's side of the wide/narrow distinction, while stating accurately that it targets
      the general window-collapse property rather than reproducing the encoder defect's `nb = 2`
      shape.
- [x] Write the blindness argument: the standing test's exhaustive tier fixes `back = mid = fwd =
      1`, the defect provably requires `nb = 2`, therefore the test would pass whether or not this
      defect — or its analogue in another emitter — were reintroduced. State that this is a
      provable gap derivable from the docstring's own counterexample, not a suspected weakness,
      and that it is not a criticism of the test in general.
- [x] Write section 8: within its own region the exhaustive tier is a decision, not a sample — a
      complete case analysis over a finite space, stronger than a property test, and should be
      said so. Then the two exact limits: nothing transfers to a larger closure or wider window
      without re-running the enumeration there, with no monotonicity argument available (the
      `nb = 2` case is the concrete demonstration); and passing never certifies A2 as a theorem in
      the sense section 2 requires, because it is an empirical fact about one run of one version of
      the encoder, the re-checker and the Lean checker. Close by placing this in
      `TRUST_PIPELINE.md`'s "property-tested" evidence category, applied to its strongest instance
      here.
- [x] Reference the separately-scoped grid-widening work by description only, never by number.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: prose

**Verification**:
- Every quoted or paraphrased claim about the historical defect is traceable to the live docstring
  (`sed -n '1,45p' semantic/witness_constraints.py`), including the `nb = 2` requirement.
- The standing test's exhaustive regime is confirmed from the live test, not assumed
  (`grep -n 'back\|mid\|fwd' tests/integration/test_certificate_a2_triangle.py` at the Tier 1
  parameter site).
- The named fixture exists:
  `ls tests/fixtures/certificates/04_window_discriminator_coherence.json`.
- `ADEQUACY.md` section 6.2 and section 7.3 are cited by section number and those numbers still
  match (`grep -n '^### 6.2\|^### 7.3' ADEQUACY.md`).
- No `file:line` citations and no task/project-number citations (same two greps as Phase 1).
- Diff read-through confirming the only changed hunks are sections 7 and 8.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - sections 7 and 8 written.

---

### Phase 5: Sections 9, 10 and 11 — the S3 trust-base consequence, the per-route analysis, and See also [COMPLETED]

**Goal**: The document states why the A2 gap is a completeness matter rather than a soundness one,
draws the trust-base corollaries, gives the route-by-route analysis of what closing the gap would
require, and closes with a "See also" matching the sibling documents' convention.

**Tasks**:
- [x] Write section 9's premise: `ADEQUACY.md` section 2's S3 is discharged by *deciding* the
      antecedent on every reported certificate — twice and independently, per section 6.2 — rather
      than by proving the producer correct, which is possible exactly because (C1)-(C4) are
      decidable. State that this is the design's load-bearing property, not a convenience.
- [x] Trace the consequence exhaustively through the two failure branches: a wrongly-constraining
      or under-constraining encoder yields something that fails to decode or fails (C1)-(C4), and
      the fail-fast step rejects loudly; an over-constraining encoder yields UNSAT where a
      countermodel exists, reported as "no certificate found within these bounds", which
      `ADEQUACY.md` section 7.4's never-report-validity rule already establishes was never a
      validity claim — a completeness cost only. State explicitly that there is no third branch,
      and why: passing the re-check *is* what satisfying (C1)-(C4) means, decided directly rather
      than inferred from the encoder's intent.
- [x] State the corollary: the Z3 encoder, the decoder and Z3 itself are not in the soundness
      trust base at all; the soundness trust base is Lean's kernel, the S2 transcription audit,
      the re-checker implementation (mitigated, not eliminated, by the dual Python/Lean check),
      and the translation (S4). Then the ranking corollary: S4, not A2, is the weakest joint in
      the direction already asserted — A2's failure mode is bounded and self-announcing, S4's is
      invisible to the round-trip by construction because both sides consume the same
      already-translated formula, and the box half of the translation has no property-test
      coverage.
- [x] State the honesty point: a "countermodel" verdict — from the Python re-checker, from the
      Lean certificate checker, or from their agreement — says only that the four `Decidable`
      instances returned true on the family rebuilt from the wire. It is not a kernel-checked
      proof for that particular certificate; only the soundness theorem is a proof, and it is a
      proof of the implication applied to whatever the decision procedures certify.
- [x] Write section 10 as the per-route table with a row each for extraction, direct verification
      against a formal semantics of the host language and the Z3 API, reflection inside the
      kernel, widening the exhaustive differential grid, making the selector argument and the
      window agreement executable, and consuming a proof-producing Lean checker — each with what
      it would require, what it would buy, and its cost or status.
- [x] Write section 10's honest ranking: only the first three satisfy section 2's category
      argument on its own terms, and all three are substantial and unstarted; the grid and
      selector routes are concrete and valuable but strengthen evidence within a region and cannot
      become a proof however far the grid is widened, because a finite enumeration is bounded by
      what it enumerates; the proof-producing-checker route addresses the re-checker rather than
      the encoder this document is scoped to.
- [x] Write section 11, "See also", pointing at `ADEQUACY.md` (sections 5.2, 5.3, 7.3), 
      `TRUST_PIPELINE.md` (Stage 2, the trust base, what remains), `ARCHITECTURE.md`, and the
      relevant source modules by path, matching the sibling documents' See-also style.
- [x] Re-read the whole document end to end for register consistency with `ADEQUACY.md` and
      `TRUST_PIPELINE.md` (terse, table-heavy, citation-precise) and for the risk named in Risks:
      that no passage can be read as claiming the encoder is verified.

**Timing**: 1.25 hours

**Depends on**: 4

**Verification Tier**: prose

**Verification**:
- Every `ADEQUACY.md` section number cited across the whole document resolves to a real heading
  (extract each cited number and check it against `grep -n '^#\{2,3\} ' ADEQUACY.md`).
- The four soundness-trust-base members named match `ADEQUACY.md`'s own obligation table and
  trust-base discussion (`sed -n '63,90p' ADEQUACY.md` plus the section 6 trust-base passage).
- The S4 coverage claim is checked against the live adjudicator rather than assumed: confirm what
  `oracle/bimodal_logic/ground_truth.py` covers before asserting the box half is uncovered.
- Blocking: `grep -nEi '\b(task|project) [0-9]+' A2_GAP.md` is empty — section 10 is the passage
  most likely to reach for a task number.
- No `file:line` citations (`grep -nE '\.py:[0-9]+' A2_GAP.md` empty).
- Every internal section reference in the document resolves to one of its own eleven H2 headings.
- Diff read-through confirming the only changed hunks are sections 9-11 of `A2_GAP.md`, and
  `git status --short` shows no modified source or test file.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - sections 9, 10 and 11 written;
  document complete.

---

### Phase 6: Cross-reference wiring and final verification sweep [COMPLETED]

**Goal**: The document is reachable from the three places a reader would look — `ADEQUACY.md`
section 7.3, the docs hub index, and `TRUST_PIPELINE.md`'s See also — and the whole deliverable
passes a final sweep for citation validity, scope compliance, and no-restatement.

**Tasks**:
- [x] Re-read `ADEQUACY.md` section 7.3 immediately before editing (a sibling task dispatched this
      same cycle concerns S4 and may have touched this file). Add a short cross-reference pointing
      at `A2_GAP.md` as the companion treatment of the proof-versus-implementation gap in this
      argument, placed so it reads as an extension of 7.3's own deciding-test discussion rather
      than as a replacement for it.
- [x] Re-read `docs/README.md` immediately before editing. Add the new document in **both** places
      the hub lists each document: the Quick Navigation "Essential Documentation" bullet list
      (with a two-to-three line description matching the style of the `ADEQUACY.md` and
      `TRUST_PIPELINE.md` bullets) and the "Documentation Overview" section (with its own `###
      A2_GAP.md` subsection and bullet list).
- [x] Re-read `TRUST_PIPELINE.md`'s "See also" immediately before editing. Add an `A2_GAP.md`
      entry describing it as the deep treatment of the encoder-side gap that document's Stage 2
      summarizes.
- [x] Final no-restatement check: compare the new document's sections 3, 6, 7 and 9 against
      `TRUST_PIPELINE.md`'s Stage 2 and "The trust base" sections; confirm each overlapping claim
      appears as a citation plus an extension rather than a fresh explanation, and cut or
      re-anchor anything that reads as a restatement.
- [x] Final scope check: `git status --short` shows exactly one new file and exactly three
      modified markdown files, with no file under `semantic/`, `models/`, `tests/`, or `.claude/`
      touched.
      *(deviation: altered — `A2_GAP.md` was committed at the end of phases 1-5, before the
      concurrent-sibling revisions described above required further edits to it in phase 6, so it
      now shows as modified rather than untracked. All four touched paths are still exactly the
      ones this plan names; no source, test, or `.claude/` file is touched.)*
- [x] Stage by explicit file list only (the new document plus the three modified markdown files) —
      never `git add -A`, a directory pathspec, or `git commit -am` — and review
      `git diff --staged` before committing.

**Timing**: 45 minutes

**Depends on**: 5

**Verification Tier**: prose

**Scope Hypothesis**: Four cross-reference edits are required, in three files (`ADEQUACY.md`
section 7.3; `docs/README.md` in two places; `TRUST_PIPELINE.md`'s See also). Confirm at
implementation time by grepping the docs directory for how `TRUST_PIPELINE.md` itself is
referenced (`grep -rn 'TRUST_PIPELINE' code/src/model_checker/theory_lib/bimodal/`) — if that
document is linked from any additional location (for example the theory package README or
`ARCHITECTURE.md`), add the matching reference there too and record the widened scope in the
implementation summary.

**Verification**:
- `grep -rn 'A2_GAP' code/src/model_checker/theory_lib/bimodal/` shows a reference in
  `ADEQUACY.md`, two in `docs/README.md`, and one in `TRUST_PIPELINE.md`.
- Every relative markdown link to the new document resolves to a real file from its own directory.
- Blocking, on all four files: `grep -nEi '\b(task|project) [0-9]+'` is empty for the new
  document and for every hunk added to the three existing documents.
- `git status --short` shows exactly the four expected paths and nothing else; `git diff --staged`
  is reviewed and contains only this task's own hunks.
- Diff read-through confirming every changed hunk in the three existing documents is markdown
  prose in a navigational or cross-reference position, with no existing content deleted or
  reworded beyond the insertion point.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - section 7.3 gains a
  cross-reference to the companion document.
- `code/src/model_checker/theory_lib/bimodal/docs/README.md` - new document added to the Quick
  Navigation bullet list and to the Documentation Overview section.
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` - "See also" gains an
  `A2_GAP.md` entry.

## Testing & Validation

- [x] `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` exists and contains all eleven
      planned H2 sections.
- [x] Every Lean identifier, Python module, function, method and fixture named in the document
      resolves to a live symbol or path (per-phase greps above, re-run once over the finished
      document).
- [x] `grep -nEi '\b(task|project) [0-9]+'` is empty for all four touched files' added content
      (`.claude/rules/no-task-references-in-deliverables.md`; the document sits outside `specs/**`).
- [x] `grep -nE '\.py:[0-9]+'` is empty for `A2_GAP.md` (symbol-level citation register, matching
      `TRUST_PIPELINE.md`).
- [x] Every relative markdown link in the added content resolves to an existing file.
- [x] `git status --short` shows exactly four paths: one new document and three modified markdown
      documents. No file under `semantic/`, `models/`, `tests/`, `oracle/`, or `.claude/` is
      modified.
- [x] No test run is required or expected: the change set contains no Python. As a cheap
      regression guard that nothing outside `docs/` was touched, confirm the above `git status`
      check rather than running the suite.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` (new) - the deep-treatment companion
  document, eleven sections.
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (modified) - section 7.3
  cross-reference.
- `code/src/model_checker/theory_lib/bimodal/docs/README.md` (modified) - hub index entries in two
  places.
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` (modified) - See-also entry.
- `specs/192_a2_proof_vs_implementation_gap_report/summaries/01_*-summary.md` - implementation
  summary, including any Scope Hypothesis confirmations or divergences from Phases 2 and 6.

## Rollback/Contingency

Every phase's output is markdown in four files, and each phase commits its own green state, so
rollback is per-commit and needs no working-tree destruction. To undo a single phase, revert that
phase's commit (`git revert <sha>`), or remove the new document and `git checkout` the three
cross-reference edits **from HEAD** once the tree is clean. If an uncommitted working tree must be
discarded instead, take a durable non-reverting checkpoint first
(`bash .claude/scripts/git-snapshot.sh 192 --no-revert`) and see
`context/contracts/recovery.md`'s rollback rung for the reverting invocation's exact shape,
including its out-of-scope override flag; do not run a bare default-mode snapshot as a routine
precaution. Because sibling tasks share this working tree, never revert by directory or glob — name
the four paths explicitly.

Contingency if Phase 2's Scope Hypothesis fails (the live emission surface differs from seven call
sites or four tracked groups): document the observed surface, not the report's count, and record
the divergence in the summary; the document's argument does not depend on the number being seven.
Contingency if Phase 3's window check finds `target_window()` and `_box_window` already disagree:
stop, do not document agreement, and report the discrepancy — that would be a live defect of the
class this document is about, and belongs in a separate task rather than in a documentation change.
