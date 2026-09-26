# Research Report: Routes to Proving the Certificate Encoder Meets (C1)-(C4)

- **Task**: 195 - research_encoder_spec_proof_routes
- **Started**: 2026-09-26T19:03:35Z
- **Completed**: 2026-09-26T19:40:00Z
- **Effort**: ~35 minutes agent time; recommendations carry their own estimates
- **Dependencies**: 192 (A2_GAP.md, complete)
- **Sources/Inputs**:
  - Local documents: `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (sections 5.2, 5.3, 6, 7.1-7.4), `docs/A2_GAP.md` (sections 2, 4, 5, 8, 9, 10), `docs/TRUST_PIPELINE.md`, `docs/SETTINGS.md`
  - Local code: `semantic/witness_constraints.py`, `semantic/witness_registry.py`, `semantic/certificate.py`, `semantic/core.py`, `semantic/symmetry.py`, `iterate.py`, `tests/integration/test_certificate_a2_triangle.py`, `tests/_lean_check.py`, `tests/unit/test_structure.py`, `code/src/model_checker/models/structure.py`
  - Local artifacts: `specs/193_extend_a2_triangle_grid_to_nb_nf_2/reports/01_extend-a2-triangle-grid.md` (measured candidate counts)
  - BimodalLogic (`~/Projects/BimodalLogic`): `FormalSystem/Metalogic/Decidability/WitnessFamily/{Predicates,Decide,Closure}.lean`, `BiLasso/{Assembly,Enumerate,Extraction}.lean`, `BimodalTools/CheckCertificateMain.lean`, `specs/state.json` (tasks 623, 677-681)
  - Experiments run for this report (see Appendix A): segment-length sweeps against the real search
- **Artifacts**: `specs/195_research_encoder_spec_proof_routes/reports/01_encoder-spec-proof-routes.md`
- **Standards**: report-format.md, subagent-return.md
- **Task Type**: formal
- **Domains**: logic (modal/temporal semantics, decidability), math (periodic structure and divisibility of the searched space)

## Project Context

- **Upstream Dependencies**: BimodalLogic tasks 623 (compression + assembly, `[NOT STARTED]`, deps unmet), 677 (proof-producing `check_certificate`), 680 (record 7.1(iii) prerequisite satisfiable)
- **Downstream Dependents**: task 198 (A3 bound realization), task 199 (round-trip ledger / TRUST_PIPELINE.md revision)
- **Alternative Paths**: consuming a verified bounded enumerator instead of proving the local encoder correct (evaluated below as route (d))
- **Potential Extensions**: segment-length sweeping in the search; a verified SMT-LIB emitter

## Executive Summary

- **Recommendation: do not attempt routes (a), (b) or (c) as a proof of A2 now.** Discharge A2 in
  proportion to what it buys (hardening section 7.4, and making a future A1 consumable), via a
  four-stage path whose first two stages are local, cheap, and independently valuable, and whose
  expensive stage is deferred until A1 is landed or imminent.
- **The single highest-value local finding is not about A2 at all.** The A2-triangle test's leg
  (i)/(iii) comparison is an **aggregate one-bit** comparison (`(accepted > 0) == z3_model_status`,
  `test_certificate_a2_triangle.py:238`). Ten million enumerated candidates collapse to a single
  existential bit, while A2's statement ("exactly the conjunction of (C1)-(C4), no extra
  constraint") is a **per-candidate** claim. A solver-free per-candidate check costs roughly the
  enumeration's existing runtime and turns the strongest evidence in the repository from an
  existential agreement into a decision of the A2 biconditional over the enumerated region.
- **A newly-measured defect in the (ADEQ) space, reproduced against the running search**: the
  searched family space is **not monotone in `back`/`mid`/`fwd`**. A formula was found that is SAT
  at `(3,1,3)` and `(6,1,6)` but genuinely UNSAT (not timeout) at `(4,1,4)` and `(5,1,5)`. The
  encoder fixes *exact* segment lengths (`WitnessRegistry.wrap`'s modulo arithmetic), so a family
  of back-period `nb'` is representable at `nb` iff `nb' | nb`. Consequences: ADEQUACY section
  7.1's condition (iii) is **false as worded** for this search; A3 ("configured lengths
  `>= f(|C|)`") is **insufficient** even with `f` in hand; and `SETTINGS.md`'s user-facing
  "maximum length" / "raising any of the three enlarges the search" is wrong.
- **Route (d), the external verified bounded enumerator, is correctly identified as the cheaper
  route to rigor but for a sharper reason than stated**: it does not discharge A2, it makes A2
  *unnecessary* for the claim A2 exists to support, by deciding bounded absence directly, with
  neither the Python encoder nor Z3 in the loop. Two honest limits: BimodalLogic's own
  `Enumerate.lean` calls its enumeration "astronomically impractical... a decidability
  construction, not an algorithm", so consumption is viable as a **test oracle at the A2-triangle's
  grid points**, not as a production oracle; and the enumerator enumerates lengths `<= n`
  (`ListEnum.upTo`) where this search fixes lengths `= (nb,nm,nf)` -- the same mismatch as the
  monotonicity finding, now visible from both sides.
- **Route (b) as posed (translation validation against a verified specification) is strictly more
  expensive than the verified-emitter variant of (a) that it presupposes**, and is justified only by
  the pipeline features it preserves (unsat cores, `iterate`, orbit exclusion). Neither belongs in
  A2_GAP.md's existing route table, which lists a different route (b) ("direct verification" of the
  Python).
- **Two surface corrections to A2_GAP.md section 4's seven-call-site enumeration**: `iterate.py`'s
  `_pin_theory_specific_values` appends unit clauses directly to `semantics.frame_constraints`
  (`iterate.py:266,280`), an eighth emission path; and `core.py`'s D6 claim that
  `finalize_certificate()` is "the sole writer" of that list is therefore false in the iteration
  path.

## Context & Scope

A2 (ADEQUACY.md section 7.3) holds iff the Z3 constraint set this repository emits is exactly the
conjunction of (C1)-(C4) over windows at least as wide as section 5.2's, with no extra constraint.
The mathematics is machine-checked and sorry-free (the four window collapses and four `Decidable`
instances, `Metalogic/Decidability/WitnessFamily/Decide.lean:335,743,809,865,878,923,927`). The
open obligation is the code-to-specification bridge that section 5.3 argues a proof does not
discharge for a specific piece of Python.

This report evaluates routes to actually proving it, under the proportionality constraint the
adequacy document itself establishes: A3 is vacuous until A1 supplies `f`; A0 caps the strongest
honest claim at "Z-time valid" permanently (`not_validIn_base_prior_UZ` /
`not_validIn_base_z1`, `Metalogic/Independence/ZTimeSharpness.lean:225,236`). So a fully
discharged A2 hardens section 7.4's never-report-validity rule -- which already has a runtime
fail-fast guard (`semantic/model.py`, section 6.2 step 3) -- rather than upgrading the headline
result. It is also the bridge that makes a future A1 usable here at all, which is where most of
its value sits.

Two constraints from the dispatch are honoured rather than rediscovered: route (b)/(c) must not
re-propose a verified bounded enumerator (BimodalLogic task 623 item 2 already scopes one), and
section 7.1's condition (iii) is now satisfiable in principle because section 6 supplies a
certificate export and an independent re-checker. Deliverable is a report with a recommendation and
a staged path, not an implementation.

## Domain Analysis

- **Logic** (primary): the object of proof is a specification stated in modal/temporal semantics --
  the four Hintikka-style conditions on labelled bi-lassos, their finite-window collapses, and the
  `Decidable` instances built from them. Route selection turns on what kind of link can exist
  between a Lean statement about `WitnessFamily` and a claim about running Python.
- **Math** (secondary, and decisive for one finding): the searched space is a set of *exactly
  periodic* label functions. Representability across segment lengths is therefore a divisibility
  question about periods, not an inclusion question about bounds -- which is what produced the
  non-monotonicity result below.
- **Physics**: not applicable; no dynamical-systems content in this task.

## Findings

### Logic-domain findings: what the routes can and cannot establish

1. **The category argument is already settled and should not be re-litigated.** A2_GAP.md section 2
   establishes that no proof about (C1)-(C4) discharges a claim about what a specific piece of
   Python emits without first creating a proof-preserving link: extraction, direct verification of
   the source, or reflection. Every route below is classified by which link it creates, or by which
   obligation it makes unnecessary.

2. **Route (a), verified generator, has a cheaper variant not currently recorded: a verified
   SMT-LIB emitter.** A2_GAP.md's route (a) assumes extraction targeting `z3-solver`'s Python
   bindings. The cheaper form is to specify the generators in Lean over `LabelledLasso`/closure
   data, prove an encoding-adequacy theorem (an assignment satisfies the emitted clause set iff the
   decoded family satisfies (C1)-(C4) over the proved windows), and have Lean **print SMT-LIB2**
   that Python feeds to Z3 unchanged. This deletes the Python generator instead of verifying it.
   Residual trust: Lean's compiled runtime (already trusted for `check_certificate`), an audited
   printer, Z3's parser. No verified-extraction pipeline is needed, and Lean has none.
   - Integration costs that must be named up front: the four `assert_tracked` groups exist for
     unsat-core extraction (`models/structure.py`'s `_setup_solver`); `iterate.py` adds
     per-iteration difference and orbit-exclusion clauses; `semantic/symmetry.py`'s group action
     works on live `WitnessRegistry` variables. A file-based hand-off loses all three unless the
     Lean emitter also emits them.

3. **Route (b), translation validation, is strictly dominated in cost by (2) unless the pipeline
   features are the point.** Per-run validation that the emitted clause set matches a verified
   specification requires *the same* verified Lean generator plus a canonical form on both sides
   (a total order on variables, a normal form for `And`/`Or`/`Implies`/`==`/`AtMost`, and a
   canonical variable naming that survives `WitnessRegistry`'s `lab_{lasso}_{slot}_{repr}`
   spelling). If you have the verified generator, emitting from it is cheaper than validating
   against it. Route (b) is the right answer only if the Python pipeline's incremental features
   must be kept, in which case it is the only route that establishes the property **for the code
   that actually runs**, as the dispatch notes.
   - A2_GAP.md section 10's route (b) is a *different* route ("direct verification" of Python
     against a formalized Python/Z3-API semantics). Translation validation is absent from that
     table and should be added.

4. **Route (c), second implementation plus differential, is what the A2-triangle test is -- and it
   is weaker than its own documentation implies, in two specific ways.**
   - **Aggregate collapse.** `_assert_exhaustive_triangle_agrees` compares
     `(accepted > 0) == structure.z3_model_status` (`test_certificate_a2_triangle.py:238`). At the
     size-2 boxed closure this collapses 10,485,760 enumerated candidates into one bit
     (`specs/193.../reports/01_extend-a2-triangle-grid.md`, measured). An encoder wrong on almost
     every candidate but right about existence passes. A2_GAP.md section 8's claim that the test
     "is a **decision**, not a sample" is true of the *enumeration* but not of the *comparison*.
   - **Reduced independence.** `witness_constraints.py` imports `_coherence_window`, `_box_window`,
     `_scan_forward_bound`, `_scan_backward_bound` from `certificate.py`, and (task 194)
     `WitnessRegistry.target_window()` now delegates to `certificate._box_window`. All four windows
     are shared by import, so **a wrong-but-shared window is invisible to legs (i)/(iii) by
     construction**. The only genuinely independent window source is Lean's leg (ii), which is
     test-only and sampled (Tier 2, `back=mid=fwd=1` only). Sharing removed a real drift risk and
     simultaneously reduced the differential's independence; both halves of that trade should be
     recorded.

5. **Route (d), consume BimodalLogic's verified bounded enumerator: correctly cheaper, but it
   bypasses A2 rather than discharging it.** The enumerator decides "no `WitnessFamily` over
   closure `C` with segment lengths within the bound satisfies (C1)-(C4)" inside Lean, from the
   four landed `Decidable` instances plus an enumeration-completeness lemma. That proposition is
   exactly what an UNSAT verdict here is trying to assert, so the encoder and Z3 drop out of the
   claim entirely -- no encoder-correctness theorem is needed, and no Z3 UNSAT proof.
   - **Only the enumerator's first half is A1-gated.** `validZTime_iff_checkFamily`
     (`BiLasso/Assembly.lean:90`) takes an `fmp` hypothesis, which is A1. But *bounded absence*
     needs only the candidate list plus its `mem_...` completeness lemma, with no `fmp`. So this
     repository can consume a sub-deliverable of task 623 item 2 ahead of item 1. That is the
     precise ask to make of the external repository.
   - **Feasibility is the binding constraint.** `BiLasso/Enumerate.lean`'s own accounting: the
     enumeration is "astronomically impractical... a **decidability** construction, not an
     algorithm", with `#eval` smoke tests confined to a one-state presentation, a two-formula
     closure and `n = 1`. The A2-triangle's grid points are 1.5M-10.7B candidates
     (`specs/193.../reports/01...`). Compiled Lean (`lake exe`) at the smaller grid points is
     plausible and must be measured; kernel `decide` is not, and BimodalLogic has an explicit
     policy of eliminating `native_decide` (`Metalogic.lean:262`,
     `BXCanonical/Completeness.lean:43`).
   - **Trust level, stated honestly.** `lake exe check_certificate`'s own docstring records that a
     verdict "is not a kernel-checked proof... and it inherits whatever trust is placed in Lean's
     compiler". A bounded-absence verdict from a compiled enumerator is compiled-Lean-trusted
     evidence -- strictly better than Python-encoder-plus-Z3, still not kernel-checked.

6. **Reconstructing Z3 UNSAT proofs is the wrong target, independently of its difficulty.** Z3's
   UNSAT is not in the soundness trust base at all (A2_GAP.md section 9's corollary), so
   reconstructing it upgrades only the negative report -- which A0 caps and A1 blocks anyway. The
   ecosystem also points away from Z3 for this (Appendix B).

7. **Reusable Lean infrastructure for route (d) already exists at the BiLasso level.**
   `BiLasso/Enumerate.lean` supplies `ListEnum.ofLen`/`upTo`, `closureSubsets` (with
   `mem_closureSubsets` completeness), `rawLabels`/`mem_rawLabels`, and the
   soundness/completeness pattern (`mem_boundedAnnots` / `boundedAnnots_sound`). A
   `WitnessFamily`-level enumerator is a re-run of this pattern over families rather than
   presentation-relative annotations, which is why the external task scopes it at item-2 size.

### Math-domain findings: the searched space is not monotone in the segment lengths

8. **The encoder fixes exact segment lengths, not maxima.** `WitnessRegistry.wrap` decodes
   `t % nb` for `t < 0` and `nm + (t - nm) % nf` for `t >= nm`
   (`semantic/witness_registry.py:125`), so every allocated family has back-period exactly `nb`
   and forward-period exactly `nf`. A family with back-period `nb'` is representable at `nb` iff
   `nb' | nb` (a function with both periods has period `gcd(nb, nb')`); likewise for `nf`. `mid`
   pads freely.

9. **Measured, not argued: a formula SAT at (3,1,3) and UNSAT at both (4,1,4) and (5,1,5).** See
   Appendix A for the exact inputs, verdicts, `timeout=False` flags and millisecond runtimes. The
   pattern matches the divisibility prediction exactly. This is not an A2 violation -- the encoder
   faithfully encodes families at the lengths it was configured with -- but it falsifies three
   statements now in the documentation:
   - **ADEQUACY.md section 7.1 condition (iii)**, "a demonstration that this repository's search
     enumerates the same family space at a segment length at least that bound", cannot be
     demonstrated as worded: at a single length `>= f(|C|)` the search enumerates only the
     sub-family whose periods divide the configured lengths, not the same space.
   - **A3** ("configured lengths `>= f(|C|)`") is insufficient even once A1 supplies `f`. Honest
     forms: configure lengths that are common multiples of every candidate length up to `f(|C|)`
     (i.e. `lcm(1..f)`, which is `e^{O(f)}` and impractical), or sweep `(back, mid, fwd)` over the
     grid `<= f(|C|)` (at most `f^3` solver calls, cheap), or strengthen A1 to deliver lengths at a
     fixed divisor-friendly value.
   - **`docs/SETTINGS.md`** (lines 20-34) calls `back`/`mid`/`fwd` "maximum length" and states that
     "raising any of the three enlarges the search". Both are wrong and user-facing: a user who
     raises `back` from 2 to 3 can lose a countermodel they previously had. `semantic/core.py`'s D4
     ("the maximum segment lengths") has the same error; `witness_registry.py`'s "fixed segment
     lengths" is the correct wording.

10. **The external enumerator's space is the divisor-closed superset, from the other side.**
    `rawLassos` uses `ListEnum.upTo` (segments of length `<= n`) while `rawLabels` uses `ofLen` at
    each candidate's own lengths (`BiLasso/Enumerate.lean:110,211`). So Lean enumerates lengths
    `<= n` and this repository searches lengths `= (nb,nm,nf)`. Any consumption of route (d) as an
    oracle must reconcile the two spaces, which is the same work as (9).

### Cross-domain synthesis

11. **What demonstrating section 7.1(iii) concretely requires of this repository**, in dependency
    order:
    - **(iii-a) Fix the length space.** Either sweep `(back, mid, fwd)` over the grid up to the
      bound (recommended: `f^3` cheap solves, and it is the only form under which "the same family
      space" is true), or restate A3 in divisor terms. Without this, (iii) is unprovable rather
      than merely unproved.
    - **(iii-b) State and check the represented space.** A written specification of exactly what
      the encoder's satisfying assignments represent: families over closure `C` with
      `1 + |{Box members}|` lassos (uncapped `max_witnesses`), labels `⊆ C`, segment lengths
      exactly `(nb,nm,nf)`, atoms base-only. Checked by a round-trip: a `family -> assignment`
      inverse of `extract_certificate`, plus a per-candidate agreement test (this is Stage 1 below,
      and it is the same deliverable).
    - **(iii-c) Closure agreement.** `semantic/formula.py:156`'s `subformula_closure` is a
      hand-written mirror of `Syntax/Subformulas.lean`, and the closure is load-bearing on both
      sides -- Lean's `LocalCoherentLab`/`BoxFaithful` guard their clauses by
      `closureOf (Γ ++ Del)` (`WitnessFamily/Predicates.lean:71,105`). Lean recomputes its own
      closure from the wire's `target`, so leg (ii) covers it **for accepted certificates only**. A
      direct set-level differential (export `closureOf` from Lean, compare as sets over generated
      formulas) does not exist and is cheap.
    - **(iii-d) Witness-lasso budget.** `max_witnesses` (default `None`, uncapped) *forces* lasso
      sharing when set, which `witness_registry.py`'s own docstring records as trading
      completeness. Any A2/A3 claim must carry the precondition `max_witnesses is None or >=
      |{Box members}|`. ADEQUACY.md does not mention `max_witnesses` at all.
    - **(iii-e) Segment-length parity with the bound's shape.** Once A1 lands, check that the
      bound's three components map onto `back`/`mid`/`fwd` as the search means them (the Lean bound
      is a single `n` over all three segments; the search takes three independent settings).
    - Only (iii-a) is blocking; (iii-b) through (iii-d) are independently valuable now and are
      exactly the Stage 1/2 work recommended below.

12. **Emitted-surface corrections for A2_GAP.md section 4.** Two items, both verified:
    - `iterate.py`'s `_pin_theory_specific_values` appends pinned unit clauses directly to
      `semantics.frame_constraints` (`iterate.py:266` for bits/guesses, `:280` for selectors), an
      **eighth emission path** not in the seven-call-site enumeration. It is by design (the pins
      exist to make a rebuild reproduce a specific model, and the method's own comments document
      why `temp_solver` alone was insufficient), and it affects iteration only, not the first
      solve. It is still part of the surface "no extra constraint" quantifies over.
    - Consequently `semantic/core.py:164`'s D6 comment -- "`finalize_certificate()` is the sole
      writer, mutating this list in place" -- is false in the iteration path and should be
      corrected.
    - `semantic/symmetry.py` emits nothing itself (`apply` is a pure relabeling; every caller
      re-checks with `certificate.recheck`), so it is not an emission path; `iterate.py`'s orbit
      clause built from it is.

13. **A0's standing deciding test is more robust than the suite records.** ADEQUACY.md section 7.2
    requires no certificate "at every configured length"; `tests/unit/test_structure.py:224`
    checks one grid point, `(2,1,2)`. Both the `prior_UZ` and `z1` instances report genuine UNSAT
    at all 11 grid points swept for this report (Appendix A), including `(1,0,1)` and `(4,1,4)`.
    That is a free strengthening of an existing test, and a useful control: the non-monotonicity of
    finding (9) does **not** disturb A0, as (SOUND) predicts it cannot.

## Decisions

- **Recommend against routes (a), (b) and (c)-as-proof now.** All three fail the proportionality
  test: each costs months, and a discharged A2 buys a hardened section 7.4 plus A1-consumability,
  not a stronger headline claim. Route (a)'s verified-SMT-LIB-emitter variant is the one to keep on
  the shelf for later, in preference to extraction-to-Python or direct Python verification.
- **Recommend route (d) as the rigor route, scoped as a test oracle rather than a production
  oracle**, with the enumerator-plus-completeness-lemma requested from BimodalLogic task 623 item 2
  decoupled from item 1.
- **Recommend the per-candidate strengthening of the existing differential as the immediate work**,
  on the grounds that it decides the A2 statement over the region already being enumerated at
  approximately the runtime already being paid.
- **Treat the non-monotonicity finding as the report's primary deliverable alongside the route
  recommendation**, because it makes section 7.1(iii) unprovable-as-worded and A3 insufficient
  independently of which A2 route is chosen, and because its documentation half is user-facing.
- **Do not pursue Z3 UNSAT-proof reconstruction.**

## Recommendations

Prioritized. Effort figures are estimates for a single implementer following this repository's TDD
standard.

### Stage 1 -- per-candidate translation validation in the small (3-5 days, local, no dependencies)

- Add a solver-free evaluator for the emitted clause list under a fully pinned candidate
  assignment (`And`/`Or`/`Not`/`Implies`/`==`/`AtMost` over the registry's bits, guesses and
  selectors; ~50 lines), and assert, **per candidate**, that "every emitted clause is true under the
  candidate's assignment" iff `certificate.recheck` accepts it.
- Keep the existing aggregate assertion; add the per-candidate one beside it. Do not introduce a
  Z3 call per candidate (10M solver calls is infeasible); pinned evaluation is microsecond-scale,
  comparable to `recheck`'s measured 6.4us/candidate.
- Payoff: converts the repository's strongest A2 evidence from a one-bit existential agreement into
  a decision of the A2 biconditional over the enumerated region, and localizes a failure to a named
  candidate instead of a closure. This is translation validation in the small, and the only
  cheap route to a statement of the shape A2 actually has.

### Stage 2 -- the 7.1(iii) prerequisites (1.5-2 weeks, local, no dependencies)

- **2a. Segment-length space.** Document the exact-length/divisibility fact; add the reproducing
  test from Appendix A as a standing regression; then either implement a `(back, mid, fwd)` sweep
  (a search-level option, off by default) or restate A3 in divisor terms in ADEQUACY.md. Fix
  `docs/SETTINGS.md:20-34` and `semantic/core.py`'s D4 wording, and add a user-facing note that
  raising a length is not monotone.
- **2b. Represented-space specification and round-trip.** Write down (iii-b)'s specification; add
  the `family -> assignment` inverse and its round-trip test.
- **2c. Closure differential.** Export `closureOf` from a small `lake exe` (or reuse
  `check_certificate`'s decoder) and compare against `semantic/formula.py`'s closure as sets over
  generated formulas.
- **2d. Preconditions.** Record `max_witnesses` in ADEQUACY.md as a precondition of A2/A3, and make
  the search warn (or refuse) when `max_witnesses < |{Box members}|`.
- **2e. Free wins.** Extend `TestA0FrameClassStandingTest` to the swept grid (Appendix A);
  correct A2_GAP.md section 4 with finding (12)'s eighth emission path and fix `core.py`'s
  "sole writer" comment.

### Stage 3 -- consume the verified bounded enumerator as a test oracle (1 week local, after the external deliverable)

- Ask BimodalLogic for the item-2 sub-deliverable only: `boundedFamilies`-style candidate list over
  closure `C` and segment bound `n`, its `mem_...` completeness lemma, and a `lake exe` that
  decides bounded absence for a given `(Γ, Δ, n)` -- explicitly **not** gated on item 1's `fmp`.
- Locally: a Tier-2 replacement that runs that executable at the A2-triangle's feasible grid points
  and compares its bounded-absence verdict against the Python search's SAT/UNSAT, reusing
  `tests/_lean_check.py`'s skip discipline. Measure before committing: the enumeration is
  astronomically impractical past small parameters by its own authors' account.
- Reconcile the `<= n` versus `= (nb,nm,nf)` space mismatch using Stage 2a's outcome.
- Payoff: bounded absence becomes compiled-Lean-checked rather than Z3-and-encoder-trusted at those
  points, with neither the encoder nor Z3 in the claim. This is the cheapest available increase in
  rigor, and it is why route (d) outranks (a)-(c).

### Stage 4 -- deferred: the verified SMT-LIB emitter (2-3 months, blocked on proportionality)

- Only once A1 has landed or is imminent (BimodalLogic task 623, `[NOT STARTED]`, 2-4 weeks
  estimated, dependencies unmet). Lean side: clause syntax, generators over the proved windows, an
  encoding-adequacy theorem in both directions, a canonical printer (~4-8 weeks). Python side:
  replace local generation with the emitted file (~1-2 weeks), plus the unsat-core / `iterate` /
  symmetry integration costs of finding (2).
- Prefer this over A2_GAP.md route (a)'s extraction-to-Python (no verified extraction exists for
  Lean) and over its route (b)'s direct Python verification (no tooling). Choose translation
  validation instead of emission only if the incremental pipeline features must be preserved.

## Risks & Mitigations

- **Risk**: Stage 1's per-candidate check finds a real disagreement, turning a research task into a
  defect hunt. **Mitigation**: that is the point; report it as a finding and scope diagnosis
  separately, as the task-193 dispatch already directed for three-way disagreements.
- **Risk**: Stage 2a's sweep multiplies solver calls by up to `f^3` and changes default runtimes.
  **Mitigation**: ship the sweep off by default; document it as the only setting under which a
  future A3 claim is available.
- **Risk**: Stage 3's external deliverable slips or arrives A1-gated anyway. **Mitigation**: the
  ask is explicitly for the non-`fmp` half; Stages 1-2 carry their own value and do not depend on
  it.
- **Risk**: the non-monotonicity fix is read as a behavioural regression by users who tuned lengths
  upward. **Mitigation**: documentation-first (2a), with the sweep opt-in.
- **Risk**: a verified emitter (Stage 4) reintroduces an S4-shaped translation obligation at the
  printer. **Mitigation**: the printer is small and auditable, and the canonical-form comparison of
  Stage 1 can be reused to pin it; state the residual honestly rather than claiming it away.

## Context Extension Recommendations

- **Topic**: Periodicity and divisibility of the searched certificate space.
  **Gap**: No context file records that `back`/`mid`/`fwd` are exact periods, that
  representability across lengths is a divisibility condition, or that the search is therefore
  non-monotone in its own settings. Three separate documents state the opposite.
  **Recommendation**: add a short domain note under `context/project/math/` (order/periodic
  structure) cross-referenced from the bimodal theory docs, and cite it from ADEQUACY.md
  section 7.1/A3.
- **Topic**: What "verified" means across a compiled-executable boundary.
  **Gap**: kernel-checked versus compiled-Lean versus property-tested is stated in
  `TRUST_PIPELINE.md` for this theory but not as reusable context, and it is the distinction every
  route in this report turns on.
  **Recommendation**: a note under `context/project/logic/` distinguishing the four evidence kinds
  with the `check_certificate` example.

## Appendix

### Appendix A -- experiments run for this report

All runs used the real `Syntax -> ModelConstraints -> BimodalStructure` pipeline (the same
construction order `test_certificate_a2_triangle.py`'s `_build` helper uses), `PYTHONPATH=code/src`,
`max_time` 20-120s. `z3_model_status` alone is ambiguous -- `models/structure.py:293` maps solver
UNKNOWN to `status=False` with `timeout=True` -- so the decisive runs report `timeout` and runtime
explicitly.

**A.1 Non-monotonicity (finding 9).** Premises pin `\prev`-chains at fixed distances behind the
target; conclusions empty.

- `alt2` = `['\prev A', '\prev \prev \neg A', '\prev \prev \prev A', '\prev \prev \prev \prev \neg A']`
  (requires `A, ¬A, A, ¬A` at `-1..-4`):
  `(2,1,2)` SAT · `(3,1,3)` **UNSAT** · `(4,1,4)` SAT · `(5,1,5)` SAT · `(6,1,6)` SAT
- `alt3` = the same shape with pattern `A, ¬A, ¬A, A, ¬A, ¬A` at `-1..-6`:
  `(2,1,2)` UNSAT · `(3,1,3)` **SAT** · `(4,1,4)` **UNSAT** · `(5,1,5)` **UNSAT** · `(6,1,6)` SAT
- Every verdict above: `timeout=False`, runtime 0.002-0.006s. `alt3` is therefore refutable at
  `(3,1,3)` and reported "no certificate" at `(5,1,5)`, strictly larger in every coordinate.
- Slot arithmetic confirming the mechanism: at `nb=3`, positions `-1` and `-4` share slot `2`
  (`-1 % 3 = 2 = -4 % 3`), so `alt2`'s `A` at `-1` and `¬A` at `-4` are the same Boolean.

**A.2 A0 robustness (finding 13).** Formulas taken verbatim from
`tests/unit/test_structure.py:224` (`prior_UZ`: `(\future A \rightarrow (A \Until \neg A))`, event-first;
`z1`: `(\Future (\Future A \rightarrow A) \rightarrow (\future \Future A \rightarrow \Future A))`),
plus an Until-fixpoint control. All three report UNSAT at all of
`(1,1,1) (2,1,1) (3,1,1) (1,1,2) (2,1,2) (3,1,2) (2,1,3) (3,1,3) (2,2,2) (4,1,4) (1,0,1)`.

**A.3 Negative result worth recording.** An initial sweep of six ordinary examples over eight grid
points found no non-monotonicity; the effect required formulas that pin positions at several fixed
distances behind (or ahead of) the target. A first attempt at the `prior_UZ` formula without outer
parentheses and with `\Future` read as "eventually" produced spurious SAT results; the suite's own
formula strings are the correct source, and `\Future` is `G` while `\future` is `F`.

### Appendix B -- external practice, for the routes evaluated

Pointers, not claims of applicability; none of this tooling is referenced anywhere in either
repository today.

- **Translation validation** as a discipline: Pnueli, Siegel and Singerman, "Translation
  validation" (TACAS 1998); Necula, "Translation validation for an optimizing compiler" (PLDI
  2000). The pattern is per-run validation of a producer's output against a specification, which is
  route (b)'s shape exactly.
- **Certifying algorithms**: McConnell, Mehlhorn, Näher and Schweitzer, "Certifying algorithms"
  (Computer Science Review, 2011). The design already in place here -- decide the antecedent on
  every output rather than verify the producer -- is the certifying-algorithm pattern, and
  A2_GAP.md section 9's trust-base corollary is its standard consequence.
- **Proof-carrying checkers in proof assistants**: verified DRAT/LRAT checkers (GRAT in
  Isabelle/HOL; `cake_lpr` in CakeML) are the mature end of this ecosystem; SMTCoq (CAV 2017)
  reconstructs veriT/CVC4 certificates in Coq, and the Alethe format with the Carcara checker is
  the current SMT proof-certificate line. Lean 4 has cvc5-backed reconstruction work
  (`lean-smt`). Z3's own proof logs are the least supported target of this family, which is why
  route (d)'s "no Z3 in the claim" framing is preferable to reconstructing its UNSAT.
- **Verified extraction**: CertiCoq and CakeML are the reference points for compiling verified
  functional code with a proof; Lean 4 has no verified extraction, and its compiled output is
  trusted -- which is precisely the trust level `lake exe check_certificate` already operates at.

### Appendix C -- key citations used above

- `ADEQUACY.md`: section 5.2 (window table), 5.3 (differential obligation), 6.1-6.3 (wire contract,
  four-step dual verification, S4), 7.1 (A1 route and conditions (i)-(iii)), 7.2 (A0, permanent),
  7.3 (A2 statement, A2-triangle test, selector conservativity), 7.4 (never report validity).
- `A2_GAP.md`: section 2 (category argument, three link types), 4 (seven call sites), 5 (selector),
  8 (what a bounded exhaustive test establishes), 9 (trust base, S3 corollary), 10 (routes (a)-(f)).
- BimodalLogic: `WitnessFamily/Decide.lean:335,743,809,865,878,923,927`;
  `WitnessFamily/Predicates.lean:71,92,105,114`; `WitnessFamily/Closure.lean:54`;
  `BiLasso/Assembly.lean:90,115`; `BiLasso/Enumerate.lean:58,63,110,149,189,211,305`;
  `BiLasso/Extraction.lean:354`; `BimodalTools/CheckCertificateMain.lean` (trust model);
  `Metalogic/Independence/ZTimeSharpness.lean:225,236`.
- This repository: `semantic/witness_registry.py:125,171`; `semantic/witness_constraints.py`
  (module docstring's historical defect; the four generators); `semantic/core.py:164,213-330`;
  `semantic/certificate.py:213-229,353`; `iterate.py:190-282`; `models/structure.py:270-293`;
  `tests/integration/test_certificate_a2_triangle.py:157-244`; `tests/unit/test_structure.py:224`;
  `docs/SETTINGS.md:20-45`.
