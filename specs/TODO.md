---
next_project_number: 207
---

# TODO

## Task Order

*Updated 2026-09-27. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 197,198,203,204,205,206 | -- | architecture, testing, semantics |
| 2 | 199,200 | 197,198 | documentation, semantics |

**Grouped by Topic** (indented = depends on parent):

### Documentation

199 [NOT STARTED] — Write the round-trip ledger in...

### Architecture

205 [NOT STARTED] — Establish the correct division of labour between testing and...

### Testing

204 [IMPLEMENTING] — Strengthen the A2-triangle encoding-completeness differential...
206 [NOT STARTED] — Refactor the bimodal verification test harness for...

### Semantics

197 [NOT STARTED] — Harden the certificate wire protocol on two axes, so that...
  └─ 200 [NOT STARTED] — Extend the bimodal theory to the language with the stability...
198 [NOT STARTED] — Make bound realization (A3) a computation rather than an...
203 [IMPLEMENTING] — Research and recommend whether the bimodal search should...

## Tasks

### 206. Refactor verification test harness
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None

**Description**: Refactor the bimodal verification test harness for organization and performance, refactoring structure rather than preserving it where that produces a better result. This task owns the harness itself; the trust boundary between testing and formal verification is owned by a separate task and is explicitly out of scope here. Nothing in this task may weaken what the existing tests establish, and any narrowing of an enumeration must be stated explicitly rather than absorbed as a speedup.

ORGANIZATION. Verification support code currently sits inside the test tree as code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py (the compile-once pinned evaluator and the candidate-to-assignment builder) while behaving like a library rather than a test module. Tier membership is expressed in three places at once: prose in the module docstring of tests/integration/test_certificate_a2_triangle.py, per-class pytest markers, and a class-level skipif keyed on BIMODAL_LOGIC_PATH. Grid configurations and premise families are restated across tests/integration/test_certificate_a2_triangle.py, tests/integration/test_search_period_coverage.py, tests/unit/test_witness_registry.py and tests/unit/test_structure.py. Assess whether one declarative registry of tiers and configurations, consumed by every module, is better than the current distributed expression, and whether the evaluator belongs outside the test tree given that a separate task is evaluating promoting a checker onto the production path. Coordinate on that point rather than pre-empting it: if the evaluator may become a shipped artifact, say what that implies for its location and public surface, but do not make the promotion decision here.

PERFORMANCE. Authoritative measurements already exist and should be reproduced, not re-estimated from scratch. Under CI's exact invocation shape (pytest -n 4 --timeout=300 --timeout-method=thread over the real target set), the widest boxed Tier 1 case runs 123.29s over 10,485,760 candidates, which is 1.91x the aggregate-only baseline and leaves roughly 59 percent headroom against the 300s per-test ceiling; the second boxed case runs 17.77s over 1,572,864 candidates; the widest box-free case runs under 2s. The headroom assumes CI hardware no more than about 2.4x slower than the measuring host, a margin currently documented in TestExhaustiveTriangleWithBox's docstring. Decide whether that margin is adequate and compare at least four routes: moving the widest case off the per-PR path to a scheduled run while keeping the 17.77s case in the PR gate; sharing solved structures across cases through pytest fixtures instead of re-solving per test; caching or reusing the compiled evaluator across configurations; and any algorithmic reduction of the enumeration itself. Measure before and after under the same invocation shape, on the same host, and report both numbers. A scheduling change is a legitimate outcome and is not a retreat.

CONSTRAINTS. Preserve Tier 2's clean-skip behaviour as it stands (its promotion is the other task's decision, not this one's). Preserve the timeout-is-False assertions in the A0 standing tests and the search-coverage grid pins, which exist so an inconclusive solver run cannot pass as a genuine UNSAT. Preserve the retained aggregate assertion alongside the per-candidate comparison, since it is the only check of the real Z3 search verdict as distinct from the pinned constraint-set evaluation. Verify against the four-theory gate as well as the bimodal suite, and confirm the repository-wide target set stays green.

---

### 205. Certifying countermodel architecture
- **Status**: [NOT STARTED]
- **Task Type**: formal
- **Topic**: architecture
- **Dependencies**: None

**Description**: Establish the correct division of labour between testing and formal verification for the bimodal pipeline, so that a countermodel the Z3 search reports can be trusted on the strength of an independent verified check rather than on the correctness of the encoder or of Z3. Research and recommend the architecture, then stage it; this task owns the trust boundary, not the test-harness refactoring (a separate task owns that).

THE GOVERNING ASYMMETRY. A countermodel is a positive, checkable witness: given a concrete structure and a formula, whether the structure falsifies the formula is finite and decidable, so a SAT verdict can be validated per run without trusting the encoder, the extraction, or the solver. The absence of a countermodel has no witness, so an UNSAT verdict can only be trusted by proving the search complete (A2), the bounds adequate (A1/A3), and Z3's UNSAT sound -- and ADEQUACY.md section 7.4 already declines to make that claim, with a runtime fail-fast guard. Effort should therefore concentrate where results are not independently checkable, and testing should cover where they are. Under a mandatory per-run check, every encoder, extraction and solver bug becomes a liveness failure (a missed countermodel, or an error) rather than a soundness failure (a reported countermodel that is not one), which is the guarantee this task exists to secure.

QUESTION 1, THE CHECKER'S ACTUAL REACH. Determine what the existing Lean development's re-checker establishes today: whether it decides falsification of a formula by a concrete structure under the semantics, or only well-formedness and consistency of an exported certificate. This distinction decides whether the rest of this task is extraction and plumbing work or genuine new Lean proof work, and it must be settled first by reading the Lean side rather than inferred from this repository's tests. Report the answer explicitly either way.

QUESTION 2, MANDATORY VERSUS SAMPLED. The bounded Lean cross-check (TestBoundedLeanCrossCheck in tests/integration/test_certificate_a2_triangle.py) is currently a sampled test tier that clean-skips when BIMODAL_LOGIC_PATH is unset, so in a default CI run the only check that validates a candidate countermodel against the semantics disappears entirely. Evaluate promoting that check from a sampled tier to a gate on reported output: a countermodel that has not been checked is either labelled as unchecked or not reported. Assess what that does to the user-facing contract, to SETTINGS.md, and to section 7.4's existing guard.

QUESTION 3, RUNTIME AVAILABILITY. A mandatory check must not imply a mandatory Lean toolchain for users. Evaluate extracting the checker to a standalone verified artifact shipped with the package (Lean's C backend, or an equivalent), against the alternatives of an optional two-tier trust model (unchecked versus checked countermodel), a re-implementation in Python (which reintroduces the code-to-specification gap this task is trying to avoid, and should be assessed as such rather than dismissed), and requiring the toolchain. Cost each route, including packaging and CI implications, and recommend one with a staged path.

QUESTION 4, TRANSPORT FIDELITY. The surface between a Z3 model and the checker's input is where a soundness failure could still hide, since a faithful checker fed an unfaithful transport proves nothing about the structure Z3 actually found. Assess the round trip through extract_certificate (semantic/core.py), certificate.py's wire format, and the candidate-to-assignment builder in tests/_pinned_eval.py, which is extract_certificate's mechanical inverse and duplicates its atom mapping. Recommend property-based and round-trip coverage for this surface specifically, rather than exhaustive enumeration, and say whether the two inverse mappings should be unified.

REPOSITIONING THE EXISTING TESTS, NOT WEAKENING THEM. The A2-triangle Tier 1 differential and the search-coverage grid pins are liveness and regression evidence for the UNSAT direction, not countermodel trust. Say so in the documentation so the tiers' purposes are not conflated, and reassess their cost on that basis rather than on a soundness basis. Nothing here licenses deleting or narrowing them.

DEFERRED, NAMED HERE SO IT IS NOT REDISCOVERED. A structural conformance check that the emitted Z3 constraint set matches the (C1)-(C4) schema instantiated at the configured bounds -- extending the existing operator-inventory and atom-coverage guards, linear in formula size rather than candidate space -- remains worthwhile, but is UNSAT-direction work and is explicitly sequenced after the certifying architecture above. Record it as a follow-on with the reasoning, and do not build it here.

Out of scope: the A1 compression bound, the divisor-period sweep driver, the pytest harness reorganization and its performance work, and any change that weakens what the existing tests establish. Report any genuine encoder divergence found as a finding rather than diagnosing it.

---

### 204. Strengthen a2 triangle per candidate
- **Status**: [IMPLEMENTING]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None
- **Research**: [204_strengthen_a2_triangle_per_candidate/reports/01_strengthen-a2-triangle-per-candidate.md]
- **Plan**: [204_strengthen_a2_triangle_per_candidate/plans/01_strengthen-a2-triangle-per-candidate.md]

**Description**: Strengthen the A2-triangle encoding-completeness differential from an aggregate verdict to a per-candidate comparison. The leg (i) versus leg (iii) comparison is currently a one-bit existential at tests/integration/test_certificate_a2_triangle.py:238 -- (accepted > 0) == z3_model_status -- so up to 10.5 million enumerated candidates collapse into a single SAT/UNSAT agreement, while A2 is a claim about each candidate individually. A candidate the encoder wrongly rejects and the re-checker accepts, or the reverse, is invisible so long as the aggregate verdicts still agree. Compare the two legs candidate by candidate instead, reporting the first divergence with enough of the candidate to diagnose it. Keep the cost envelope in view: the widest configured closure already reaches 10.5 million candidates, so measure before committing to unconditional execution and tier or slow-mark the new comparison as the existing cases are, verifying against CI exact invocation shape (--timeout=300 --timeout-method=thread, run with -n 4) rather than a bare idle-host figure. Keep Tier 2 clean-skip discipline intact. Report any genuine divergence as a finding; diagnosing the encoder is out of scope. This is the lead recommendation of the encoder-specification proof-routes research, preferred over routes that attempt proof.

---

### 203. Research divisor period search coverage
- **Status**: [IMPLEMENTING]
- **Task Type**: z3
- **Topic**: semantics
- **Dependencies**: None
- **Research**: [203_research_divisor_period_search_coverage/reports/01_divisor-period-search-coverage.md]
- **Plan**: [203_research_divisor_period_search_coverage/plans/01_divisor-period-search-coverage.md]

**Description**: Research and recommend whether the bimodal search should cover all divisor-periods up to each bound rather than only the exact period, and at what cost. WitnessRegistry.wrap() currently fixes exact periods, so a family of back-period nbprime is representable only when nbprime divides nb, making the searched space non-monotone in back/mid/fwd (a formula can be SAT at (3,1,3) and (6,1,6) while genuinely UNSAT at (4,1,4) and (5,1,5)). Documenting that behavior honestly is handled by a separate task; this task evaluates fixing it. Compare at least three routes: (a) leave exact-period semantics and rely on documentation plus a user-facing rule; (b) search the union over all divisors of each bound, assessing the blow-up in slot count, Z3 variable count and solve time, and whether the one-hot sel selector and conditions (C1)-(C4) survive unchanged; (c) reformulate the encoding so a bound means "period at most n" directly, and cost what that does to the certificate wire format and the Lean-side re-checker, which consume the same window bounds. Weigh each against the proportionality constraint the adequacy document establishes, and account for the interaction with ADEQUACY.md section 7.1 condition (iii), which this non-monotonicity falsifies as worded. Deliver a report with a recommendation and a staged path, not an implementation.

---

### 202. Correct nonmonotonic search bound docs
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: documentation
- **Dependencies**: Task 201
- **Research**: [202_correct_nonmonotonic_search_bound_docs/reports/01_nonmonotonic-search-bound-fixes.md]
- **Plan**: [202_correct_nonmonotonic_search_bound_docs/plans/01_nonmonotonic-search-bound-docs.md]
- **Summary**: [202_correct_nonmonotonic_search_bound_docs/summaries/01_nonmonotonic-search-bound-docs-summary.md]

**Description**: Correct the user-facing claim that the bimodal search is monotone in back, mid and fwd, which it is not. WitnessRegistry.wrap() folds positions by exact period -- negative positions as t % nb, forward positions as nb + nm + ((t - nm) % nf) -- so a lasso family of back-period nbprime is representable if and only if nbprime divides nb. Raising a bound therefore does not enlarge the searched family space monotonically: it can discard families a smaller bound represented. Measured against the running search, one formula is SAT at (back,mid,fwd) = (3,1,3) and (6,1,6) but genuinely UNSAT (timeout=False, millisecond runtimes) at (4,1,4) and (5,1,5), exactly as divisibility predicts. The consequence for users is severe and currently undocumented: widening a bound to search harder for a countermodel can silently lose one a narrower bound found. Correct every location promising otherwise: the bimodal docs/SETTINGS.md description of back/mid/fwd, semantic/core.py D4 commentary (the "maximum length" language and "raising any of the three enlarges the search"), and ADEQUACY.md section 7.1 condition (iii) plus the A3 wording treating "lengths at least f(|C|)" as sufficient, since sufficiency requires divisibility rather than magnitude. State the exact-period semantics plainly and give users the operative rule (prefer a bound that is a multiple of the periods of interest). Documentation and comments only: whether to CHANGE the search semantics is deliberately out of scope and is handled by a separate task.

---

### 201. Correct a2 gap emitted surface and sole writer
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: documentation
- **Dependencies**: None
- **Research**: [201_correct_a2_gap_emitted_surface_and_sole_writer/reports/01_a2-gap-surface-correction.md]
- **Plan**: [201_correct_a2_gap_emitted_surface_and_sole_writer/plans/01_a2-gap-surface-correction.md]
- **Summary**: [201_correct_a2_gap_emitted_surface_and_sole_writer/summaries/01_a2-gap-surface-correction-summary.md]

**Description**: Correct A2_GAP.md's emitted-constraint surface and semantic/core.py's sole-writer claim, and record the independence cost of window sharing. A2_GAP.md section 4 enumerates seven emission call sites, but iterate.py:266 and :280 append unit clauses directly to semantics.frame_constraints, which is an eighth path the section omits and a direct counterexample to semantic/core.py:164's claim that finalize_certificate() is the sole writer of frame_constraints. Correct both: add the iterate.py path to A2_GAP.md's enumeration with its clause shape, and fix or properly qualify core.py:164's comment. Separately, record a cost the window-sharing change introduced: WitnessRegistry.target_window() now delegates to certificate._box_window, which removes the drift hazard but also reduces the A2-triangle differential's independence, so a window that is wrong but shared is invisible to that test by construction. A2_GAP.md should state this trade explicitly rather than presenting the sharing as a pure gain. Documentation and comments only; no behavioral change.

---

### 200. Extend bimodal to stability modal
- **Status**: [NOT STARTED]
- **Task Type**: z3
- **Topic**: semantics
- **Dependencies**: Task 193, Task 194, Task 197

**Description**: Extend the bimodal theory to the language with the stability modal, once the verified side supplies a state-sharing witness structure, its histories characterization, its redesigned box condition, and a compression bound. The modal is absent from this theory entirely today: operators.py defines negation, conjunction, disjunction, bottom, Box, Future, Past, Until, Since and the defined operators, with no stability modal, and ADEQUACY.md states it is out of scope throughout. Adding it is not an operator definition plus a truth clause. The received account of why this design is deterministic is explicit that the obstruction is not Limit or Saturation but the histories characterization and the box case of the truth lemma: determinism is what makes every world history one of the lasso orbits, so sharing states between lassos lets a history cross from one lasso to another, breaks that characterization and the corollary that the frame's history set is exactly the certified histories, and breaks box faithfulness, which is calibrated against "every position of every lasso" and stops enumerating the history set once histories recombine. Consequently this task's scope is: add the operator and its truth conditions; replace the certificate datatype with the verified side's branching structure; re-encode the conditions for Z3 over that structure, box faithfulness in particular, which can no longer be a conjunction over lasso positions; extend the wire contract and the re-checker in step, coordinating the breaking change with the producing side; and set search bounds from the new compression function. Also revisit the iteration machinery: the symmetry group for orbit-distinctness (rotation per lasso, permutation of witness lassos) is defined for a family of lassos and will need a different group action on a branching structure. BLOCKED on the four verified-side tasks (decidability provenance gate, state-sharing structure and box-condition redesign, agreement lemma over all walks, compression and assembly); until the agreement lemma lands there is no soundness argument for any certificate this encoding could emit, and emitting one anyway would violate the never-report-validity discipline in the opposite direction, by reporting countermodels nothing certifies.

---

### 199. Adequacy round trip ledger
- **Status**: [NOT STARTED]
- **Task Type**: markdown
- **Topic**: documentation
- **Dependencies**: Task 192, Task 193, Task 194, Task 195, Task 196, Task 197, Task 198

**Description**: Write the round-trip ledger in code/src/model_checker/theory_lib/bimodal/docs/: a single document stating, once and end to end, the biconditional between what the model checker reports and what paper models exist, with every leg's discharge cited and every residual named. The statement to record is the achievable one, not the desired one: that the search returns a certificate for a given premise/conclusion pair at lengths at or above f of the closure size if and only if the conclusion is not a Z-time consequence of the premises -- the forward direction being (SOUND), the backward being (ADEQ), and the frame class being Z-time rather than the paper's full consequence relation. For each leg, cite how it is discharged and by what kind of evidence, keeping the four categories distinct: machine-checked theorem, audit by inspection, decided per run, and property-tested. Cover at minimum: S1 (proved), S2 (an audit, narrowable but never a theorem), S3 (decided per run, twice, independently -- and record the consequence that the Z3 encoder, the decoder and Z3 itself are not in the soundness trust base, so encoder defects can cost completeness or raise a loud rejection but cannot manufacture a false countermodel report), S4 (the translation bridge), A0 (a permanent frame-class limit, not an open problem), A1 (BimodalLogic's compression theorem), A2 (encoding completeness) and A3 (bound realization). Close with the honest ceiling: three residuals no further work removes -- A0's frame-class gap, S2's irreducibly informal paper-to-formalism boundary, and the deciding procedure's scope covering the language without the stability modal. Documentation only: this task synthesizes and cites the work of the others rather than doing any of it.
CORRECTION to the closing section specified above: do not present the three residuals as alike. Two are permanent and no further work removes them -- the frame-class gap, and the irreducibly informal paper-to-formalism boundary of the transcription audit. The third, the deciding procedure's scope covering only the language without the stability modal, is NOT permanent: it is an open but scoped limitation with a named route, and a task chain now exists for it on both sides (verified side: a decidability-provenance gate, a state-sharing witness structure with the box condition redesigned, an agreement lemma over all walks, and a compression bound; this side: the theory extension that consumes them). State it as such, citing the obstruction accurately -- not Limit or Saturation, but the histories characterization and the box case of the truth lemma -- so a reader is not left believing the stability modal is excluded in principle when it is excluded pending identified work.
SCOPE CHANGE (the base document now exists). TRUST_PIPELINE.md has since been written in code/src/model_checker/theory_lib/bimodal/docs/, and it already delivers the pipeline walk-through, the four evidence kinds, the trust-base statement and its corollaries, the (ADEQ) component table, the cross-repository remaining-work tables, the stability-modal obstruction, and the three-residual ceiling with the permanent-versus-routed distinction this task's own CORRECTION above called for. This task is therefore no longer "write the ledger from scratch": it is to REVISE that document into a final per-leg ledger once the legs it describes have actually landed. The remaining delta is (a) a per-leg table giving each obligation its discharge citation as landed, rather than as planned, (b) replacing the forward-looking remaining-work tables with what was actually done and what was actually left, and (c) re-verifying every cited file, line and theorem name still resolves, since the Lean development reorganizes its directories periodically and a citation audit was already needed once. Do not duplicate the existing document; edit it.

---

### 198. A3 compute bounds from closure
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: semantics
- **Dependencies**: None

**Description**: Make bound realization (A3) a computation rather than an assumption: once BimodalLogic's compression theorem supplies a computable f of the closure size, have the search compute f(|C|) from the closure and set its own back, mid and fwd lengths from it, instead of taking them as user settings whose adequacy is assumed. ADEQUACY.md's assumption table records A3 as vacuous until A1 supplies f, so this task is the consumer of that result. Two deliverables beyond the arithmetic: first, report the distinction honestly in output -- a run at lengths at or above f(|C|) may say "exhaustive at this closure", while a run below it must keep saying only that no certificate was found within these bounds, never that the argument is valid, per section 7.4's never-report-validity rule. Second, keep the frame-class caveat attached: even at adequate lengths the conclusion available is Z-time relative, since A0 is a permanent limit, and BimodalLogic's own scope note records that the deciding procedure covers the language without the stability modal, its witness models being deterministic, on which that modal is trivial. BLOCKED on BimodalLogic's compression task (the Decidable ValidZTime quasimodel/ShiftSet route, whose item 1 is A1 and whose item 2 builds the candidate list over those same bounds); there is no f to read until it lands, and nothing here should invent one.

---

### 197. Harden certificate wire proof carrying
- **Status**: [NOT STARTED]
- **Task Type**: z3
- **Topic**: semantics
- **Dependencies**: Task 196

**Description**: Harden the certificate wire protocol on two axes, so that acceptance becomes a kernel-checked entailment and deserialization leaves the trust base. First, proof-carrying acceptance: ADEQUACY.md section 6.2 is explicit that a "countermodel" verdict says only that the four Decidable instances returned true on the family rebuilt from the wire input, and is not a kernel-checked proof for that particular certificate. Once BimodalLogic's proof-producing check_certificate lands -- whose success path applies WitnessFamily.joint_countermodel to a decided hypothesis, constructing the paper-countermodel existence term rather than printing a verdict -- consume that mode here: extend the wire's output contract to carry it, and record in the presentation path that the Python re-checker has become a fast pre-filter rather than part of the trust base. Second, parse-echo verification: the Lean side parses the exported JSON, so a parser defect could mean the verified side certifies a different certificate than the one exported. Pair with BimodalLogic's canonical-printer and parse-after-print round-trip theorem by having the Lean side echo back what it parsed and comparing it bytewise against what this repository sent, treating any mismatch as a protocol error rather than a rejection. Preserve the existing output contract's discipline throughout: exactly one line, never a validity claim, and the error-versus-rejected distinction (error covers input failing the protocol, rejected covers input that parses but fails a condition). BLOCKED on the two BimodalLogic counterpart tasks (proof-producing check_certificate, and the canonical wire round-trip theorem); the wire contract is an export contract per section 6.1, so renaming or extending any of back, mid, fwd, bx, lassos or target is a breaking change requiring coordination with the producing side, not a local refactor.

---

### 196. Discharge s4 translation bridge
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: semantics
- **Dependencies**: Task 193, Task 194
- **Research**: [196_discharge_s4_translation_bridge/reports/01_discharge-s4-translation-bridge.md]
- **Plan**: [196_discharge_s4_translation_bridge/plans/01_discharge-s4-translation-bridge.md]
- **Summary**: [196_discharge_s4_translation_bridge/summaries/02_discharge-s4-translation-bridge-summary.md]

**Description**: Discharge obligation S4, the Sentence-to-Formula translation bridge, which ADEQUACY.md section 6.3 records as covered by no Lean theorem. S4 is the weakest joint in the soundness direction this repository already asserts: the certificate's (C4) target condition is decided against target.premises and target.conclusions, so if the translation is wrong, every downstream check rigorously certifies a countermodel to a different argument than the user asked about. The round-trip against lake exe check_certificate cannot detect this, because both sides consume the same already-translated Formula. Two hazards are named explicitly: the translation must eliminate all defined operators (negation, conjunction, disjunction, the derived tense operators, \next, \prev) into the six primitives, and it must swap Until/Since arguments, since UntilOperator.true_at is event-first while Lean's untl is guard-first -- a hazard purely internal to the translation code, invisible on the wire because the wire's named event/guard fields are order-free. Note that oracle/bimodal_logic/ground_truth.py's brute-force adjudicator covers only the tense half (five primitive tags, no box case), so it cannot discharge the box half on its own; the box half must be covered explicitly. Prefer, if feasible, relocating the elimination into verified code (put the Sentence on the wire and let the verified side eliminate) so the obligation is deleted rather than tested; otherwise implement section 6.3's property test over small generated sentences, comparing the theory's own truth evaluation against a direct evaluator for the translated formula at every point of a small hand-built Z-model, and verify against the Lean-side translation once its counterpart lands in BimodalLogic. Record which route was taken and why.

---

### 195. Research encoder spec proof routes
- **Status**: [COMPLETED]
- **Task Type**: formal
- **Topic**: architecture
- **Dependencies**: Task 192
- **Research**: [195_research_encoder_spec_proof_routes/reports/01_encoder-spec-proof-routes.md]
- **Plan**: [195_research_encoder_spec_proof_routes/plans/01_encoder-spec-proof-routes.md]
- **Summary**: [195_research_encoder_spec_proof_routes/summaries/01_encoder-spec-proof-routes-summary.md]

**Description**: Research and recommend a route to actually prove, rather than test, that the bimodal certificate encoder emits exactly the conjunction of conditions (C1)-(C4) over windows at least as wide as ADEQUACY.md section 5.2's. The mathematical content is already machine-checked and sorry-free; the open obligation is the code-to-specification bridge that section 5.3 argues a proof does not discharge for a specific piece of Python. Evaluate at least three routes and recommend one with a cost estimate: (a) a verified generator, emitting the constraint set from Lean-verified code or extracting the encoder from it; (b) translation validation, or a proof-producing encoder that certifies per run that its emitted clause set matches a verified specification -- the only route that establishes the property for the code that actually runs; and (c) a second independent implementation plus differential, which is what the standing A2-triangle test already is, assessed honestly as evidence rather than proof. Weigh each against the proportionality constraint the adequacy document itself establishes: A3 is vacuous until A1 supplies f, and A0 caps the strongest honest claim at "Z-time valid" permanently, so a fully discharged A2 hardens section 7.4's never-report-validity rule, which already has a runtime fail-fast guard, rather than upgrading the headline result. Deliver a report with a recommendation and a staged path, not an implementation.
ADDENDUM, two findings that constrain this research and must be accounted for rather than rediscovered. First, route (b)/(c) must not re-propose a verified bounded enumerator: BimodalLogic's compression task already scopes one as its item 2 -- the formula-indexed candidate list over the compression bounds plus Decidable ValidZTime by decidable_of_iff from "no candidate is accepted", following BiLasso/Assembly.lean's validZTime_iff_checkFamily shape. Since the four Decidable instances and enumeration completeness are already landed there, a verified enumerator deciding bounded absence directly is the cheaper route to rigor than either proving this repository's encoder correct or reconstructing Z3 unsat proofs, and it does not require trusting Z3 at all. Evaluate it as an existing external deliverable to consume, and weigh the remaining local A2 work against it. Second, ADEQUACY.md section 7.1's condition (iii) for a genuine A1 reduction -- a demonstration that this repository's search enumerates the same family space at a segment length at least that bound -- was recorded as unbuildable until a certificate export and an independent re-checker existed here at all. Section 6 now supplies both, so that condition is satisfiable today; the research should say what demonstrating it would concretely require of this repository.

---

### 194. Close a2 selector and window drift gaps
- **Status**: [COMPLETED]
- **Task Type**: z3
- **Topic**: semantics
- **Dependencies**: None
- **Research**: [194_close_a2_selector_and_window_drift_gaps/reports/01_selector-conservativity-window-drift.md]
- **Plan**: [194_close_a2_selector_and_window_drift_gaps/plans/01_selector-conservativity-window-drift.md]
- **Summary**: [194_close_a2_selector_and_window_drift_gaps/summaries/01_selector-conservativity-window-drift-summary.md]

**Description**: Close the two residual encoder-versus-specification gaps in the A2 encoding-completeness argument that are small enough to discharge directly. First, one-hot selector conservativity: decision D5 makes the target position a one-hot sel selector rather than a fixed origin, which is structure absent from conditions (C1)-(C4) entirely, so ADEQUACY.md section 7.3's "the Z3 constraint set is exactly the conjunction of (C1)-(C4)" does not cover it. Establish and record that the selector is conservative -- the encoding is SAT with some sel[t] exactly when a certificate satisfying (C1)-(C4) exists with target time t -- and exercise it directly in a test, so the selector cannot itself be the over-constraint that a future encoding incompleteness gets wrongly blamed on. Second, window drift: WitnessRegistry.target_window() is independently defined rather than imported, unlike _coherence_window, _box_window, _scan_forward_bound and _scan_backward_bound, which witness_constraints.py takes directly from certificate.py. certificate.py's own comment records the split as deliberate, since target_window is also reused for the one-hot selector and both are simple one-line formulas, but it remains the one place encoder and re-checker can silently diverge on a window. Either share a single definition or assert that the two formulas agree across the configured range of nb, nm and nf. Verify against the full bimodal suite and the four-theory gate; no behavioral change is intended.

---

### 193. Extend a2 triangle grid to nb nf 2
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None
- **Research**: [193_extend_a2_triangle_grid_to_nb_nf_2/reports/01_extend-a2-triangle-grid.md]
- **Plan**: [193_extend_a2_triangle_grid_to_nb_nf_2/plans/01_extend-a2-triangle-grid.md]
- **Summary**: [193_extend_a2_triangle_grid_to_nb_nf_2/summaries/01_extend-a2-triangle-grid-summary.md]

**Description**: Extend the A2-triangle encoding-completeness test's exhaustive grid beyond back=mid=fwd=1 to cover nb=nf=2. tests/integration/test_certificate_a2_triangle.py currently enumerates exhaustively only at back=mid=fwd=1, per ADEQUACY.md section 7.3's stated test, and that regime is provably blind to the one A2 violation known to have actually occurred: witness_constraints.py's module docstring records that local coherence was once generated over the narrow WitnessRegistry.target_window() instead of the proved wide _coherence_window, and that the counterexample requires nb=2, since slot back[1] recurs at every odd-magnitude position. The defect is therefore invisible at nb=1, which makes raising the grid the highest-value strengthening available short of a proof. Measure before committing to unconditional execution: the single-box closure already reaches 1,572,864 candidates at nb=nf=1 and roughly 11.5 seconds of recheck time, so compute the nb=nf=2 candidate count first and tier or mark the test accordingly (the slow marker is already registered) rather than assuming it is affordable. Keep the existing three closures' coverage intact, and keep Tier 2's clean-skip discipline when no BimodalLogic checkout is present. Report any genuine three-way disagreement as a finding: diagnosing the encoder is out of scope for this task.

---

### 192. A2 proof vs implementation gap report
- **Status**: [COMPLETED]
- **Task Type**: markdown
- **Topic**: documentation
- **Dependencies**: None
- **Research**: [192_a2_proof_vs_implementation_gap_report/reports/01_a2-proof-implementation-gap.md]
- **Plan**: [192_a2_proof_vs_implementation_gap_report/plans/01_a2-gap-companion-document.md]
- **Summary**: [192_a2_proof_vs_implementation_gap_report/summaries/01_a2-gap-companion-document-summary.md]

**Description**: Write a companion report in code/src/model_checker/theory_lib/bimodal/docs/ explaining the proof-versus-implementation gap in the A2 encoding-completeness argument: what is missing is not mathematics but a proof that the running Python emits what the mathematics specifies. Place it alongside ADEQUACY.md, whose sections 5.2, 5.3 and 7.3 it extends, and cross-reference it from ADEQUACY.md section 7.3. The core thesis is section 5.3's own claim about the re-checker, transferred to the encoder: that a specific piece of Python correctly implements the finite-window reduction it is credited with "is not something a proof discharges". The report must (a) separate what IS machine-checked -- the window collapses coherent_iff_window, fulfil_iff_window, mem_all_iff_window, scan_forward and scan_backward, sorry-free, plus the fact that witness_constraints.py imports _coherence_window, _box_window, _scan_forward_bound and _scan_backward_bound directly from certificate.py so encoder and re-checker cannot drift on those bounds -- from what is not; (b) enumerate the full emitted-constraint surface that "no extra constraint" quantifies over, which is wider than the four condition emitters: finalize_certificate()'s in-place writes to frame_constraints (which ModelConstraints reads by reference), premise_behavior and conclusion_behavior per formula, and proposition_constraints; (c) name the one-hot sel selector (decision D5) as structure genuinely absent from conditions (C1)-(C4), so it needs its own conservativity argument rather than being covered by them; (d) record WitnessRegistry.target_window() as the one remaining independently-defined window, deliberately not shared with certificate.py's _box_window; (e) present the historical local-coherence defect recorded in witness_constraints.py's module docstring -- the encoder generated over the narrow target_window instead of the proved wide window, the counterexample requires nb=2, and it was caught by section 6.2's fail-fast differential rather than by any proof -- as concrete evidence that this defect class is real and that the standing A2-triangle test at back=mid=fwd=1 cannot see it; and (f) state honestly what a bounded exhaustive test does and does not establish. Documentation only: no source or test changes.
ADDENDUM. The report must also state the trust-base consequence that follows from obligation S3, since it is what makes the A2 gap a completeness matter rather than a soundness one. Because (C1)-(C4) are decidable, S3 is discharged by deciding the antecedent on every reported certificate -- twice and independently, per ADEQUACY.md section 6.2 -- rather than by proving the producer correct. Consequently the Z3 encoder, the decoder, and Z3 itself are NOT in the soundness trust base: an encoder defect can only over-constrain (costing completeness, reported as no certificate found within bounds, which was never a validity claim) or produce something that fails the four conditions (a loud rejection via the fail-fast step). It cannot manufacture a false countermodel report. The report should state this explicitly and draw the corollary that the soundness trust base is Lean's kernel, the S2 transcription audit, the re-checker implementation, and the translation (S4) -- which is why S4, not A2, is the weakest joint in the direction already asserted. It should also record that a "countermodel" verdict is not a kernel-checked proof for that particular certificate, only that the four Decidable instances returned true on the family rebuilt from the wire.
SCOPE NOTE (overlap resolved). TRUST_PIPELINE.md has since been written in the same directory, and it already states the trust-base corollary this task's ADDENDUM above asked for, names the emitted-constraint surface, the one-hot selector and the independently-defined target window, and recounts the historical narrow-window defect. This task remains distinct and worth doing, but its scope is now the DEEP TREATMENT rather than the summary: the full category argument that a claim about what a specific piece of Python emits is not the kind of claim a proof about mathematics discharges, the complete enumeration of the emitted surface with each emitter's clause shape, and the per-route analysis of what closing the gap would actually require. Build on TRUST_PIPELINE.md and cross-reference it; do not restate its summary-level content.
