---
next_project_number: 187
---

# TODO

## Task Order

*Updated 2026-09-24. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 184,186 | -- | semantics |
| 2 | 154,176,183 | 184 | semantics, test-reliability |
| 3 | 172,178 | 176 | test-reliability |

**Grouped by Topic** (indented = depends on parent):

### Semantics

184 [NOT STARTED] — Redesign the bimodal theory around witness-family certificates fo
  └─ 154 [BLOCKED] — THE PAYOFF, and the one task in this group where OVER-CLAIMING is
186 [RESEARCHED] — Review the counterfactual semantics of the Logos manual's dynamic

### Test Reliability

172 [BLOCKED] — Three tests in oracle/bimodal_logic/tests/test_soundness_regressi
176 [BLOCKED] — TestShiftClosure::test_shift_closure_on_extracted_worlds_m3 at or
  └─ 172 [BLOCKED] — Three tests in oracle/bimodal_logic/tests/test_soundness_regressi (see above)
  └─ 178 [BLOCKED] — Fix the 4-6x solver-cost regression that commit f9cc081e introduc
183 [BLOCKED] — Discriminate axiom-driven solver cost from host contention as the

## Tasks

### 186. Review manual counterfactual semantics for uniform clauses
- **Effort**: large
- **Status**: [RESEARCHED]
- **Task Type**: formal:logic
- **Topic**: semantics
- **Dependencies**: None
- **Research**: [186_review_manual_counterfactual_semantics_for_uniform_clauses/reports/01_family-level-settled-verification.md]

**Description**: Review the counterfactual semantics of the Logos manual's dynamics chapter (~/Projects/Logos/Theory/typst/manual/chapters/03-dynamics.typ) and identify whether further improvements are available, with the aim of a clean, systematic, and UNIFORM hyperintensional semantics for counterfactual conditionals -- one whose clauses place no restriction on which well-formed sentences may be embedded or interpreted.

AIM, STATED AS THE STANDARD THE ANSWER MUST MEET. The target is not another candidate clause defended in isolation. It is a semantics in which every operator in the language receives its verifier and falsifier conditions by ONE stated principle, with the counterfactual no longer a special case and with no syntactic antecedent restriction. Uniformity, generality, and elegance are the criteria; the deliverable is the deepest systematic lesson the manual's own machinery will support.

PROVENANCE. Four prior reports establish the problem and the state of the answer. Read all four before starting.
- ~/Projects/Logos/Theory/specs/406_counterfactual_null_state_verification/reports/01_counterfactual-null-state-verification.md (round 1: three context-relative readings; Reading B recommended then REJECTED by the user for reading the evaluation history)
- ~/Projects/Logos/Theory/specs/406_counterfactual_null_state_verification/reports/02_context-free-counterfactual-verifiers.md (round 2: refutes the imposition-local clause on a certified 8-atom frame; argues in its F4 that no context-free sound clause can be hyperintensional except by fiat; recommends Reading W, world-history verifiers)
- specs/185_design_and_test_hyperintensional_counterfactual_verifiers/reports/01_exact-imposition-verifier-clauses.md (refutes F4 by construction; recommends ILMC)
- specs/185_design_and_test_hyperintensional_counterfactual_verifiers/reports/02_constitutive-patterns-uniform-clauses.md (the uniformity analysis this task extends; its recommendations R1-R6 are the starting hypotheses)

WHAT IS ALREADY ESTABLISHED, AND IS NOT TO BE RE-DERIVED. These are settled results in the untensed ModelChecker fragment, each with pinned tests or saved baselines. Carry them in; do not re-litigate them.
(1) ILMC. A state s verifies A []-> B iff s is a fusion of parthood-minimal states t such that the counterfactual's own truth clause holds with t in the world slot (call this I(t)) and at every world containing t (call this L(t)). Falsifiers dually. This is context-free, sound, sufficient, exclusive, exhaustive and fusion-closed on every population measured, and hyperintensional on possible states at four atoms (Z3-confirmed at N=4). It refutes report 02's F4 impossibility argument.
(2) THE SETTLER RECIPE, which is the generalization to test against the manual. V(phi) = closure(min(I_phi AND L_phi)), where I_phi is the operator's own truth clause relativized to the candidate state and L_phi is its settling condition. When the truth clause never reads the world slot -- as for propositional identity, ground, essence, relevance, and necessity -- every state settles it, the unique minimal state is the null state, and the recipe RETURNS the manual's null-state convention as a computed case rather than a stipulation.
(3) CONSERVATIVITY OVER NECESSITY. Under ILMC, box A and (top []-> A) express the same proposition (Z3 theorem at N=3); under the status quo clause they do not (countermodel). Since the manual DEFINES box A as top []-> A, this is a uniformity defect the recipe repairs. Evidence: specs/185_.../baselines/11_uniformity-experiments.py and its saved output.
(4) THE TWO-MECHANISM STRUCTURE. Content-building operators (atoms, negation, conjunction, disjunction) take exact verifiers as given and combine them; world-quantifying operators have no given exact verifiers and must manufacture them from their truth conditions. The recipe is the canonical manufacturing procedure for the second family and demonstrably cannot replace the first (applied to conjunction it discards genuine non-minimal exact verifiers).
(5) THE MINIMALITY STEP is best understood as Fine's whole-relevance requirement applied to a set in which relevance is not otherwise guaranteed -- not as an ad hoc extremal condition.
(6) PROPOSITIONAL IDENTITY FORCES CONTEXT-FREEDOM. The identity operator threads the evaluation point into both operands' verifier clauses, so a context-dependent operand clause breaks all four constitutive relations at once. This is the structural reason the governing criterion is right.

THE QUESTIONS THIS TASK MUST ANSWER, against the manual rather than against the untensed fragment.
(a) Does the settler recipe state cleanly at the manual's FAMILY level, over anchored families and world-histories, as it does over states? Identify precisely what plays the role of I (the truth clause relativized to the candidate family) and of L (settling: every world-history extending the family makes the sentence true), and whether parthood-minimality and fusion closure are available there.
(b) Does the recipe reproduce the manual's existing null-state convention for propositional identity as a derived case, exactly as it does in the untensed fragment? If it does, the manual's convention stops being a separate stipulation and the chapter can state one principle.
(c) Does it lift the DT antecedent restriction in the well-formedness definition, so that counterfactuals, necessity, possibility, might-counterfactuals and stability become admissible antecedents with no syntactic side condition? This is the "no restrictions on the well-formed sentences that can be embedded" half of the aim.
(d) Does the strict-conditional collapse recur? Report 02's Reading W collapses every nested counterfactual to a strict conditional; ILMC escapes this in the untensed fragment precisely BECAUSE of the minimality step. Determine whether the same escape is available at the family level, and if not, exactly what blocks it.
(e) What happens to the proof-theory chapter's open items (the identity rule at counterfactual antecedents, the modus-ponens side condition, the transitivity-style rule, and the corresponding soundness qualification) under the recipe? Prior rounds each moved these; say what this one does, and record honestly which do NOT become unconditional and why.
(f) Report 02's F4 argument is refuted in the untensed fragment. State whether its family-level analogue survives, since the manual's own text may still rest on it.

SCOPE. Research only: read the manual, the prior reports, and the ModelChecker implementation as the executable check. Produce a report. Do NOT edit the manual, the Lean development, or the ModelChecker theory in this task -- if the review recommends changes, they are the subject of a following task. The manual and Lean tree are in a separate repository and are read-only here.

DELIVERABLE. A report that either (i) states one principle from which every operator's verifier clause in the manual follows, with the counterfactual as an instance and the null-state convention as a derived case, and identifies exactly what in the manual must change to adopt it; or (ii) identifies the specific obstruction at the family level that makes such a principle unavailable, with the same precision the prior reports applied to their refutations. Where the evidence does not decide, say so plainly and name the test that would.

---

### 185. Design and test hyperintensional counterfactual verifiers
- **Effort**: large
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: semantics
- **Dependencies**: None
- **Research**: [185_design_and_test_hyperintensional_counterfactual_verifiers/reports/01_exact-imposition-verifier-clauses.md]
- **Plan**: [185_design_and_test_hyperintensional_counterfactual_verifiers/plans/01_ilmc-settled-imposition-verifiers.md]
- **Summary**: [185_design_and_test_hyperintensional_counterfactual_verifiers/summaries/02_ilmc-settled-imposition-verifiers-summary.md]

**Description**: Design and test the hyperintensional semantics for counterfactual conditionals in the logos theory: specifically, which states verify and which falsify A []-> B. Define new counterfactual operators as competing alternatives and discriminate between them by exploring their logic over small models, so the choice rests on model-based evidence rather than on argument alone.

PROVENANCE. Two research rounds in the Logos manual repository set up the problem and refuted the first two candidate answers. Read both before starting:
- ~/Projects/Logos/Theory/specs/406_counterfactual_null_state_verification/reports/01_counterfactual-null-state-verification.md
- ~/Projects/Logos/Theory/specs/406_counterfactual_null_state_verification/reports/02_context-free-counterfactual-verifiers.md

GOVERNING CRITERION. A sentence must determine ONE proposition <V,F> as a function of the model alone. A clause whose verifier set depends on the point of evaluation without recording that dependence is rejected, because the same counterfactual would then express different propositions in different contexts. (In the tensed manual setting, dependence on the anchor and index is not context-dependence in the objectionable sense; dependence on the evaluation world or history is.)

BINDING MECHANISM CONSTRAINT. Every candidate MUST be built out of the SAME basic mechanics as the counterfactual semantics already implemented in code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py: the verifiers of the antecedent, semantics.max_compatible_part, semantics.is_alternative (imposition of an antecedent-verifier on a state), and the verifier/falsifier semantics of the consequent. The truth clause is FIXED: true_at and false_at are shared verbatim by every candidate and are not up for revision. THE ONLY QUESTION UNDER EXPLORATION IS WHICH STATES VERIFY AND WHICH FALSIFY A []-> B.

DISQUALIFICATION RULE. A candidate is disqualified if its verifier set is defined as a function of the TRUTH-SET { w : A []-> B is true at w } instead of being built out of the imposition machinery. This disqualifies, as candidates in their own right: fusion closures of the true worlds; settler sets { s : every world state containing s makes it true }; and the parthood-minimal or fusion-closed variants of settler sets. Those are set-theoretic operations on truth values, not semantic clauses -- which is exactly why they cannot be hyperintensional except by fiat. They may appear ONLY as comparison baselines in the measurement tables, never as recommendation candidates, and the recommendation may not name one.

THE DESIGN SPACE THAT REMAINS. Inside the fixed machinery the genuine degrees of freedom are:
(a) What role the candidate verifier s plays -- the base on which antecedent-verifiers are imposed (so the alternatives are alternatives TO s rather than to the evaluation world), a part of the evaluation world, or a part of the outcome world.
(b) Whether the consequent must merely be TRUE at each alternative, or must be VERIFIED there by a designated part. The second is what makes an exact, truthmaker-shaped clause possible at all, and the existing clause never considers it.
(c) How the pieces compose -- in particular whether s is a FUSION of consequent-verifiers drawn one from each relevant alternative, possibly fused with the antecedent-compatible part of the evaluation world that survives the imposition. This family is the natural route to verifiers that lie properly below world states while remaining hyperintensional, and it was absent from the first planning round. Develop it.

THE ADDITIONAL DESIDERATUM DRIVING THIS TASK. The clause should deliver some POSSIBLE verifiers and falsifiers that lie properly below world states, not only total states. Report 02's recommendation (Reading W: verifiers are the fusion closure of the world states at which the counterfactual is true) satisfies context-freedom, but its every possible verifier is a whole world state and nothing proper verifies. That is the specific respect in which report 02's recommendation is judged unsatisfying, and addressing it is the main point of this exploration.

WHY MODELCHECKER IS THE RIGHT TEST BED. The logos theory here is the untensed fragment, so the manual's world-histories collapse to world states and every candidate clause can be stated directly over states. Small finite models can be enumerated and the resulting logic measured -- which theorems survive, which countermodels appear -- instead of argued.

CURRENT STATE, VERIFIED ON DISK. code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py:74-90 defines
  extended_verify(state, ...)  := (state == eval_point["world"]) AND true_at(...)
  extended_falsify(state, ...) := (state == eval_point["world"]) AND false_at(...)
so the verifier set is {w} at evaluation world w and varies with the evaluation point. This is precisely the context-dependent clause the governing criterion rejects -- report 01's "Reading B", in Python. find_verifiers_and_falsifiers (:92) builds the sets per world the same way, and MightCounterfactualOperator (:182) mirrors it.

CANDIDATES TO IMPLEMENT AND DISCRIMINATE. Implement each as a separate operator, sharing true_at/false_at verbatim with the existing operator and differing only in extended_verify / extended_falsify / find_verifiers_and_falsifiers, so they can be run side by side on identical models.
(1) Status quo (context-dependent, state == eval world). Baseline; expected to fail the governing criterion, included to measure what its logic actually is.
(2) Reading I, imposition-local -- the intuitive proposal, and the one candidate carried over from the first round because it does respect the mechanism constraint: s verifies A []-> B iff for every verifier a of A and every r among the maximal a-compatible parts of s, every world containing a fused with r makes B true. Report 02 refutes this analytically on a finite 8-atom, 4-world frame: the verifier set is not closed under fusion; a verifier and a falsifier are compatible, so exclusivity fails; a verifier is part of a world at which the counterfactual is false, so the truth bridge gluts; and identity fails at nested antecedents. FIRST CONCRETE DELIVERABLE: reproduce that countermodel mechanically here and either confirm or overturn it. The frame is given explicitly in report 02, finding F3.1, and is small enough to encode directly.
(3) EXACT IMPOSITION CANDIDATES -- the family the exploration exists to develop, per (b) and (c) above. Require the consequent to be VERIFIED rather than merely true at the alternatives, and let s be composed from those consequent-verifiers. The obvious starting point to state precisely, implement, and measure: s verifies A []-> B iff s is a fusion of states { b_u }, one drawn from the B-verifiers at each world u that is an alternative to the evaluation world under some verifier of A. Variants to state and discriminate: whether the alternatives are taken to s or to the evaluation world; whether the antecedent-compatible remainder r is fused into s; whether the choice is universal over alternatives or existential; and the polarity-dual falsifier clause in each case. These are hypotheses to be made precise and tested, not a finished clause -- deriving the right member of this family is the core work.
(4) Any further candidate the work suggests, subject to the mechanism constraint. The aim is the most naturally articulated clause with the best logic, not a defence of any candidate above.
(5) DISQUALIFIED BASELINES, measured but never recommended: fusion closure of the true worlds (report 02's "Reading W"), settlers, and minimal settlers. Implement them only to populate the comparison columns of the measurement tables and to show concretely what the mechanism constraint buys.

A THEORETICAL CONSTRAINT TO BE TESTED, NOT ASSUMED. Report 02 argues that any context-free clause that is sound (a verifier contained in a world makes the counterfactual true there) and sufficient (every world where it is true contains a verifier) must have verifiers that are settlers; and since settler-hood is a function of the truth-set, no such clause is hyperintensional except by fiat. The exact imposition candidates in (3) are the direct challenge to that argument: they are built from the antecedent's and the consequent's verifiers, so they are hyperintensional by construction, and the open question is whether any of them is also sound and sufficient. If one is, that refutes report 02's F4 argument and is the single most valuable outcome available here. If none is, then determining exactly which of soundness and sufficiency the family must give up -- and what the best available trade is -- is the deliverable instead. Treat F4 as a live question, not a settled result.

MEASUREMENTS THAT DISCRIMINATE. For each candidate, over small models, determine at minimum:
- Closure of V and F under fusion. Report 02 notes that some verifiers will be impossible states; impossible states are part of no world state and so are invisible to the truth bridge. Confirm that harmlessness per candidate rather than assuming it -- it holds for some candidates and demonstrably fails for others.
- Exclusivity and exhaustivity: no possible state both verifies and falsifies; every world state does one or the other.
- Whether a verifier can be part of a world at which the counterfactual is false (bridge soundness).
- The status of the counterfactual axioms and rules at NESTED counterfactual antecedents, which is where the candidates come apart: identity, (A []-> B) []-> (A []-> B); the modus-ponens-style rule; antecedent strengthening with conjunction; and whether X []-> C collapses to the strict conditional [](X -> C).
- Whether distinct counterfactuals sharing a truth-set receive distinct propositions (hyperintensionality at nested position).
- Regression: re-run the existing logos counterfactual examples per candidate and record which currently-valid theorems break and which currently-invalid ones become valid. Baseline is code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py and tests/test_counterfactual_examples.py.

SCOPE. Exploration and evidence-gathering. Add new operators alongside the existing one; this is not a destructive replacement. Do not delete or rewrite the current counterfactual operator until a successor is chosen on evidence. Work on a dedicated branch.

DELIVERABLE. A recommendation naming one clause, the model-based evidence discriminating it from the others, and an explicit statement of what it concedes. If the evidence does not discriminate between two candidates, say so plainly and name the further test that would.

---

### 184. Refactor bimodal theory tests green and paper lean aligned
- **Effort**: large
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: semantics
- **Dependencies**: None

**Description**: Redesign the bimodal theory around witness-family certificates for discrete (Z) time, replacing the current window-and-abundance Z3 encoding rather than repairing it. The authority for this task is the research report at specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/reports/01_finite-certificate-redesign.md; read it in full before researching, planning, or implementing anything here.

WHY REPLACE RATHER THAN REPAIR. The current encoding is not a model of the paper's semantics. It evaluates tense operators over a bounded window (-M, M) with acknowledged boundary vacuity, so G A is vacuously true at the last window time; it lets Box range over a finite set of window histories rather than over H_F; and it substitutes abundance and shift-closure constraints for the histories the paper's semantics actually contains. The decisive evidence is that it refutes the paper's own bimodal axiom MF (Box A -> Box G A), finding a countermodel at N=1, M=2, which is why MF_MODAL_FUTURE_TH is excluded from the suite. The perpetuity theorems are valid only under M=3 shift closure with 30 s budgets, task_restriction is disabled for solver cost so SAT results live in a larger frame class than the grounded one, and every open test-reliability item chases rlimit growth from the Skolemized Seriality and Interpolation axioms. These are properties of the design, not bugs in it.

WHY A CERTIFICATE AND NOT A FINITE FRAME. Over Z-time a finite task frame is just a finite bi-serial digraph: compositionality makes every duration relation a power of the unit step, Limit makes the zero-duration relation identity, and Saturation is automatic for finite carriers. But finite digraphs under all-paths semantics are incomplete for Z-time validity, and this is machine-checked in the Lean development (Probe476.fmp_false). Box quantifies over all bi-infinite paths, so a pumped cycle in any finite digraph is itself a history; countermodels therefore need infinitely many world states in general. The finite object to search for is a witness family, not a frame.

SCOPE: DISCRETE TIME ONLY. This task covers Z-time. Dense and continuous time are explicitly future work, and the reason is recorded rather than assumed: over a dense Archimedean order a finite carrier forces the cones to stabilize, Limit then collapses every small-duration fibre to a singleton, and compositionality propagates identity to every duration, so the frame is static and every possible world constant. Dense-time countermodel search needs finite presentations of infinite carriers (mosaic- or region-style), which is out of scope. The stability modal is also out of scope.

THE SEARCHED OBJECT. Fix premises and conclusions and let C be the subformula closure of their union. A certificate is: a box guess assigning a Boolean to each boxed subformula in C; a main lasso, plus one witness lasso for each boxed subformula guessed false (so at most one more than the number of boxes, and lassos may be shared); each lasso given as (back, mid, fwd) segments with a label, a subset of C, at each position, positions left of the origin repeating back and positions at or after the mid length repeating fwd. Four conditions: (1) local coherence at every position, matching the Lean LocalCoherent predicate, with atoms free so that the valuation is the atom part of the label; (2) fulfilment, so every Until obligation has a later witness with the guard holding in between, and symmetrically for Since, decided within a bounded window on a periodic annotation; (3) box faithfulness, so a box guessed true has its argument in every label of every lasso and a box guessed false has some position of some lasso omitting it; (4) the target condition, some position of the main lasso carrying every premise and no conclusion.

THE CERTIFIED MODEL. The certificate denotes the ShiftSet whose carrier is the disjoint union of the lassos' (index, time) points, with the shift action as the task relation and an atom true at (i, t) exactly when it is in that label. Seriality, interpolation, Saturation and Limit are discharged by that construction; its possible worlds are exactly the orbits, so Box ranges over exactly the certified histories. The model has infinitely many world states and infinite durations, which is the target property. Soundness is true on paper and is the theorem BimodalLogic task 623 is proving; ModelChecker does not depend on that proof for its own soundness. Completeness (every Z-refutable inference has a certificate within length bounds) is the compression lemma of 623 and determines only whether "no certificate found within bounds" carries information. ModelChecker must therefore never report validity; that remains the tableau's and the proof system's job.

CONSEQUENCES FOR THE TWO ORIGINAL AIMS. Both are retained, but as consequences of replacing the semantic core, not as repairs to it.

(1) TESTS GREEN AND FAST. The new encoding is quantifier-free: the variables are Booleans for label membership plus the box guess, with segment lengths fixed per iteration. There is no ForAll, no MBQI, no E-matching pattern, and no rlimit tuning, so the original speed aim follows from the redesign and is not pursued as separate solver work. N and M disappear as settings and are replaced by maximum segment lengths for back, mid and fwd plus an optional cap on witness count, defaults small and raised on demand. Iteration becomes blocking clauses on labels. This is what ends the holding pattern in which bimodal was given in-development status and made CI non-gating.

(2) SEMANTIC ALIGNMENT. The Python semantics come into line with the paper and the Lean formalization by construction, because the certificate conditions are the Lean predicates and the certified model is the Lean ShiftSet. Where the three sources disagree the disagreement must still be identified and resolved deliberately with the chosen source of truth recorded, not silently patched on one side.

WHAT IS GIVEN UP. Certified frames are deterministic, with no branching at a shared state. For the current language this is without loss, by the equivalence of Z-frame validity with validity over recurrence-free Z-frames. Branching witness families would be needed for the stability modal, which is open research in the Lean development and must not be promised here. Design the certificate datatype so that lassos may later share states, but do not implement sharing now.

DELIVERABLES.
- A new semantic/ core implementing the certificate encoding and the certified ShiftSet model.
- Operators rewritten as label-constraint generators over positions; Box's generator introduces the guess variable and, when the guess is false, requests a witness lasso. The currently inert WitnessRegistry and WitnessConstraintGenerator are the natural home for this and should be rewritten rather than deleted.
- Model structure and printing: each history shown as (back)^w | mid | (fwd)^w over atom valuations with the evaluation position marked, a table of boxed subformulas with their guessed values, and for each false box its witness history and position. World states are (history, time) points and the task relation is the shift. The time-shift-relation and interval displays are removed.
- iterate.py rewritten with difference constraints on labels and guesses, plus isomorphism rejection modulo rotation of periodic segments and renaming of witness lassos.
- A pure-Python re-checker of the four certificate conditions, independent of the Z3 model object, run on every found model in tests.
- Examples migrated, with MF_MODAL_FUTURE_TH, BM_TH_1 and BM_TH_2 restored along with the rest of the nine currently excluded examples (TN_CM_1, TN_CM_2, BM_CM_3, MD_TH_2, BM_TH_1, BM_TH_2, MF_MODAL_FUTURE_TH, BX7_LINEAR_U_TH, BX7P_LINEAR_S_TH). Every expectation is to be checked against the paper's axioms rather than carried over.
- Theory docs rewritten, retiring the frame-axiom ledger and the duration-guard gap note.
- The development marker removed, together with every "and not development" gating clause, which is the exit condition the CI comments already name. The oracle provider in oracle/bimodal_logic/ is rewritten against the new semantics, its abundance and shift-closure soundness tests are deleted with the machinery they test, and the known-conclusive manifest is regenerated. The oracle's own soundness core and unconditional-gating property remain out of scope for modification.

SEQUENCING. This task was previously the refactor-first gate holding back five dependent bimodal tasks (154, 172, 176, 178, 183). Those tasks are being abandoned in the same operation that creates this revision, because each is a point-fix against machinery this redesign deletes: extension-certified search assumes the window-and-abundance design and its polarity split, the contention-flaky soundness tests belong to the encoding being removed, the M=3 shift-closure regression concerns a constraint that will no longer exist, the frame-axiom solver cost concerns Skolemized Seriality and Interpolation which over Z are discharged by bi-seriality alone, and the gating-shortfall discrimination measures the cost of the old encoding against a manifest that will be regenerated. There are consequently no dependents waiting on this task, and it can be implemented immediately: its soundness argument holds on paper and its certificate format is fixed by the Lean annotation type, so the later formal guarantee will not change the format.

FOLLOW-ON WORK, NOT IN SCOPE HERE. The report proposes two successor tasks. First, wiring the Lean tableau bridge as a differential oracle at frame class Z-time, replacing the current Z3-against-Z3 self-consistency scan and harness comparison, with ground_truth.py kept as a tie-breaker for the temporal-only fragment. Second, JSON certificate export in the Lean annotation shape plus a round-trip test through a Lean re-verification executable. A fixed-frame model-checking mode, checking a given finite digraph, is a separate optional feature and is also out of scope.

STARTING POINTS. The research report named above is the primary reference. Then: code/src/model_checker/theory_lib/bimodal/ (semantic/, operators.py, iterate.py, examples.py, tests/); oracle/bimodal_logic/; the paper at ~/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex (app:TaskSemantics, thm:extension, def:BL-semantics, lem:history-time-shift-preservation); and ~/Projects/BimodalLogic/FormalSystem/ with its specs/, in particular Semantics/IntNormalForm.lean, Semantics/ShiftSet.lean, Semantics/Extension/PeriodicExtension.lean, and Metalogic/Decidability/BiLasso/.

---

### 183. Discriminate gating shortfall axiom vs contention
- **Effort**: 2-4 hours
- **Status**: [BLOCKED]
- **Task Type**: python
- **Topic**: test-reliability
- **Dependencies**: Task 184

**Description**: Discriminate axiom-driven solver cost from host contention as the cause of the gating conclusive-population shortfall for TestGatingConclusiveScan::test_known_conclusive_population_self_consistent in oracle/bimodal_logic/tests/test_cross_oracle_differential.py. Consolidates report items 0a, 1, and 2 into one task because they resolve on the same next observations of the same test and would otherwise block on each other.

BACKGROUND. Six consecutive unstable-watch runs (2026-08-27 -> 2026-09-01) all checked out the stale origin/master commit 98d3ad8d (frozen roughly five days): 33091941820 (98/103 conclusive, 5 timeouts, 761.61s), 33193518591 (96/103, 7, 824.89s), 33250263772 (98/103, 5, 749.10s), 33306220265 (96/103, 7, 898.78s), 33386925098 (96/103, 7, 808.64s), 33494135668 (97/103, 6, 788.74s). Zero disagreements on all six. origin/master has since caught up (no longer stale as of this task's creation).

All six were falsely classified NEW (not TIMING) by .github/scripts/unstable_watch_classify.py's classify(), because its DISAGREEMENT_SIGNATURE was a bare substring that matched pytest's unrendered f-string traceback listing rather than a real rendered disagreement. Fixed in commit cfb9cb4a (2026-08-31), which is not an ancestor of 98d3ad8d and has therefore never executed in any real CI run to date.

A local run at axiom-bearing HEAD=9ce3b4ad (which contains the 2026-08-31 Skolemized Seriality/Interpolation frame axioms, commit f9cc081e) recorded agreements=93 disagreements=0 timeout_count=10 conclusive=93/103, 951.21s -- worse on both axes than every one of the six CI runs above. The host was demonstrably NOT idle (load ~5.9 -> ~4.8 across 24 cores, 7.3GB of swap in use), so this single data point is confounded and does not discriminate between two live explanations:
  1. Axiom-driven solver cost increase (a real, rlimit-confirmed 4-6x cost increase from the same two axioms was already measured in a different Z3 constraint context by a related, currently-blocked task).
  2. Host contention alone.

WHAT WOULD DISCRIMINATE. Either (i) the same test at the same HEAD=9ce3b4ad on a verifiably idle CI-class runner (load ~0, no swap), or (ii) the same test at the pre-axiom 98d3ad8d checkout on a comparably-loaded local host (~load 5-6), to see whether contention alone reproduces a 93/103-class shortfall without the axioms.

CONSOLIDATED ITEMS (from the diagnosis report's "What remains open"):
1. Confirm cfb9cb4a actually reaches a real unstable-watch run now that origin/master has caught up, and confirm the next run(s) classify TIMING rather than NEW.
2. Re-measure this gating test's conclusive count once a real CI run executes the Skolemized Seriality/Interpolation axioms inside Z3OracleProvider's BimodalSemantics construction on an uncontended runner.
0a. Discriminate axiom cost from host contention as the cause of the local 93/103, 951.21s result (see "WHAT WOULD DISCRIMINATE" above).

INSTRUMENTATION NOW AVAILABLE. The ORACLE_GATING_SCAN_OUT_DIR environment variable (wired into this test's call site by a prior task) should be used on the first observation, so the per-formula timeout set is captured directly rather than lost again, as it was during the original 2026-08-27 -> 2026-09-01 investigation.

HARD CONSTRAINTS (verbatim, carried forward -- binding on this task): do not widen GATING_RECHECK_SOLVE_TIMEOUT_MS; do not lower MIN_CONCLUSIVE_GATING_FORMULAS; do not weaken, skip, or delete the assertion; do not de-quarantine or re-quarantine the test as the primary remedy; do not change bimodal semantics or the oracle soundness core or its unconditional-gating property.

NOT IN SCOPE: this is a discrimination/observation task, not a shortfall-remediation task. TESTING_GUIDE.md section 8.9's standing-rule escalation trigger (two review cycles, roughly two months, with no active repair work in progress) has not fired -- the marking is roughly one week old and repair work is actively in progress and partially landed. Do not treat this task as license to remediate the underlying shortfall itself; that decision is deferred until the discriminating observation this task produces exists.

---

### 178. Fix frame axiom solver cost regression
- **Effort**: 4-8 hours
- **Status**: [BLOCKED]
- **Task Type**: python
- **Topic**: test-reliability
- **Dependencies**: Task 176, Task 184

**Description**: Fix the 4-6x solver-cost regression that commit f9cc081e introduced into BimodalSemantics.build_frame_constraints, which forces TestShiftClosure::test_shift_closure_on_extracted_worlds_m3 to be quarantined under the `unstable` marker instead of passing. The quarantine is applied by the M=3 shift-closure task, which this task depends on; if that task's own marker phase is still in flight or was reverted when you read this, confirm the marker's actual presence at the test site rather than assuming it.

WHAT IS ESTABLISHED. This is not an open investigation -- the root cause is already bisected and recorded. Commit f9cc081e (2026-08-31 13:35) added build_seriality_constraint() and build_interpolation_constraint() to build_frame_constraints. Isolated single-process git-worktree bisection with a standalone repro produced: at f9cc081e^, rlimit_count = 7,850,279 (byte-for-byte identical across repeated runs) and the solver returns SAT; at f9cc081e, rlimit_count = 29,028,028 and the solver returns unknown/canceled at wall_seconds 15.0004 against the test's 15.0s max_time. At HEAD the range is 32.5M-46.5M, unknown/canceled on 5/5 runs. The effect is on Z3's machine-load-independent resource metric, so it is not a contention artifact. Full evidence: the specs entry for the M=3 shift-closure regression, baselines/01_head-classification.json through 04_attribution.md (active or archived).

START FROM THE RECORDED FRONTIER, DO NOT REDO IT. Seven encoding-level avenues were already tried and each failed to reach budget: explicit E-matching patterns on each new axiom individually and jointly; a corrected joint z3.MultiPattern following the existing build_forward_comp_constraint precedent; reordering the two axioms' position in build_frame_constraints' returned list; and combinations. Best measured result, re-measured cleanly by a sole owner across 5 runs, was rlimit_count 19.3M-21.4M -- a real and reproducible ~2.2x reduction from the unmodified 32-46M baseline, but still short of the ~8M region needed to finish inside the budget, with all 5 runs remaining unknown/canceled. That mitigation (E-matching patterns on both new axioms PLUS reordering them after skolem_abundance/world_uniqueness in build_frame_constraints' returned list) was deliberately NOT landed, to avoid banking a target-insufficient change without its own regression-gate pass. It is the frontier to start from, and it should be reconstructible from baselines/05_fix-attempts.md without re-deriving it. Per-avenue measurements are in that task's baselines/05_fix-attempts.md. Read it first and start past it rather than re-walking those seven.

WHAT SUCCESS LOOKS LIKE. Close the rlimit_count gap from the current ~11M-46M range down to the pre-regression ~8M region while keeping both new axioms' logical content intact, verified across a >= 20-seed re-verification with no undecided draw at max_time == 15.0. That is verbatim the exit criterion recorded at the `unstable` marker site in oracle/bimodal_logic/tests/test_soundness_regression.py, so satisfying it is what retires the marker. Removing the `unstable` marker is part of this task's completion, not a separate follow-up.

CONSTRAINTS. Do NOT revert the two axioms -- the task that added them deferred that decision deliberately, and reverting would drop asserted TaskFrame axioms from five back to three. Do NOT widen the test's 15.0s max_time budget. Do NOT weaken or remove the test's assertions. Do NOT touch GATING_RECHECK_SOLVE_TIMEOUT_MS or MIN_CONCLUSIVE_GATING_FORMULAS. A single green run is never sufficient evidence -- the marker's own exit criterion requires the >= 20-seed re-verification above.

WHY THIS EXISTS AS ITS OWN TASK. The quarantine task fixed the symptom (the red suite) and explicitly did not fix the cause. Nothing else in the backlog owns this cost regression, and an indefinitely-quarantined test is itself a defect to escalate per TESTING_GUIDE.md section 8.9's standing rule. This task is that escalation's owner.

---

### 176. Fix m3 shift closure sat regression
- **Effort**: 3-5 hours
- **Status**: [BLOCKED]
- **Task Type**: python
- **Topic**: test-reliability
- **Dependencies**: Task 184
- **Research**: [172_fix_contention_flaky_soundness_regression_tests/reports/02_spawn-analysis.md]
- **Plan**: [176_fix_m3_shift_closure_sat_regression/plans/01_m3-shift-closure-sat-regression.md]

**Description**: TestShiftClosure::test_shift_closure_on_extracted_worlds_m3 at oracle/bimodal_logic/tests/test_soundness_regression.py:541 fails deterministically with `AssertionError: Solver should find SAT for atom 'p' at M=3 with depth-bounded abundance` (structure.z3_model_status is False). Reproduced 2/2 across two independent full pass-1 oracle runs (bash oracle/run-oracle-suite.sh, 705.05s and 718.15s, both '1 failed, 615 passed, 2 skipped, 4 xfailed'). This is a DETERMINISTIC, reproducible failure -- not a contention flake -- discovered while verifying task 172 (fix_contention_flaky_soundness_regression_tests), which cannot fix it: the test constructs BimodalStructure directly with its own max_time: 15.0 budget, a different code path from the find_countermodel()/timeout_ms=5000/OracleTimeoutError mechanism task 172's xdist_serial remedy targets. In scope by file, out of scope by remedy.

HISTORICAL CONTEXT. This test's docstring cites 'Task 114 fix: uses temporal_depth=1 for bounded shift closure at M=3' -- the archived task-114 summary (specs/archive/114_skolem_abundance_overconstrain_fix/) shows task 114 (2026-06-01) introduced BimodalSemantics.depth_bounded_skolem_abundance_constraint(max_shift) specifically so this test would find SAT at M=3, and removed a prior xfail. specs/archive/108_soundness_regression_test_suite/ and specs/archive/114's own records show this test historically ran 2-8s against its 15s max_time budget -- 2-7x headroom, not a near-budget shape, so this does not look like a scheduling/timeout regression on its face (confirm structure.timeout's actual value as a first step, do not assume). Three later commits (task 144 phases 2-4, 2026-08-11, oracle-solve-cost-reduction) experimented with alternative Z3 trigger/grounding strategies for the same depth_bounded_skolem_abundance_constraint quantifier, but each commit message records it as reverted/tested-and-rejected -- verify the current encoding is genuinely byte-identical to the post-task-114 baseline rather than assuming the revert was clean. code/pyproject.toml pins z3-solver only as '>=4.8.0' (unpinned upper bound); the currently installed version is 4.16.0 -- check whether a drifted Z3 version altered solver behavior on this exact quantifier shape (MBQI/E-matching heuristics are version-sensitive). git log --stat on tasks 152/158/175's landed commits touches no bimodal semantic/solver code this test depends on, ruling out same-window tree drift as the cause.

WHAT TO DO. (1) Confirm whether the failure is a genuine solver UNSAT/inconclusive result within budget or a mislabeled timeout -- read structure.timeout directly. (2) Bisect or otherwise determine what changed since task 114 landed (Z3 version, an incomplete revert of the task-144 experiments, or something else) that turned a previously-SAT-finding encoding into a non-SAT one for this exact formula (atom 'p', M=3, temporal_depth=1, max_shift=1). (3) Fix the constraint/solver-layer defect if one is found, OR -- only if a genuine fix is not found -- mark the test `unstable` per code/docs/core/TESTING_GUIDE.md section 8.9, which requires ALL FOUR of: a documented failure mechanism with measurements, demonstrable non-semantic-ness, a genuine fix attempt recorded with why it failed, and a concrete written exit criterion. Do not weaken or remove the test's assertions to reach green.

CONSTRAINTS. Do not touch GATING_RECHECK_SOLVE_TIMEOUT_MS or MIN_CONCLUSIVE_GATING_FORMULAS. Do not widen this test's max_time budget merely to force green -- widening past the 15s value only masks a genuine UNSAT result and contradicts the 2-8s historical measurement showing budget was never the constraint. Verify the fix via a full `bash oracle/run-oracle-suite.sh` run (not a narrowed selection), confirming pass 1 reports zero failures. After this task lands, task 172 (fix_contention_flaky_soundness_regression_tests) should be re-verified and closed with /implement 172.

---

### 172. Fix contention flaky soundness regression tests
- **Status**: [BLOCKED]
- **Task Type**: python
- **Topic**: test-reliability
- **Dependencies**: Task 176, Task 184
- **Research**: [172_fix_contention_flaky_soundness_regression_tests/reports/01_contention-flaky-tests.md]
- **Plan**: [172_fix_contention_flaky_soundness_regression_tests/plans/01_mark-flaky-tests-xdist-serial.md]
- **Summary**: [172_fix_contention_flaky_soundness_regression_tests/summaries/01_mark-flaky-tests-xdist-serial-summary.md]

**Description**: Three tests in oracle/bimodal_logic/tests/test_soundness_regression.py fail deterministically under the gating suite's parallel pass but pass in isolation. They are CPU-contention casualties of a tight solve budget, and they were invisible to every narrowed verification gate run to date because no recent task touched their file.

THE THREE TESTS:
- TestBoundaryVacuity::test_depth1_countermodel_has_required_fields
- TestGuardedCompositionality::test_forward_comp_with_temporal_formula_output
- TestGuardedCompositionality::test_nullity_with_temporal_formula_output

MEASURED EVIDENCE (2026-08-26, full two-pass run of oracle/run-oracle-suite.sh on the 24-core dev host):
- Pass 1 (626 tests, -n 6, "not xdist_serial and not slow and not unstable"): 3 failed, 617 passed, 2 skipped, 4 xfailed in 770.33s. The three failures above are the only ones.
- All three fail identically with OracleTimeoutError at the provider default timeout_ms=5000, temporal_depth=1, time_bound M=3, raised at oracle/bimodal_logic/provider.py:292.
- Run SERIALLY at the same commit, all three pass in 4.53s TOTAL (~1.5s each) -- roughly 3x contention inflation against the 5000ms budget under six workers.
- Pass 2 (15 tests, serial): 15 passed in 677.08s, clean.

RULED OUT -- NOT A REGRESSION. The max_rlimit plumbing added to Z3OracleProvider.find_countermodel() is genuinely default-off: `timeout_ms: int = 5000` is unchanged and `max_rlimit` is only inserted into the settings dict when truthy (`if max_rlimit:`), mirroring ModelDefaults.solve()'s own guard. All three of these tests call find_countermodel(F_P) with no keyword arguments, so their code path is byte-for-byte identical to before that change. Do not spend time re-investigating this.

WHY THEY ARE NOT ALREADY HANDLED. These three tests are NOT marked @pytest.mark.xdist_serial, so they land in pass 1 under -n 6 rather than in the serial pass that exists precisely to eliminate this contention class. This is the same hazard the logos max_time floor corrected and that the CI-budget task addressed for example settings dicts -- but on a DIFFERENT constant: the oracle provider's own timeout_ms default, which no floor guard currently covers.

WHAT TO DO. Choose a remedy backed by measurement, not by pattern-matching:
(a) Route the three to the serial pass with @pytest.mark.xdist_serial -- the precedent already used for test_mixed_and_box_next and the BM_CM_4 parametrizations, and the fix the two-pass split was designed for. Cheapest and most consistent, but it lengthens pass 2 (currently 677s against an 1800s budget, so there is headroom -- confirm it stays inside).
(b) Pass max_rlimit alongside timeout_ms at these call sites -- Z3's load-INDEPENDENT resource-unit budget, already plumbed end-to-end and blessed by code/docs/core/TESTING_GUIDE.md section 8.6. Measure the rlimit for each of the three formulas first and set the budget over the measured worst draw with headroom, following the ~2x-to-3x-of-worst convention used elsewhere in this tree. This addresses the root cause (wrong unit) rather than rescheduling around it.
(c) Both -- (a) for immediate green, (b) for durability.

Also consider, and decide explicitly with reasons recorded: whether the oracle provider's timeout_ms=5000 default deserves a floor guard analogous to code/tests/ci/test_example_budget_floor.py, since nothing currently prevents another test from being written against a budget that only holds when the machine is idle. Survey the other call sites before deciding -- a floor is only worth adding if the population justifies it.

CONSTRAINTS:
- Do NOT weaken any assertion to reach green.
- Do NOT edit GATING_RECHECK_SOLVE_TIMEOUT_MS (stays 40000) or MIN_CONCLUSIVE_GATING_FORMULAS (stays 100).
- Verify via the real two-pass driver `bash oracle/run-oracle-suite.sh`, NOT a narrowed single-file selection -- narrowed gates are exactly what hid this defect. Budget ~25 minutes for a full run (pass 1 ~13 min at -n 6, pass 2 ~11 min serial).
- Note for the implementer: long runs are reaped by the harness if launched as ordinary background tasks. Use `setsid nohup ... &` to detach, then poll.

---

### 154. Extension certified search over small bimodal models
- **Status**: [BLOCKED]
- **Task Type**: python
- **Topic**: semantics
- **Dependencies**: Task 152, Task 153, Task 184

**Description**: THE PAYOFF, and the one task in this group where OVER-CLAIMING is the principal risk. With the frame axioms in place, the paper's `thm:extension` becomes applicable to bimodal countermodels: every partial history the solver finds is a fragment of a genuine total world history in $H_\F$. Use that to move work out of the solver -- but only the half the theorem actually covers.

WHAT THE THEOREM BUYS. Today the solver is made to approximate totality inside the search: `world_interval_constraint` gives each world a time interval, `lawful` chains unit steps across it, and the `capped_skolem_abundance_constraint` / `depth_bounded_skolem_abundance_constraint` family manufactures time-shifted copies. The extension theorem says the interval-and-shift scaffolding is not needed in order to KNOW that a found history is realizable: any partial assignment consistent with the frame axioms already lies inside some total history. So the solver may search genuinely small partial structures -- fewer worlds, narrower windows, no shift closure -- with totality discharged afterwards.

WHAT IT DOES NOT BUY. This must be stated in the code and in the summary, not only here. `thm:extension` is EXISTENTIAL. It certifies that a witness exists; it says nothing about universal obligations. Truth of `\Box \phi` quantifies over all of $H_\F$, and truth of `\Future \phi` and `\Past \phi` over all of $\D$, whereas `NecessityOperator.true_at` currently quantifies over the solver's finite world set and the tense operators over the bounded window. The abundance constraints approximate that second column and the extension theorem DOES NOT REPLACE THEM. Any design that drops abundance wholesale and cites `thm:extension` as cover is wrong. The preceding audit's baseline records exactly which examples this bites; use it.

DELIVERABLE 1 -- POST-HOC CERTIFICATION. After extraction, take the countermodel's partial histories and produce the finite lasso witness of BimodalLogic 441 (prefix plus cycle, forward and backward), verify that it satisfies the frame axioms and agrees with the extracted window, and attach it to the model structure. This is the concrete, checkable form of the claim "this bounded history is a fragment of a possible world", and it replaces the prose assurance currently carried in the `task_restriction` soundness comment.

DELIVERABLE 2 -- SPLIT THE CONSTRAINT SET BY POLARITY. Formulas whose falsification obligations are purely existential -- no `\Box` or universal tense operator in a verifying position -- need no abundance closure and can be searched at smaller `M` with fewer worlds. Formulas carrying universal obligations keep the current treatment. Drive this off the EXISTING `temporal_depth` machinery, which already performs depth-aware abundance selection, rather than adding a second parallel mechanism beside it.

DELIVERABLE 3 -- MEASURE IT. The claim here is a performance claim as well as a soundness claim. Report solve times against the audit baseline for the examples in each polarity class, and report honestly if the win turns out to be small or absent. A correct-but-slower result is a legitimate outcome and should be reported as such rather than tuned until it looks good.

DELIVERABLE 4 -- SURFACE THE CERTIFICATE. A user who gets a bimodal countermodel should be able to see the extension witness, not just the bounded window. Fit this to the existing output conventions rather than inventing a new output channel.

REGRESSION PROCEDURE. Use `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/README.md` for the concrete re-run/diff procedure against the audit's baseline; the `task_restriction` soundness comment this task's Deliverable 1 replaces the prose assurance of is assessed standalone in `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/02_task-restriction-verdict.md` (verdict: independent gap, not subsumed by the frame-axiom task).

DEPENDENCIES. The frame-axiom task (without *Seriality* and interpolation the extension theorem does not apply at all), the audit task (baseline), and BimodalLogic 441 (the lasso construction and the agreement lemma, including its explicit statement of what does not transfer).
