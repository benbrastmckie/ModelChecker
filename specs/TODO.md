---
next_project_number: 219
---

# TODO

## Task Order

*Updated 2026-09-29. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 198,200,216,217,218 | -- | documentation, semantics, cli-presentation |
| 2 | 199 | 198 | documentation |

**Grouped by Topic** (indented = depends on parent):

### Documentation

216 [NOT STARTED] — Apply the upstream A1 / A1-Gamma / A3 adequacy-chain rows to...
199 [NOT STARTED] — Write the round-trip ledger in...

### Semantics

198 [BLOCKED] — Make bound realization (A3) a computation rather than an...
200 [BLOCKED] — Extend the bimodal theory to the language with the stability...
217 [NOT STARTED] — Re-scope the two blocked bimodal adequacy consumers in...

### Cli Presentation

218 [NOT STARTED] — Refactor bimodal/ theory countermodel presentation in...

## Tasks

### 218. Refactor bimodal countermodel presentation
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: cli-presentation
- **Dependencies**: None

**Description**: Refactor bimodal/ theory countermodel presentation in dev_cli.py output: review the old presentation in /home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/theory_lib/bimodal/examples.py for salvageable elements (inspiration only, theory is outdated), research best CLI display methods online, and systematically improve the presentation elements for the current bimodal/ theory in this repo, making any other systematic model-checker changes only as needed

---

### 217. Rescope blocked adequacy consumers
- **Status**: [NOT STARTED]
- **Task Type**: meta
- **Topic**: semantics
- **Dependencies**: None

**Description**: Re-scope the two blocked bimodal adequacy consumers in specs/state.json, whose recorded blockers no longer match the upstream state. This task edits task metadata under specs/ only. It must not edit any document under code/, and it must not edit the BimodalLogic repository.

WHY BOTH ENTRIES ARE NOW WRONG, IN DIFFERENT DIRECTIONS. Verify each of the following against the live /home/benjamin/Projects/BimodalLogic tree before rewriting anything; treat this description as a lead to check, not as findings to transcribe.

ENTRY 1, the A3 compute-bounds-from-closure task (project_name a3_compute_bounds_from_closure). Its recorded blocker is that there is no computable f to read and nothing here should invent one. That blocker is discharged: f now exists in closed form, supplied by the landed compression instance exists_witnessFamily_of_not_validZTime -- confirm the exact fully-qualified name in the tree -- and the upstream adequacy row for A3 is reclassified from vacuous to live and open. But the task must NOT simply be unblocked as written, because only part of its deliverable is now justified. Split the recorded scope accordingly: the mid clause is satisfiable by magnitude and is actionable; the back/fwd clause is NOT, because the landed theorem bounds segment lengths and not minimal periods, so representability against a registry that folds by exact modulus still requires a bounded sweep. Record in addition that the landed instance holds only at empty premises and a single conclusion while every countermodel example in this repository's bimodal examples.py carries a non-empty premise list, with MD_CM_1 at two conclusions, so the general consequence form is a separate open upstream obligation this task depends on for its full scope. Keep the task's honest-reporting half intact and make explicit that it grows in importance rather than shrinking: a bare reading of "f now exists" overclaims relative to what landed, and the never-report-validity discipline is what prevents that overclaim reaching users. Choose the resulting status deliberately -- either unblock it at the reduced, genuinely actionable scope, or keep it blocked with the blocker restated as the back/fwd periodicity result and the general consequence form -- and say in the entry which was chosen and why.

ENTRY 2, the stability-modal extension task (project_name extend_bimodal_to_stability_modal). Its recorded blocker names four upstream tasks and says that until the agreement lemma lands there is no soundness argument. All four are now marked completed upstream, so a status-only check reads as discharged. That reading is wrong and the entry must not be unblocked. The upstream compression-and-assembly task's own plan was to land a refutation and re-scope: the current six-condition L-plus substrate is proved to certify NO instance of the stability modal, in either target placement, at any time or size, and the corresponding integer-time non-validity is proved, so the empty certificate class is a completeness failure and not a vacuity. The root cause is that the local-coherence snce clause quantifies its predecessor over the share-class at the label's own time, forcing any two indices naming the same world state to agree on every snce formula of the closure; the untl clause escapes only by quantifying at the successor time. Confirm the governing declaration names in the tree. Rewrite the blocker to name the three upstream successor tasks that are actually outstanding -- the stability-modal substrate design task that is the design authority, the sharing-substrate redesign task that proposes one candidate to be folded into it, and the L-plus carrier normalization task that is an independent prerequisite for any decidability route -- all three currently not started. Record also that there is no L-plus compression subtree at all yet, and that upstream states it is worth building only against a corrected condition set, since that subtree is precisely what this task would consume. Keep the status blocked. The task's original reasoning is superseded while its conclusion stands, and the entry should reflect the present blocker rather than the discharged one.

HOW TO WRITE THE ENTRIES. Update each description in place via the repository's own state-writing script rather than hand-editing specs/state.json, and regenerate TODO.md in the same pass. Keep both descriptions self-contained: a future reader must be able to act on them without re-deriving any of this from the upstream repository. Cross-repository task numbers are acceptable inside these specs entries, but cite the upstream results that matter by fully-qualified declaration name as well, so the entries survive renumbering on either side. Narrative and provenance belong here in specs/, not in any deliverable document.

---

### 216. Apply upstream adequacy chain rows
- **Status**: [NOT STARTED]
- **Task Type**: general
- **Topic**: documentation
- **Dependencies**: None

**Description**: Apply the upstream A1 / A1-Gamma / A3 adequacy-chain rows to code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md and TRUST_PIPELINE.md, and move the WitnessFamily/Compression citations onto the name + manifest convention.

PROVENANCE. This is not a fresh audit. The producing repository has already derived copy-ready replacement text and deliberately did not reach across the repository boundary to apply it. Read it first: /home/benjamin/Projects/BimodalLogic/specs/693_a1_compression_conformance_adequacy_chain/handoff-a1-adequacy-rows.md, sections (a) through (d), plus its cited report reports/01_a1-compression-conformance.md in that same directory. Verify each claim against the live BimodalLogic tree rather than trusting the note, and do not edit that repository.

STYLE CONSTRAINT, BINDING AND THE POINT OF THIS TASK. The deliverable documents must state only the CURRENT status of each component. They must NOT carry transition narrative, change-log prose, or dated/recency language that goes stale the moment the upstream tree moves again -- no "moves from open to partially discharged", no "what changed", no "recently landed", no "as of <date>", no "this supersedes the earlier route" framing. Where the handoff note itself is written as a transition (its "What changed, in one line each" block, and section (b)(1)'s instruction to keep the rejected exists_annot_of_truth route "as history"), translate it into present-tense status and DO NOT carry the history across. A durable technical reason why a route cannot work may be kept as a standing qualification; a record of which route was tried when may not. Scope restrictions ARE current status, not history, and must be kept: that the landed compression instance holds at empty premises and a single conclusion, and that the general consequence form is a separate open obligation, are present facts about what is and is not proved. Narrative belongs in specs/, not in these documents.

ITEM 1, THE THREE COMPONENT ROWS. In ADEQUACY.md section 7's component table (header "| | Component | Status |"): replace the A1 row, leave A0 and A2 unchanged, insert a new A1-Gamma row after A1, and replace the A3 row. A1 is discharged only at the empty-premise, single-conclusion instance, via exists_witnessFamily_of_not_validZTime, sorry-free, axiom closure {propext, Classical.choice, Quot.sound}. A1-Gamma carries the general form the chain actually consumes and is open; record that every countermodel example in this repository's bimodal examples.py has a non-empty premise list and that MD_CM_1 has two conclusions, since that is what makes the restriction load-bearing here rather than cosmetic. A3 is no longer vacuous: f exists in closed form. Prefer stating f's closed form, which upstream checks by rfl, over transcribing a table of sampled bound values that can drift; if sampled numbers are included at all, attribute them to the named declaration they were measured from. A3's mid clause is satisfiable by magnitude; its back/fwd clause remains open because the landed theorem bounds segment lengths and not minimal periods, so representability against a registry folding by exact modulus still needs a bounded sweep. Keep the max_witnesses precondition note.

ITEM 2, A LIVE SELF-CONTRADICTION BETWEEN TWO DOCUMENTS IN THIS REPOSITORY. TRUST_PIPELINE.md's A-component table states A3 in the magnitude form ("configured lengths >= f(|C|)"), while ADEQUACY.md section 7's A3 row states the representability form and says in terms that the magnitude form can be false even when the underlying family exists. The producing repository carries three independent warnings on this same point. Adopt the representability form in both documents so they agree. Also correct TRUST_PIPELINE.md's "In the Lean development" table row for compression and the verified bounded enumerator: verified absence is a theorem at restricted scope, not a live capability and not a practical replacement for trusting Z3 UNSAT -- the two sides quantify differently (the Lean criterion over the whole segment-length grid, a Z3 UNSAT verdict at one configured triple), there is no executable target that runs the enumerator, and the decision procedure is a def rather than a global instance. State that as the row's standing scope, not as a correction of a previous claim.

ITEM 3, CITATION CONVENTION, WHICH IS THE STRUCTURAL FIX FOR STALENESS. The producing repository now seeds the declarations this argument turns on into scripts/lean-citation-seeds.txt, generates scripts/lean-citation-manifest.json from it, and keeps that manifest byte-current under its own gate. Move the WitnessFamily/ and Compression/ citations in these two documents onto the name + manifest convention the manifest's note field prescribes, instead of file.lean:NNN anchors. This is not cosmetic: ADEQUACY.md currently cites Agreement.lean:232 for WitnessFamily.joint_countermodel in two places, and the declaration's keyword line is now 248 -- the name never changed and no gate in either repository went red, which is exactly the failure mode line anchors produce. Fix both occurrences by name rather than by renumbering them.

VERIFICATION. Confirm every fully-qualified declaration name cited actually resolves in the live BimodalLogic tree before writing it. Re-read both edited documents end to end afterwards and confirm no transition narrative, dated language, or line-number anchor to the WitnessFamily/Compression subtree survives. Per this repository's no-task-references-in-deliverables rule, cite no task numbers from either repository in the edited documents; provenance belongs in this task's own specs artifacts.

---

### 215. Fix persistent searchsolver population in shared iterate engine
- **Effort**: 3-4 hours
- **Status**: [COMPLETED]
- **Task Type**: z3
- **Topic**: semantics
- **Dependencies**: None
- **Research**: [210_fix_generic_iterator_pinning_unreached/reports/02_spawn-analysis.md]
- **Plan**: [215_fix_persistent_searchsolver_population_in_shared_iterate_engine/plans/01_populate-persistent-search-solver.md]
- **Summary**: [215_fix_persistent_searchsolver_population_in_shared_iterate_engine/summaries/01_populate-persistent-search-solver-summary.md]

**Description**: code/src/model_checker/models/structure.py's ModelDefaults.solve() assigns self.stored_solver = self.solver BEFORE calling self._setup_solver(model_constraints), which is what actually populates constraints and reassigns self.solver to a new, populated solver object (structure.py:254-260). Because stored_solver is captured before that reassignment, it permanently references the solver's empty, pre-population state, for every theory. Combined with solve()'s finally-block cleanup (_cleanup_solver_resources(), structure.py:298-300) unconditionally setting self.solver = None, iterate/constraints.py's ConstraintGenerator._create_persistent_solver() (lines 56-98) builds the live iteration loop's persistent search solver from an empty assertion set for every theory without a bimodal-style workaround (logos, exclusion, imposition) -- confirmed empirically, len(iterator.constraint_generator.solver.assertions()) == 0 immediately after constructing a real LogosModelIterator/ExclusionModelIterator/ImpositionModelIterator. Bimodal already works around this exact defect for itself via theory_lib/bimodal/iterate.py's _ensure_frame_constraints_in_search_solver (lines 105-196), whose own docstring names the root cause as 'a bug in the shared engine (models/structure.py's solve())' -- but that workaround was never generalized to the other three theories. Fix strategy (choose one during research/planning, both are viable and should be weighed on their merits, not decided here): (1) root-cause reorder fix -- move self.stored_solver = self.solver in solve() to AFTER _setup_solver reassigns self.solver, so stored_solver correctly references the populated solver (it is not cleared by _cleanup_solver_resources(), so it survives past solve()'s return); before making this change, search all stored_solver usages repo-wide to confirm nothing relies on the current broken pre-population timing. (2) generalize bimodal's re-assertion into the shared ConstraintGenerator base class (iterate/constraints.py), re-asserting frame_constraints/model_constraints/premise_constraints/conclusion_constraints onto self.solver after _create_persistent_solver() runs, for every theory, mirroring theory_lib/bimodal/iterate.py:105-196 moved one level up. Either strategy must leave bimodal's existing _ensure_frame_constraints_in_search_solver override in place, unmodified -- the two mechanisms being redundant for bimodal post-fix is an accepted side effect, not a defect to resolve in this task. Add live, non-mocked regression coverage (new or extended file under code/src/model_checker/iterate/tests/) asserting, for logos, exclusion, and imposition: the persistent search solver has a non-zero assertion count immediately after iterator construction against a real, solved BuildExample (fails today, confirmed 0 for all three); and more strongly, that a model produced by that persistent solver actually satisfies the real frame_constraints/model_constraints/premise_constraints/conclusion_constraints (not merely a non-empty assertion count). Confirm bimodal's tests/integration/test_iterate.py is unchanged in outcome. Run the full iterate/ suite plus the four-theory directory gate and record results. Explicitly OUT OF SCOPE: code/src/model_checker/iterate/models.py's generic pinning loop and iterate/tests/integration/test_models.py's TestGenericPinningReachesRebuiltSolve class (both are task 210's own Phase 3/4 territory, not this task's) and removing/simplifying bimodal's own workaround. This task unblocks task 210's Phase 3 closure: once the persistent search solver is genuinely populated, task 210's already-correct pin-routing fix (appending pins into model_constraints.frame_constraints) will make the pinned candidate satisfiable rather than UNSAT for logos and imposition, exactly as it already is for exclusion.

---

### 214. Apply upstream citation corrections
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: documentation
- **Dependencies**: None
- **Research**: [214_apply_upstream_citation_corrections/reports/01_citation-corrections-mapping.md]
- **Plan**: [214_apply_upstream_citation_corrections/plans/01_apply-citation-corrections.md]
- **Summary**: [214_apply_upstream_citation_corrections/summaries/01_apply-citation-corrections-summary.md]

**Description**: Apply the citation corrections the BimodalLogic repository has already derived and made copy-ready for this side, to code/src/model_checker/theory_lib/bimodal/docs/.

PROVENANCE. This is not a fresh audit. The producing repository's cross-repository citation
gating work completed its half and deliberately wrote nothing under ~/Projects/ModelChecker,
recording instead a "Corrections the consuming table owes" table at
~/Projects/BimodalLogic/docs/reference/transcription-audit-surface.md (currently ~line 148).
That table is the input to this task. It states explicitly that the corrections are to be
applied "by mechanical lookup rather than by re-deriving them", and that every row resolves
against the generated ~/Projects/BimodalLogic/scripts/lean-citation-manifest.json, which the
producing side's check C35 keeps current. Read the corrections table and the manifest; do not
re-derive line numbers by hand, and do not edit anything in the producing repository.

FOUR ROWS TO APPLY. Confirm each against the manifest before editing, since the producing tree
moves.

(1) FOUR STALE LINE CITATIONS. not_validIn_base_prior_UZ, not_validIn_base_z1,
prior_UZ_minFrameClass_sharp and z1_minFrameClass_sharp each now land inside a different
theorem, not_validOn_z1_dense, after a uniform shift caused by a docstring edit above the
targets. ADEQUACY.md cites all four with explicit line numbers in at least two places -- its
machine-checked-results table (~lines 255-257, citing ZTimeSharpness.lean:225, 236, 251, 262)
and its A0 discussion (~lines 716-725, repeating :225, :236, :251, :262). Both sites are wrong.
Note for the record while fixing it that every gate in both repositories was green while these
citations were wrong; that is the stated reason the manifest and C35 exist, and it is the
argument for preferring name citations over line citations below.

(2) ONE CITED RANGE THAT NO LONGER EXISTS. The hand separation proof that ADEQUACY.md's Lemma-1
Limit row points at (~line 243, "discharged for `std` at
Metalogic/Decidability/WitnessFamily/Std.lean:73-80") has been deleted.
WitnessFamily.std is now built through Semantics.ShiftSet.ofIntAction; cite that and
ShiftSet.sep_of_succOrder instead. The row's verdict IMPROVES and the edit must say so: the
obligation is now kernel-checked rather than hand-proved. Do not silently swap the citation and
leave the old weaker verdict standing.

(3) TWO LOOSE RANGES. WitnessFamily.std_isZTime, std_sat_ztime, std_sat_base, sh_surj and
ProofSystem.FrameClass.Sat are cited over ranges that are correct under the span convention but
wider than the declaration. The manifest carries both the keyword line and the full span.

(4) THE LIMIT VERDICT IS TOO STRONG, AND THIS ONE IS A SUBSTANTIVE CORRECTION, NOT A STALE
POINTER. TaskFrame.Limit transcribes only the subset half of the paper's set equation. The
superset half -- that w lies in each of its own positive cones -- is lem:nullity, DERIVED
choice-free from Seriality together with the subset half, via
TaskFrame.nullity_of_serial_limit; it is not postulated, and carrying it as an axiom would
duplicate a theorem. Soften every consuming statement that presents Limit as transcribing the
full equation. Note that ADEQUACY.md's surrounding argument about state-sharing already says,
correctly and at length (~lines 318-342), that the real obstruction is not Limit or Saturation
but Lemma 2 and the Box case -- so check whether this correction interacts with that passage
before editing, and keep the two consistent.

THREE RESIDUE ROWS HANDED OFF. The producing table's rows 3, 20 and 24 are the ones its own
audit does not reach, and were made copy-ready with explicit hand-off framing for this side.
Row 3 is FrameOver's worldNonempty field and its TaskFrame.worldNonempty accessor -- the
paper's reading of W as a NONEMPTY set, mattering because an empty carrier satisfies all four
constraints vacuously while validating falsehood. Row 24 carries a conditional that the
producing side preserved exactly; preserve it exactly here too rather than paraphrasing it.
Decide, and record, whether each belongs in this repository's adequacy argument at all.

SCOPE. Documentation only, confined to code/src/model_checker/theory_lib/bimodal/docs/ --
ADEQUACY.md primarily, with ARCHITECTURE.md carrying WitnessFamily.std and sh_surj as well.
Derive the affected file set fresh by grepping the docs directory for each declaration name
rather than trusting this list. No source, test or gate changes; no full-theory gate run is
required, and the verification that matters is that every citation this task touches resolves
by name in the manifest.

PREFER NAMES OVER LINES where the surrounding prose allows it. Four of these rows are stale
purely because a docstring edit shifted line numbers underneath them, and the producing side's
instruction on every such row is "cite the names; take the locations from the manifest". Each
line number left behind is a future instance of this same task.

---

### 213. Fix lazy bounded probe parallel flake
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None
- **Research**: [213_fix_lazy_bounded_probe_parallel_flake/reports/01_lazy-bounded-probe-flake-fix.md]
- **Plan**: [213_fix_lazy_bounded_probe_parallel_flake/plans/01_lazy-bounded-probe-flake-fix.md]
- **Summary**: [213_fix_lazy_bounded_probe_parallel_flake/summaries/01_lazy-bounded-probe-flake-fix-summary.md]

**Description**: Fix the wall-clock flake in test_checker.py::TestLazyBoundedMemoizedProbe, and close the scanner blind spot that let it land unmarked.

SCOPE CORRECTION (this task's original framing named the wrong test and a fix that has already landed). The original description proposed diagnosing "the probe's bound" as a wall-clock timeout and marking it. That fix is already in the tree: test_probe_timeout_yields_unavailable_not_a_hang carries @pytest.mark.xdist_serial, added by the certifying-countermodel work's final-gate phase, four hours before this task was written. It is NOT the failing test and must not be touched.

THE ACTUAL FAILING TEST, named identically in three independent full-gate reproductions:
TestLazyBoundedMemoizedProbe::test_import_performs_no_subprocess_call
(code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py, currently ~line 142).

EVIDENCE, already recorded -- do not re-derive it from scratch:
specs/206_refactor_verification_test_harness/baselines/01_ci-shaped-baseline.md reproduces it
three times (Run 2 post-task-205 baseline, the Phase 6 "After" run, and the parallel pass),
each time as the single failure in an otherwise green ~3140-item run under
`-m "not packaging and not performance and not unstable and not xdist_serial" -n 4`.
Standalone it passed in 0.58s and 0.60s. The same task's .orchestrator-handoff.json records it
as an out-of-scope pre-existing flake.

WHY IT FAILS. The test spawns a subprocess (`sys.executable -c <source string>`) whose source
reads a real clock around an import and asserts `elapsed < 1.0`. Measured standalone cost is
~0.6s, so the bound carries roughly 0.4s of headroom -- headroom that a contended four-worker
pool routinely consumes. When the inner assert trips, the subprocess exits non-zero and the
outer `assert result.returncode == 0` fails. This is host-load sensitivity, not a logic defect,
which is exactly why it never reproduces standalone.

ITEM 1 -- FIX THE ASSERTION. Prefer deleting the wall-clock assertion outright over marking or
widening it. The test's stated purpose is that importing the module must not probe, and the
neighbouring assertion `m._memoized_result is m._UNSET` already establishes precisely that,
deterministically and independently of host load; `subprocess.run(..., timeout=15)` already
guards against a genuine hang. On that reading `elapsed < 1.0` is a redundant proxy for an
invariant the test checks directly, and removing it costs no coverage. If the timing assertion
is judged to carry independent value, then mark it and justify the bound in a comment -- but
make that case explicitly rather than by default, and do not simply raise the number until the
flake stops reproducing.

ITEM 2 -- CLOSE THE SCANNER BLIND SPOT. code/tests/ci/test_timing_marker_coverage.py exists to
stop exactly this shape from reaching the contended pool unmarked, and it did not catch this
one. Its own docstring is accurate about why: detection is a structural AST scan over a test
function's own body plus a one-hop same-module helper, looking for a `time.time()` /
`perf_counter()` / `monotonic()` call node together with a bound-comparison `assert` node. Here
both live inside a string literal handed to `subprocess.run`, so the AST sees one
`ast.Constant` and nothing to flag. Extend the guard to recognize clock-read-plus-bound-assert
pairs inside string literals passed to subprocess/exec-style call sites, and add a self-test in
that module's existing style proving the extended scan flags the shape. If that detection is
judged too broad or too fragile to implement as an AST rule, record the decision and the
reasoning in the module docstring alongside its existing scope carve-outs (the deliberately
excluded `time.sleep()` case is the precedent for how to document a boundary) rather than
leaving the gap silently open.

VERIFICATION. Item 1's correctness does not depend on a contended reproduction: if the
assertion is removed, the failure mode is gone by construction, and a single full-gate run
under `-n 4` confirming a clean parallel pass is sufficient. Do not attempt to prove a negative
by repeated draws. Item 2 is verified by its own self-test.

---

### 212. Consolidate remaining bimodal test helpers
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: Task 210
- **Research**: [212_consolidate_remaining_bimodal_test_helpers/reports/01_consolidate-remaining-bimodal-helpers.md]
- **Plan**: [212_consolidate_remaining_bimodal_test_helpers/plans/01_consolidate-remaining-bimodal-helpers.md]
- **Summary**: [212_consolidate_remaining_bimodal_test_helpers/summaries/01_consolidate-remaining-bimodal-helpers-summary.md]

**Description**: Consolidate the remaining bimodal test modules that define their own _settings/_build helpers onto tests/_build_support.py. Four call sites were folded onto the shared helper when it was introduced; the rest were outside that task's declared scope.

DERIVE THE LIST FRESH, do not trust a count. At the time of writing, grep -rln for '^def _settings' and '^def _build' across code/src/model_checker/theory_lib/bimodal/tests/, excluding _build_support.py itself, reports ten modules: integration/test_data_extraction.py, integration/test_injection.py, integration/test_iterate.py, integration/test_output_gate.py, integration/test_until_since_integration.py, unit/test_operators.py, unit/test_proposition.py, unit/test_semantics_core.py, unit/test_structure.py, unit/test_witness_constraints.py. Re-run the grep before starting, since concurrent work in this tree changes the set.

ONE OF THOSE TEN IS NOT A CANDIDATE. unit/test_structure.py's local _build is a deliberate, documented four-line wrapper that defaults the 'verify' setting to 'off' before delegating to the shared helper, preserving an output-gate determinism fix. Leave it. It is also the precedent for how to handle any other module whose helper turns out not to be equivalent: keep a documented local wrapper that delegates, rather than either forcing the module onto the shared form or leaving a full duplicate.

Establish equivalence by reading each helper against _build_support.py's, not by assuming the shared name implies a shared shape. Where a module's helper differs, say why in the module and do not silently normalize the difference away. Verify with the full four-theory gate rather than the bimodal subset.

---

### 211. Correct kernel checked proof overclaim
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: documentation
- **Dependencies**: None
- **Research**: [211_correct_kernel_checked_proof_overclaim/reports/01_kernel-checked-proof-overclaim.md]
- **Plan**: [211_correct_kernel_checked_proof_overclaim/plans/01_kernel-checked-proof-overclaim.md]
- **Summary**: [211_correct_kernel_checked_proof_overclaim/summaries/01_kernel-checked-proof-overclaim-summary.md]

**Description**: Resolve the kernel-checked-proof contradiction in the bimodal trust documentation, and decide the BIMODAL_LOGIC_COMMIT pin's fate. Three items.

ITEM 1, A LIVE SELF-CONTRADICTION (verified against the tree, not inherited from a report). Two documents in code/src/model_checker/theory_lib/bimodal/docs/ now say opposite things about what an acceptance: entailment verdict licenses.

ASSERTS the claim, and is the side that is wrong:
- ADEQUACY.md line ~457: '"entailment" means the binary constructed the paper-countermodel existence term for this particular certificate (a kernel-checked proof)'.
- ADEQUACY.md line ~490: '... constructing the paper-countermodel existence term rather than printing a verdict -- a kernel-checked proof for that particular certificate, not merely four Decidable instances agreeing'.

DENIES the claim, and is already correct -- DO NOT "fix" these:
- TRUST_PIPELINE.md line ~162 and A2_GAP.md line ~519 both read 'It is not a kernel-checked proof for ...'.
- SETTINGS.md line ~108 states the accurate position explicitly: the phrase belongs to a reserved third Acceptance value (per-certificate kernel checking by re-elaboration) that nothing this checker produces today.

Per BimodalTools/CertificateImport.lean's Acceptance inductive docstring, SETTINGS.md is right. The accurate narrower claim, already used throughout semantic/checker.py and the docs written alongside it: Lean constructed a WitnessFamily.Refutes term for this certificate by applying a compile-time kernel-checked implication to four run-time decisions. Rewrite the two ADEQUACY.md sites to that wording. The overclaim does not reach users -- semantic/model.py's _verification_label is written from the Lean docstring directly -- so this is a documentation-consistency defect, not a false user-facing claim. Re-grep for 'kernel-checked proof' across the docs directory when done: every surviving occurrence should either deny the claim or be SETTINGS.md's explanation of why the phrase is reserved.

ITEM 2, A DEAD PIN. Decide whether to auto-track or retire tests/_lean_check.py's BIMODAL_LOGIC_COMMIT constant. It is declared and exported but consumed by nothing, and has drifted repeatedly. Enforcement now lives in semantic/checker.py's capability handshake, with the commit captured dynamically as CheckerHandle.provenance per resolution rather than read from the stale constant.

ITEM 3, VERIFY A DEFERRAL BEFORE RESTATING IT. TRUST_PIPELINE.md records the Lean-side half of obligation S4 as deferred and not yet attempted, but the companion BimodalLogic repository now declares a translate_sentence executable (root BimodalTools.TranslateSentenceMain) in its lakefile.toml. Infrastructure may exist even where the truth-preservation theorem does not. If the sentence-translation conformance task has already landed, prefer its findings over a fresh probe.

---

### 210. Fix generic iterator pinning unreached
- **Status**: [COMPLETED]
- **Task Type**: z3
- **Topic**: semantics
- **Dependencies**: Task 213, Task 215
- **Research**: [210_fix_generic_iterator_pinning_unreached/reports/01_fix-generic-iterator-pinning.md]
- **Plan**: [210_fix_generic_iterator_pinning_unreached/plans/01_fix-generic-iterator-pinning.md]
- **Summary**: [210_fix_generic_iterator_pinning_unreached/summaries/01_fix-generic-iterator-pinning-summary.md]

**Description**: Fix generic iterator pinning never reaching the rebuilt model's solve for logos, exclusion and imposition. The generic is_world/possible/verify/falsify pinning loop in code/src/model_checker/iterate/models.py accumulates its pins into a local temp_solver that is write-only for any theory without a _pin_theory_specific_values override -- logos, exclusion and imposition. Those three theories' rebuilt models during iteration are therefore effectively unpinned: the pins are computed but never reach the Z3 solve that actually produces the next model, and iterate/core.py's loop has no consistency check that would catch a divergent rebuild. Bimodal is unaffected, having an override that appends to frame_constraints directly.

EVIDENCE: a live, non-mocked logos iteration probe showing rebuilt model 2's is_world signature is an independent, unpinned resolve. Recorded as finding F4 in specs/207_fix_stale_all_constraints_snapshot/reports/01_fix-stale-all-constraints.md, and deliberately left out of scope by that task's plan because fixing it changes iteration results for three theories.

SCOPE: (1) confirm the same live probe for exclusion and imposition rather than assuming the logos result generalizes; (2) decide whether the fix is a _pin_theory_specific_values default that actually applies temp_solver's assertions, or a different mechanism; (3) add regression coverage for iteration correctness analogous to TestAllConstraintsReflectsCertificateAfterSolve, which covers display completeness only. Run the full four-theory gate, since this changes iteration results.

ALSO FIX while in this area: theory_lib/bimodal/iterate.py's _ensure_frame_constraints_in_search_solver docstring still says, in the present tense, that all_constraints "permanently misses" the certificate encoding. That stopped being true when all_constraints became a read-only computed property; the defensive design the docstring documents (reading the four component lists directly) remains correct and necessary for the separate stored_solver bug it is actually about.

---

### 209. Bimodal sentence translation contract
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: cross-repo-contract
- **Dependencies**: Task 205, Task 206
- **Research**: [209_bimodal_sentence_translation_contract/reports/01_sentence-translation-contract.md]
- **Plan**: [209_bimodal_sentence_translation_contract/plans/01_sentence-translation-contract.md]
- **Summary**: [209_bimodal_sentence_translation_contract/summaries/01_sentence-translation-contract-summary.md]

**Description**: Fix the extremal-operator defect in Sentence.update_types and wire the sentence-translation conformance channel against BimodalLogic's fixture. Relocated from the BimodalLogic repository, where the research and plan were authored but every source edit lands here; that plan is complete, strict-validated, and should be READ RATHER THAN REDERIVED.

UPSTREAM ARTIFACTS, read both before planning:
- Research: /home/benjamin/Projects/BimodalLogic/specs/686_modelchecker_contract_handoffs/reports/01_modelchecker-contract-handoffs.md
- Plan (6 phases, 5 waves, --strict PASS): /home/benjamin/Projects/BimodalLogic/specs/686_modelchecker_contract_handoffs/plans/01_modelchecker-contract-handoffs.md
The upstream research covered BOTH repositories with file:line and commit evidence; a fresh single-repo research round would be strictly weaker. Prefer adopting the upstream plan (revising for anything 205/206 have since changed) over authoring a new one.

WHAT IS ACTUALLY OUTSTANDING. Of six contract hand-off items originally assumed open, upstream research established that only two are real work here:

ITEM 6, A LOCATED DEFECT (do this first). code/src/model_checker/syntactic/sentence.py's store_types extremal-operator branch (around lines 238-240) keys off self.name being in {'\top','\bot'} -- the ORIGINAL operator name -- rather than the shape of the derived type. Consequence: \top's Imp-of-two-Bots expansion is silently truncated to (first_elem, None, None). Corroborating evidence already in-tree: examples.py's 'avoid TopOperator bug' workaround comments, and an exclusion in theory_lib/bimodal/tests/unit/test_formula.py's _BOX_TEST_CORPUS. The fix is to dispatch on the derived shape. Upstream planning bounded the blast radius: logos' \top/\bot are PRIMITIVE syntactic.Operators yielding a one-element derived type, so a shape-keyed branch in the shared syntactic/sentence.py is behavior-identical outside bimodal -- verify that claim, do not assume it, and run the FULL suite rather than the bimodal subset. Removing the _BOX_TEST_CORPUS exclusion is how the fix proves itself from the site that documented the defect.

ITEM 5, AN UNWIRED CONFORMANCE CHANNEL (depends on item 6). Nothing here consumes BimodalLogic's Tests/fixtures/sentence-translation-fixtures.jsonl -- zero references. Add an integration test asserting, per fixture row, that this repository's own update_types + formula.translate + to_json output equals the row's formula field COMPARED AS PARSED JSON, never as bytes (both repositories' docs require this). Natural home is theory_lib/bimodal/tests/integration/, following _lean_check.py's skip-resolution idiom. It depends on item 6 because at least one fixture row is a \top sentence. Assert the row count so a truncated or unreadable fixture fails loudly instead of passing vacuously, and give checkout-absence its own distinctly named skip. Read the fixture live from the resolved BimodalLogic checkout rather than mirroring a copy here: one source of truth cannot drift, and drift is what this channel exists to detect. The channel is forward-only (tr is not injective), so do not add an inverse formula-to-sentence pass.

ALREADY LANDED HERE, VERIFY ONLY, DO NOT REIMPLEMENT. Three items landed via tasks 197 and 207 (through commit ec430559) and need a verification pass, not source edits: the echo comparison (assert_echo_matches_sent is defined AND called in test_certificate_lean_agreement.py and test_semantics_core.py); ensure_ascii=False as the sole wire serializer (certificate.py's canonical_wire_bytes); and the acceptance absent-default of 'decided' in both consumers. Re-doing any of these at face value from a stale description is the main failure mode to avoid.

CLOSED WITH A NEGATIVE RESULT, NO WORK. An audit for an out-of-repository Lean consumer of the CheckResult.countermodel pattern match found no target anywhere on the machine: this repository contains zero .lean files, and no other checkout imports BimodalTools/CertificateImport/CanonicalWire. Record the negative result; do not re-open the search.

WHY THE DEPENDENCIES. Task 206 (refactor_verification_test_harness) is actively restructuring theory_lib/bimodal/tests/ including its README, which is where this task's new module and doc edits land. Task 205 (certifying_countermodel_architecture) edits _lean_check.py, tests/README.md, test_certificate_lean_agreement.py and test_semantics_core.py, and carries substantial acceptance-field work -- overlapping both this task's Phase 6 targets and its item-1/item-4 verification sites. Landing this task before either settles would collide on files neither declares in a file_scope. Sequence after both.

RELATED, NOT BLOCKING. BimodalLogic has separately catalogued citation drift in this repository's theory_lib/bimodal/docs/ADEQUACY.md -- four stale ZTimeSharpness.lean citations and an eight-citation wrong-declaration cluster in section 4.1's proof-mapping table, now seeded into its C35 manifest gate. Task 205 also edits ADEQUACY.md. See /home/benjamin/Projects/BimodalLogic/docs/reference/transcription-audit-surface.md for the corrections table. Coordinating that is out of scope here.

PROVENANCE NOTE. Because this task now lives in this repository under its own number, ordinary 'task 209: {action}' commit messages are correct. The upstream plan proposed a 'bimodal-contract:' prefix only to avoid falsely claiming a number in this repository's sequence; that workaround is no longer needed and should not be carried over.

CONSTRAINTS. This repository's working tree may carry concurrent in-flight work from other sessions. Stage only this task's own explicitly named files -- never a directory or glob pathspec, never git add -A, and never a destructive git command (reset --hard, checkout --, clean -fd, restore) while the tree is dirty. To revert a landed phase, git revert that phase's own commit. Do not write anything under /home/benjamin/Projects/BimodalLogic.

---

### 208. Fix logos subtheory meta test timeout
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: test-reliability
- **Dependencies**: None
- **Research**: [208_fix_logos_subtheory_meta_test_timeout/reports/01_logos-subtheory-meta-test-timeout.md]
- **Plan**: [208_fix_logos_subtheory_meta_test_timeout/plans/01_delete-duplicate-subtheory-meta-test.md]
- **Summary**: [208_fix_logos_subtheory_meta_test_timeout/summaries/01_fix-logos-subtheory-meta-test-timeout-summary.md]

**Description**: Fix the logos subtheory-orchestration meta-test, which sits over CI's per-test timeout ceiling with negative margin and duplicates coverage the gate already collects directly. This is a pre-existing condition, not a regression: it was observed intermittently failing and then passing across two runs of the same gate in the same working tree with no intervening code change, which is the signature of a test sitting exactly on its timeout boundary.

MEASURED EVIDENCE, CONFIRM BEFORE CHANGING ANYTHING. code/src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py::TestSubtheoryOrchestration::test_all_subtheory_tests_pass runs 320.90s in isolation on an idle host with no timeout flag applied. CI's gate (.github/workflows/tests.yml) runs with --timeout=300 --timeout-method=thread, so the isolated figure already exceeds the per-test ceiling by roughly 21 seconds. Across two runs of the full repository gate under CI's exact invocation shape on the same tree it both passed (3098 passed, 0 failed) and failed (1 failed, 3097 passed), which is consistent with a boundary case rather than a deterministic failure or an ordinary flake.

WHY IT COSTS WHAT IT COSTS. The test body is a serial for-loop over subtheory names that spawns a nested pytest per subtheory via subprocess.run with capture_output=True. Three consequences worth separating. It is serial by construction, so it gains nothing from -n 4 for its own runtime while still contending with the other three xdist workers for cores, which is why its wall time moves with overall system load. It carries NO pytest markers at all -- not slow, not xdist_serial, and no per-test timeout override -- so CI's marker expression selects it unconditionally. And it largely duplicates work: the subtheory test suites it shells out to are already collected and run directly by the same repository-wide gate, so the nested runs re-execute tests that have already passed in the parent session, making this plausibly the single most wasteful item in the suite.

WHAT TO DECIDE. Establish first whether this meta-test adds any coverage the direct collection does not. If the subtheory suites are fully collected by the gate already, the honest outcome may be deletion rather than optimization, and that should be stated plainly rather than avoided out of caution; if it does add something (an isolation property, a per-subtheory independence guarantee, a check that each suite passes standalone rather than only in aggregate), identify exactly what, and preserve that specific property by the cheapest means rather than by re-running every test in a subprocess. Compare at least: deleting it in favour of direct collection; replacing the subprocess loop with in-process collection checks that assert the independence property without re-executing; marking it xdist_serial or slow and moving it off the per-PR path to a scheduled run; and parallelising the subprocess loop. Measure before and after under CI's exact invocation shape, and report both numbers rather than an estimate.

CONSTRAINTS. Do not simply raise the timeout to make a 320-second test fit -- that hides the cost rather than addressing it, and the ceiling exists to bound total CI latency. Do not lose any assertion the meta-test currently makes without saying explicitly what was dropped and why it is safe. Verify against the full repository gate under CI's own invocation shape, since the fix changes what the gate selects. Check whether sibling theories carry the same nested-pytest meta-test pattern and report any found, but fix only logos here unless the same fix applies mechanically.

---

### 207. Fix stale all constraints snapshot
- **Status**: [COMPLETED]
- **Task Type**: z3
- **Topic**: architecture
- **Dependencies**: None
- **Research**: [207_fix_stale_all_constraints_snapshot/reports/01_fix-stale-all-constraints.md]
- **Plan**: [207_fix_stale_all_constraints_snapshot/plans/01_fix-stale-all-constraints.md]

**Description**: Fix ModelConstraints.all_constraints being a stale eager snapshot that misses everything bimodal's two-phase constraint emission adds after construction, and audit every production reader of it. This was surfaced as a side finding while strengthening the A2-triangle differential: that work needed the true post-solve constraint set, could not get it from all_constraints, and added a local full_constraints() reconstruction inside the test tree to work around it. The workaround is fine for tests; the underlying attribute is still wrong for every production reader, and those were explicitly left out of scope there.

ROOT CAUSE, ALREADY LOCALIZED -- CONFIRM, DO NOT RE-DERIVE. models/constraints.py:97 computes all_constraints once at construction as an eager list concatenation of frame_constraints + model_constraints + premise_constraints + conclusion_constraints. Bimodal's encoding is deliberately two-phase (its semantic/core.py documents this as decision D6): frame_constraints starts EMPTY and is only populated later by finalize_certificate(), once every boxed subformula is known. Because all_constraints is a concatenated snapshot rather than a view, it is computed while frame_constraints is still empty and never sees the (C1)-(C4) constraints that finalize_certificate installs. For bimodal specifically, all_constraints therefore omits the entire certificate encoding.

THE THREE PRODUCTION READERS TO ASSESS, EACH WITH A DIFFERENT SEVERITY.

First, and most likely to be a genuine defect: iterate/models.py:93 builds a fresh z3.Solver and adds every constraint from model_constraints.all_constraints as "the base constraints", then pins theory-specific values through the iterator hook, then at :152 overwrites model_constraints.all_constraints with list(temp_solver.assertions()). If the base set is missing (C1)-(C4), the solver the iterator builds is weaker than the one that produced the original model, so an iterated bimodal "model" may satisfy the pinning constraints while violating the certificate conditions the first solve enforced. Determine whether the theory-specific pinning hook (bimodal semantic/core.py's per-variable bit/guess/sel pinning) happens to mask this by fixing every free variable, or whether genuinely invalid iterated models are reachable. Construct a test that answers this rather than reasoning it out: the honest outcome may be either "unreachable, document why" or "reachable, here is the failing case".

Second: iterate/constraints.py:51-52 preserves original_constraints from the same attribute for iteration, inheriting the same gap.

Third, and user-visible but not a soundness issue: models/structure.py's _get_relevant_constraints (lines 429 and 435) returns all_constraints for the "SATISFIABLE CONSTRAINTS:" display and as the unsat-core fallback. For bimodal this prints a constraint set with the certificate encoding missing entirely, so verbose and saved output under-reports what was actually solved. Note that A2_GAP.md already records that models/structure.py's _setup_solver never reads all_constraints, so the solve path itself is not implicated -- state that explicitly in whatever fix lands, so a future reader does not over-read the severity.

FIX DIRECTION, TO BE DECIDED BY RESEARCH RATHER THAN ASSUMED. Compare at least: making all_constraints a computed property or view so it always reflects the current component lists rather than a construction-time snapshot; having finalize_certificate (and any other late emitter) maintain all_constraints as it mutates frame_constraints; and promoting the test tree's full_constraints() reconstruction into the production API and having readers call it. Weigh each against the fact that four theories plus the iterate engine read or append to this attribute, so a change to its semantics is cross-theory: logos, exclusion and bimodal all append to it from their own semantic cores. Whatever lands must not silently change behaviour for the theories that are single-phase and currently correct.

CONSTRAINTS. Verify against the full repository gate under CI's own invocation shape, not just the bimodal suite, because this attribute is cross-theory. Preserve the test tree's existing full_constraints() behaviour or migrate its callers deliberately -- the A2-triangle per-candidate comparison depends on it and must stay green. Do not narrow or weaken any existing assertion to accommodate a fix.

---

### 206. Refactor verification test harness
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: Task 207
- **Research**: [206_refactor_verification_test_harness/reports/01_refactor-verification-test-harness.md]
- **Plan**: [206_refactor_verification_test_harness/plans/01_refactor-verification-test-harness.md]
- **Summary**: [206_refactor_verification_test_harness/summaries/01_refactor-verification-test-harness-summary.md]

**Description**: Refactor the bimodal verification test harness for organization and performance, refactoring structure rather than preserving it where that produces a better result. This task owns the harness itself; the trust boundary between testing and formal verification is owned by a separate task and is explicitly out of scope here. Nothing in this task may weaken what the existing tests establish, and any narrowing of an enumeration must be stated explicitly rather than absorbed as a speedup.

ORGANIZATION. Verification support code currently sits inside the test tree as code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py (the compile-once pinned evaluator and the candidate-to-assignment builder) while behaving like a library rather than a test module. Tier membership is expressed in three places at once: prose in the module docstring of tests/integration/test_certificate_a2_triangle.py, per-class pytest markers, and a class-level skipif keyed on BIMODAL_LOGIC_PATH. Grid configurations and premise families are restated across tests/integration/test_certificate_a2_triangle.py, tests/integration/test_search_period_coverage.py, tests/unit/test_witness_registry.py and tests/unit/test_structure.py. Assess whether one declarative registry of tiers and configurations, consumed by every module, is better than the current distributed expression, and whether the evaluator belongs outside the test tree given that a separate task is evaluating promoting a checker onto the production path. Coordinate on that point rather than pre-empting it: if the evaluator may become a shipped artifact, say what that implies for its location and public surface, but do not make the promotion decision here.

PERFORMANCE. Authoritative measurements already exist and should be reproduced, not re-estimated from scratch. Under CI's exact invocation shape (pytest -n 4 --timeout=300 --timeout-method=thread over the real target set), the widest boxed Tier 1 case runs 123.29s over 10,485,760 candidates, which is 1.91x the aggregate-only baseline and leaves roughly 59 percent headroom against the 300s per-test ceiling; the second boxed case runs 17.77s over 1,572,864 candidates; the widest box-free case runs under 2s. The headroom assumes CI hardware no more than about 2.4x slower than the measuring host, a margin currently documented in TestExhaustiveTriangleWithBox's docstring. Decide whether that margin is adequate and compare at least four routes: moving the widest case off the per-PR path to a scheduled run while keeping the 17.77s case in the PR gate; sharing solved structures across cases through pytest fixtures instead of re-solving per test; caching or reusing the compiled evaluator across configurations; and any algorithmic reduction of the enumeration itself. Measure before and after under the same invocation shape, on the same host, and report both numbers. A scheduling change is a legitimate outcome and is not a retreat.

CONSTRAINTS. Preserve Tier 2's clean-skip behaviour as it stands (its promotion is the other task's decision, not this one's). Preserve the timeout-is-False assertions in the A0 standing tests and the search-coverage grid pins, which exist so an inconclusive solver run cannot pass as a genuine UNSAT. Preserve the retained aggregate assertion alongside the per-candidate comparison, since it is the only check of the real Z3 search verdict as distinct from the pinned constraint-set evaluation. Verify against the four-theory gate as well as the bimodal suite, and confirm the repository-wide target set stays green.

---

### 205. Certifying countermodel architecture
- **Status**: [COMPLETED]
- **Task Type**: formal
- **Topic**: architecture
- **Dependencies**: Task 197
- **Research**: [205_certifying_countermodel_architecture/reports/01_certifying-countermodel-architecture.md]
- **Plan**: [205_certifying_countermodel_architecture/plans/01_certifying-countermodel-architecture.md]
- **Summary**: [205_certifying_countermodel_architecture/summaries/01_certifying-countermodel-architecture-summary.md]

**Description**: Decide and stage how a reported countermodel becomes trustworthy in the hands of a user who has no Lean toolchain, and reposition the existing test tiers to match what each one actually establishes. Narrow scope deliberately: the proof-carrying acceptance mode and the deserialization trust base are owned by the certificate-wire hardening task and must be consumed here, not re-decided; the test-harness reorganization and its performance work are owned by the harness refactoring task. This task owns three things only -- the output gate, the checker's runtime availability, and the tier repositioning.

THE GOVERNING ASYMMETRY, WHICH IS THE RATIONALE FOR ALL THREE. A countermodel is a positive, checkable witness: whether a concrete structure falsifies a formula is finite and decidable, so a SAT verdict can be validated per run without trusting the encoder, the extraction or the solver. The absence of a countermodel has no witness, so an UNSAT verdict can only be trusted by proving the search complete (A2), the bounds adequate (A1/A3), and Z3's UNSAT sound -- and ADEQUACY.md section 7.4 already declines to make that claim, with a runtime fail-fast guard. Effort belongs where results are not independently checkable; testing covers where they are. Under a mandatory per-run check every encoder, extraction and solver defect becomes a liveness failure (a missed countermodel, or an error) rather than a soundness failure (a reported countermodel that is not one), and securing that is this task's purpose.

ALREADY SETTLED, DO NOT SPEND RESEARCH RE-ESTABLISHING IT. The Lean side's check_certificate is verdict-producing today, not entailment-producing: acceptance reports that four Decidable instances returned true on the family rebuilt from the wire input, which ADEQUACY.md section 6.2 already records and which the Lean development has its own task open to change. Take that as given.

ITEM 1, THE OUTPUT GATE. TestBoundedLeanCrossCheck in tests/integration/test_certificate_a2_triangle.py is a sampled test tier that clean-skips when BIMODAL_LOGIC_PATH is unset, so in a default CI run the only check validating a candidate countermodel against the semantics disappears entirely. Evaluate promoting that check from a sampled tier to a gate on reported output: a countermodel that has not been checked is either labelled unchecked or not reported at all. Assess what that does to the user-facing contract, to SETTINGS.md, and to section 7.4's existing guard, and say whether an interim gate over today's verdict-producing checker is worth shipping before the proof-carrying mode lands, or whether the weaker check would misrepresent its own strength.

ITEM 2, RUNTIME AVAILABILITY -- THE PRACTICAL BLOCKER, AND THE PART NOTHING ELSE SCOPES. A mandatory check must not imply a mandatory Lean toolchain for users, and no task in either repository currently scopes the packaging that makes this true. Evaluate extracting the checker to a standalone verified artifact shipped with the package (Lean's C backend, or an equivalent) against three alternatives: an optional two-tier trust model distinguishing an unchecked from a checked countermodel; a re-implementation in Python, which reintroduces the code-to-specification gap this task exists to avoid and should be costed as such rather than dismissed; and simply requiring the toolchain. Cost each including packaging, wheel size, platform coverage and CI implications, and recommend one with a staged path. This item does not wait on the proof-carrying mode and can be researched immediately.

ITEM 3, CONFIRM THE LEDGER REPAIR THAT HAS ALREADY BEEN APPLIED, AND EXTEND IT. Do NOT re-record the soundness/adequacy asymmetry or the trust base: docs/TRUST_PIPELINE.md already states both carefully, including that absence has no witness, that Z3, the encoder and the decoder are deliberately outside the trust base, and that the translation rather than the encoder is the weakest link. Three edits have ALREADY been applied to that document by the orchestrator and need verification rather than redoing: its stale "Widen the A2 grid to nb = nf = 2" remaining-work row was removed (the widened cases exist and pass); its "The standing test for A2" section no longer claims the test is blind to the one defect known to have occurred, and now records both the closed nb=2 blind spot with its measured cost and the move from an aggregate to a per-candidate leg (i)/(iii) comparison; and two new remaining-work rows were added for this task's own items 1 and 2. Confirm all three read correctly against what actually landed, and extend rather than duplicate them. What remains genuinely open for this item: state explicitly wherever the tiers are described that the Tier 1 differential and the search-coverage grid pins are liveness and regression evidence for the UNSAT direction rather than countermodel trust, reassess their cost on that basis, and cross-check SEARCH_COVERAGE.md and section 7.1's sub-bullet list for consistency. Nothing here licenses deleting or narrowing any test, and the retained aggregate assertion stays.

COORDINATION, NOT DEPENDENCY. No hard dependency edge is declared, because item 2 is independent and is the most valuable thing to start. But the wire's output contract, proof-carrying acceptance, and parse-echo verification belong to the certificate-wire hardening task; if this task's research reaches them it stops and defers rather than deciding. Expect documentation overlap on ADEQUACY.md sections 6.2 and 7.4 and on SETTINGS.md, and re-read before editing.

DEFERRED, NAMED SO IT IS NOT REDISCOVERED. A structural conformance check that the emitted Z3 constraint set matches the (C1)-(C4) schema instantiated at the configured bounds -- extending the existing operator-inventory and atom-coverage guards, linear in formula size rather than candidate space -- remains worthwhile but is UNSAT-direction work, explicitly sequenced after everything above. Record it as a follow-on with the reasoning; do not build it here.

Out of scope: the A1 compression bound, the divisor-period sweep driver, the harness reorganization and its performance work, the wire format and proof-carrying acceptance, and any change that weakens what the existing tests establish. Report any genuine encoder divergence as a finding rather than diagnosing it.

---

### 204. Strengthen a2 triangle per candidate
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None
- **Research**: [204_strengthen_a2_triangle_per_candidate/reports/01_strengthen-a2-triangle-per-candidate.md]
- **Plan**: [204_strengthen_a2_triangle_per_candidate/plans/01_strengthen-a2-triangle-per-candidate.md]
- **Summary**: [204_strengthen_a2_triangle_per_candidate/summaries/01_strengthen-a2-triangle-per-candidate-summary.md]

**Description**: Strengthen the A2-triangle encoding-completeness differential from an aggregate verdict to a per-candidate comparison. The leg (i) versus leg (iii) comparison is currently a one-bit existential at tests/integration/test_certificate_a2_triangle.py:238 -- (accepted > 0) == z3_model_status -- so up to 10.5 million enumerated candidates collapse into a single SAT/UNSAT agreement, while A2 is a claim about each candidate individually. A candidate the encoder wrongly rejects and the re-checker accepts, or the reverse, is invisible so long as the aggregate verdicts still agree. Compare the two legs candidate by candidate instead, reporting the first divergence with enough of the candidate to diagnose it. Keep the cost envelope in view: the widest configured closure already reaches 10.5 million candidates, so measure before committing to unconditional execution and tier or slow-mark the new comparison as the existing cases are, verifying against CI exact invocation shape (--timeout=300 --timeout-method=thread, run with -n 4) rather than a bare idle-host figure. Keep Tier 2 clean-skip discipline intact. Report any genuine divergence as a finding; diagnosing the encoder is out of scope. This is the lead recommendation of the encoder-specification proof-routes research, preferred over routes that attempt proof.

---

### 203. Research divisor period search coverage
- **Status**: [COMPLETED]
- **Task Type**: z3
- **Topic**: semantics
- **Dependencies**: None
- **Research**: [203_research_divisor_period_search_coverage/reports/01_divisor-period-search-coverage.md]
- **Plan**: [203_research_divisor_period_search_coverage/plans/01_divisor-period-search-coverage.md]
- **Summary**: [203_research_divisor_period_search_coverage/summaries/01_divisor-period-search-coverage-summary.md]

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
- **Status**: [BLOCKED]
- **Task Type**: z3
- **Topic**: semantics
- **Dependencies**: Task 193, Task 194, Task 197

**Description**: Extend the bimodal theory to the language with the stability modal, once the verified side supplies a state-sharing witness structure, its histories characterization, its redesigned box condition, and a compression bound. The modal is absent from this theory entirely today: operators.py defines negation, conjunction, disjunction, bottom, Box, Future, Past, Until, Since and the defined operators, with no stability modal, and ADEQUACY.md states it is out of scope throughout. Adding it is not an operator definition plus a truth clause. The received account of why this design is deterministic is explicit that the obstruction is not Limit or Saturation but the histories characterization and the box case of the truth lemma: determinism is what makes every world history one of the lasso orbits, so sharing states between lassos lets a history cross from one lasso to another, breaks that characterization and the corollary that the frame's history set is exactly the certified histories, and breaks box faithfulness, which is calibrated against "every position of every lasso" and stops enumerating the history set once histories recombine. Consequently this task's scope is: add the operator and its truth conditions; replace the certificate datatype with the verified side's branching structure; re-encode the conditions for Z3 over that structure, box faithfulness in particular, which can no longer be a conjunction over lasso positions; extend the wire contract and the re-checker in step, coordinating the breaking change with the producing side; and set search bounds from the new compression function. Also revisit the iteration machinery: the symmetry group for orbit-distinctness (rotation per lasso, permutation of witness lassos) is defined for a family of lassos and will need a different group action on a branching structure. BLOCKED on the four verified-side tasks (decidability provenance gate, state-sharing structure and box-condition redesign, agreement lemma over all walks, compression and assembly); until the agreement lemma lands there is no soundness argument for any certificate this encoding could emit, and emitting one anyway would violate the never-report-validity discipline in the opposite direction, by reporting countermodels nothing certifies.

---

### 199. Adequacy round trip ledger
- **Status**: [NOT STARTED]
- **Task Type**: markdown
- **Topic**: documentation
- **Dependencies**: Task 192, Task 193, Task 194, Task 195, Task 196, Task 197, Task 198, Task 211, Task 214

**Description**: Write the round-trip ledger in code/src/model_checker/theory_lib/bimodal/docs/: a single document stating, once and end to end, the biconditional between what the model checker reports and what paper models exist, with every leg's discharge cited and every residual named. The statement to record is the achievable one, not the desired one: that the search returns a certificate for a given premise/conclusion pair at lengths at or above f of the closure size if and only if the conclusion is not a Z-time consequence of the premises -- the forward direction being (SOUND), the backward being (ADEQ), and the frame class being Z-time rather than the paper's full consequence relation. For each leg, cite how it is discharged and by what kind of evidence, keeping the four categories distinct: machine-checked theorem, audit by inspection, decided per run, and property-tested. Cover at minimum: S1 (proved), S2 (an audit, narrowable but never a theorem), S3 (decided per run, twice, independently -- and record the consequence that the Z3 encoder, the decoder and Z3 itself are not in the soundness trust base, so encoder defects can cost completeness or raise a loud rejection but cannot manufacture a false countermodel report), S4 (the translation bridge), A0 (a permanent frame-class limit, not an open problem), A1 (BimodalLogic's compression theorem), A2 (encoding completeness) and A3 (bound realization). Close with the honest ceiling: three residuals no further work removes -- A0's frame-class gap, S2's irreducibly informal paper-to-formalism boundary, and the deciding procedure's scope covering the language without the stability modal. Documentation only: this task synthesizes and cites the work of the others rather than doing any of it.
CORRECTION to the closing section specified above: do not present the three residuals as alike. Two are permanent and no further work removes them -- the frame-class gap, and the irreducibly informal paper-to-formalism boundary of the transcription audit. The third, the deciding procedure's scope covering only the language without the stability modal, is NOT permanent: it is an open but scoped limitation with a named route, and a task chain now exists for it on both sides (verified side: a decidability-provenance gate, a state-sharing witness structure with the box condition redesigned, an agreement lemma over all walks, and a compression bound; this side: the theory extension that consumes them). State it as such, citing the obstruction accurately -- not Limit or Saturation, but the histories characterization and the box case of the truth lemma -- so a reader is not left believing the stability modal is excluded in principle when it is excluded pending identified work.
SCOPE CHANGE (the base document now exists). TRUST_PIPELINE.md has since been written in code/src/model_checker/theory_lib/bimodal/docs/, and it already delivers the pipeline walk-through, the four evidence kinds, the trust-base statement and its corollaries, the (ADEQ) component table, the cross-repository remaining-work tables, the stability-modal obstruction, and the three-residual ceiling with the permanent-versus-routed distinction this task's own CORRECTION above called for. This task is therefore no longer "write the ledger from scratch": it is to REVISE that document into a final per-leg ledger once the legs it describes have actually landed. The remaining delta is (a) a per-leg table giving each obligation its discharge citation as landed, rather than as planned, (b) replacing the forward-looking remaining-work tables with what was actually done and what was actually left, and (c) re-verifying every cited file, line and theorem name still resolves, since the Lean development reorganizes its directories periodically and a citation audit was already needed once. Do not duplicate the existing document; edit it.

---

### 198. A3 compute bounds from closure
- **Status**: [BLOCKED]
- **Task Type**: python
- **Topic**: semantics
- **Dependencies**: None

**Description**: Make bound realization (A3) a computation rather than an assumption: once BimodalLogic's compression theorem supplies a computable f of the closure size, have the search compute f(|C|) from the closure and set its own back, mid and fwd lengths from it, instead of taking them as user settings whose adequacy is assumed. ADEQUACY.md's assumption table records A3 as vacuous until A1 supplies f, so this task is the consumer of that result. Two deliverables beyond the arithmetic: first, report the distinction honestly in output -- a run at lengths at or above f(|C|) may say "exhaustive at this closure", while a run below it must keep saying only that no certificate was found within these bounds, never that the argument is valid, per section 7.4's never-report-validity rule. Second, keep the frame-class caveat attached: even at adequate lengths the conclusion available is Z-time relative, since A0 is a permanent limit, and BimodalLogic's own scope note records that the deciding procedure covers the language without the stability modal, its witness models being deterministic, on which that modal is trivial. BLOCKED on BimodalLogic's compression task (the Decidable ValidZTime quasimodel/ShiftSet route, whose item 1 is A1 and whose item 2 builds the candidate list over those same bounds); there is no f to read until it lands, and nothing here should invent one.

---

### 197. Harden certificate wire proof carrying
- **Status**: [COMPLETED]
- **Task Type**: z3
- **Topic**: semantics
- **Dependencies**: Task 196
- **Research**: [197_harden_certificate_wire_proof_carrying/reports/01_harden-certificate-wire-proof-carrying.md]
- **Plan**: [197_harden_certificate_wire_proof_carrying/plans/01_harden-certificate-wire-proof-carrying.md]
- **Summary**: [197_harden_certificate_wire_proof_carrying/summaries/01_harden-certificate-wire-proof-carrying-summary.md]

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
