---
next_project_number: 184
---

# TODO

## Task Order

*Updated 2026-09-01. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 154,176,183 | -- | semantics, test-reliability |
| 2 | 172,178 | 176 | test-reliability |

**Grouped by Topic** (indented = depends on parent):

### Semantics

154 [NOT STARTED] — THE PAYOFF, and the one task in this group where OVER-CLAIMING is

### Test Reliability

176 [BLOCKED] — TestShiftClosure::test_shift_closure_on_extracted_worlds_m3 at or
  └─ 172 [BLOCKED] — Three tests in oracle/bimodal_logic/tests/test_soundness_regressi
  └─ 178 [BLOCKED] — Fix the 4-6x solver-cost regression that commit f9cc081e introduc
183 [NOT STARTED] — Discriminate axiom-driven solver cost from host contention as the

## Tasks

### 183. Discriminate gating shortfall axiom vs contention
- **Effort**: 2-4 hours
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: test-reliability
- **Dependencies**: None

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
- **Dependencies**: Task 176

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
- **Dependencies**: None
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
- **Dependencies**: Task 176
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
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: semantics
- **Dependencies**: Task 152, Task 153

**Description**: THE PAYOFF, and the one task in this group where OVER-CLAIMING is the principal risk. With the frame axioms in place, the paper's `thm:extension` becomes applicable to bimodal countermodels: every partial history the solver finds is a fragment of a genuine total world history in $H_\F$. Use that to move work out of the solver -- but only the half the theorem actually covers.

WHAT THE THEOREM BUYS. Today the solver is made to approximate totality inside the search: `world_interval_constraint` gives each world a time interval, `lawful` chains unit steps across it, and the `capped_skolem_abundance_constraint` / `depth_bounded_skolem_abundance_constraint` family manufactures time-shifted copies. The extension theorem says the interval-and-shift scaffolding is not needed in order to KNOW that a found history is realizable: any partial assignment consistent with the frame axioms already lies inside some total history. So the solver may search genuinely small partial structures -- fewer worlds, narrower windows, no shift closure -- with totality discharged afterwards.

WHAT IT DOES NOT BUY. This must be stated in the code and in the summary, not only here. `thm:extension` is EXISTENTIAL. It certifies that a witness exists; it says nothing about universal obligations. Truth of `\Box \phi` quantifies over all of $H_\F$, and truth of `\Future \phi` and `\Past \phi` over all of $\D$, whereas `NecessityOperator.true_at` currently quantifies over the solver's finite world set and the tense operators over the bounded window. The abundance constraints approximate that second column and the extension theorem DOES NOT REPLACE THEM. Any design that drops abundance wholesale and cites `thm:extension` as cover is wrong. The preceding audit's baseline records exactly which examples this bites; use it.

DELIVERABLE 1 -- POST-HOC CERTIFICATION. After extraction, take the countermodel's partial histories and produce the finite lasso witness of BimodalLogic 441 (prefix plus cycle, forward and backward), verify that it satisfies the frame axioms and agrees with the extracted window, and attach it to the model structure. This is the concrete, checkable form of the claim "this bounded history is a fragment of a possible world", and it replaces the prose assurance currently carried in the `task_restriction` soundness comment.

DELIVERABLE 2 -- SPLIT THE CONSTRAINT SET BY POLARITY. Formulas whose falsification obligations are purely existential -- no `\Box` or universal tense operator in a verifying position -- need no abundance closure and can be searched at smaller `M` with fewer worlds. Formulas carrying universal obligations keep the current treatment. Drive this off the EXISTING `temporal_depth` machinery, which already performs depth-aware abundance selection, rather than adding a second parallel mechanism beside it.

DELIVERABLE 3 -- MEASURE IT. The claim here is a performance claim as well as a soundness claim. Report solve times against the audit baseline for the examples in each polarity class, and report honestly if the win turns out to be small or absent. A correct-but-slower result is a legitimate outcome and should be reported as such rather than tuned until it looks good.

DELIVERABLE 4 -- SURFACE THE CERTIFICATE. A user who gets a bimodal countermodel should be able to see the extension witness, not just the bounded window. Fit this to the existing output conventions rather than inventing a new output channel.

REGRESSION PROCEDURE. Use `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/README.md` for the concrete re-run/diff procedure against the audit's baseline; the `task_restriction` soundness comment this task's Deliverable 1 replaces the prose assurance of is assessed standalone in `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/02_task-restriction-verdict.md` (verdict: independent gap, not subsumed by the frame-axiom task).

DEPENDENCIES. The frame-axiom task (without *Seriality* and interpolation the extension theorem does not apply at all), the audit task (baseline), and BimodalLogic 441 (the lasso construction and the agreement lemma, including its explicit statement of what does not transfer).
