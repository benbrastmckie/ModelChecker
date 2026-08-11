---
next_project_number: 145
---

# TODO

## Task Order

*Updated 2026-08-11. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 143 | -- | oracle suite capacity |

**Grouped by Topic** (indented = depends on parent):

### Oracle Suite Capacity

143 [BLOCKED] — The gating oracle suite's serial pass (pass 2 of oracle/run-oracl

## Tasks

### 144. Fix oracle per formula solve timeouts
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: oracle suite capacity
- **Dependencies**: None
- **Research**: [144_fix_oracle_per_formula_solve_timeouts/reports/01_oracle-solve-cost-reduction.md]
- **Plan**: [144_fix_oracle_per_formula_solve_timeouts/plans/01_oracle-solve-cost-reduction.md]
- **Summary**: [144_fix_oracle_per_formula_solve_timeouts/summaries/01_oracle-solve-cost-reduction-summary.md]

**Description**: The gating oracle suite cannot reach a green Step 6 in code/scripts/verify-refactor.sh because a varying set of per-formula Z3 solves fails to decide within its budget. This is NOT machine contention and NOT a correctness regression: two full end-to-end gate runs, at load average 5.4-7.5 and at load average 1.57, both failed at Step 6, and the QUIETER run failed MORE (pass 1 failed on the quiet machine after passing under contention). Every failure is an OracleTimeoutError or its downstream conclusive-floor consequence, with disagreements=0 in both runs -- no semantic disagreement anywhere. Observed failures. Quiet run (load 1.57): pass 1 -- TestMixedFormulas::test_mixed_and_all_future_neg (OracleTimeoutError at 60000 ms) and TestTernarySerializationAll::test_all_sat_task_relation_ternary (OracleTimeoutError at 180000 ms); pass 2 -- TestMixedFormulas::test_mixed_and_box_next (OracleTimeoutError at 60000 ms). Contended run (load 5.4-7.5): pass 2 -- test_mixed_and_box_next plus test_cross_oracle_differential.py:656 conclusive floor miss (99 of 103 conclusive against floor 100, timeout_count=4). An earlier research-phase pass-2 remeasure showed the same 99-of-103 floor miss alone. test_mixed_and_box_next is the only signature common to both full-gate runs; it is marked @pytest.mark.xdist_serial and was historically characterized at ~44-45s, so it now sits at or over its 60s budget even on an idle machine -- the strongest single lead. Full evidence is preserved in specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/oracle-suite-step6-quiet-attempt.txt and oracle-suite-step6-contended-attempt.txt, with the classification argument in that task summaries/01_phase4-triage-record.md. This is option (b) from the originating capacity diagnosis: attack the cause by making the slow solves faster. It is semantic/encoding work on the Z3 formulation, not a budget change. HARD CONSTRAINT: this must NOT be resolved by widening any budget or lowering any floor. Do not raise SELF_SCAN_SOLVE_TIMEOUT_MS or the 60000/180000 ms per-solve budgets, do not lower MIN_CONCLUSIVE_GATING_FORMULAS or MIN_CONCLUSIVE_SCAN_FORMULAS, and do not xfail or skip the failing tests. A timeout is a budget/performance outcome that is never cleared by widening a solve budget (code/docs/core/TESTING_GUIDE.md sections 8.6 and 8.8); a floor miss is a signal to investigate, never a license to lower the floor. Establish first whether these solves have regressed in cost or were always marginal, then reduce their cost at the encoding level. Adjudicate inside nix develop only. Note that the pass-level ORACLE_PASS2_TIMEOUT budget is NOT implicated: pass 2 measured 958.58s and 847.38s against its 1800s budget in these same runs.

---

### 143. Decide oracle serial pass timeout capacity
- **Status**: [BLOCKED]
- **Task Type**: python
- **Topic**: oracle suite capacity
- **Dependencies**: Task 144
- **Research**: [143_decide_oracle_serial_pass_timeout_capacity/reports/01_serial-pass-capacity.md]
- **Plan**: [143_decide_oracle_serial_pass_timeout_capacity/plans/01_formalize-capacity-decision.md]
- **Summary**: [143_decide_oracle_serial_pass_timeout_capacity/summaries/01_phase4-triage-record.md]

**Description**: The gating oracle suite's serial pass (pass 2 of oracle/run-oracle-suite.sh, ORACLE_PASS2_TIMEOUT default 900s) now runs at 96.6% of its budget: a measured '14 passed, 592 deselected in 869.58s' leaves only 30.4 seconds of slack. This is expected to flake on a loaded machine, and that measurement was itself taken under rising system load (6.48 -> 11.19). For calibration the same pass took 795.70s with 10 tests and 770.48s with 11 tests; it now carries 14. The cause is legitimate rather than accidental: four genuinely slow solves were deliberately routed into the contention-free serial pass via @pytest.mark.xdist_serial to fix real -n 6 CPU-contention failures -- test_mixed_and_box_next (~44-45s) and three BM_CM_4 cases (~15-24s each). Scheduling was the correct fix and nothing was weakened to obtain the current green. But the serial pass now carries more work than when its 900s budget was set, and that budget was never revisited. Decide the capacity question deliberately and record the reasoning. Options, from the originating diagnosis report: (a) raise ORACLE_PASS2_TIMEOUT as an honest capacity adjustment; (b) attack the cause by making those four solves faster, which is semantic work on the encoding rather than a budget change; (c) accept and monitor, treating a pass-2 timeout as a capacity signal rather than a correctness regression. Option (a) is the lowest-effort durable fix and was recommended, PROVIDED it is done as a deliberate decision with the reasoning recorded -- not as an incidental fix during unrelated work. Before deciding, re-measure pass 2 on a genuinely quiet machine, since the 869.58s figure is contaminated by concurrent load and likely overstates the steady-state cost. Adjudicate inside 'nix develop' only. ALSO OWNS RE-PINNING THE GATE'S COLLECTION COUNTS. The end-to-end run of code/scripts/verify-refactor.sh is now green on Steps 1, 2, 4, 5, 6 and 7 but reports 2 FAILED checks at Step 3: 'oracle gating-parallel collection count is 590, expected exactly 594' and 'oracle xdist_serial collection count is 14, expected exactly 10'. These are not regressions. They are the pins correctly detecting the deliberate relocation of four genuinely slow solves out of the parallel pass and into the serial pass. The suite total is unchanged at 606 and the partition invariant still holds (590 + 14 + 2 = 606). The gate's own failure message prescribes the remedy: 're-pin all four BASELINE_ORACLE_* values together'. This was deliberately NOT done when the markers landed, to avoid pinning twice: if this task's capacity decision raises ORACLE_PASS2_TIMEOUT, or moves tests back out of the serial pass, or makes those solves fast enough to return to the parallel pass, the distribution changes again. Re-pin ONCE, after the capacity decision is settled and the final distribution is known, updating all four BASELINE_ORACLE_* values together and re-running the full gate to confirm 'All checks passed'. Note that re-pinning to match an intentional redistribution is not a weakening: the pins remain exactly as strict and will still fail on any future unintended change. Do not, however, relax the partition check or the total.

---

### 142. Surface oracle timeout skips and run exhaustive scan
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: oracle verification coverage
- **Dependencies**: None
- **Research**: [142_surface_oracle_timeout_skips_and_run_exhaustive_scan/reports/01_oracle-timeout-skips-scan.md]
- **Plan**: [142_surface_oracle_timeout_skips_and_run_exhaustive_scan/plans/01_surface-oracle-timeout-skips.md]
- **Summary**: [142_surface_oracle_timeout_skips_and_run_exhaustive_scan/summaries/01_surface-oracle-timeout-skips-summary.md]

**Description**: Two categories of oracle verification currently produce no signal in the gating suite, and both hide real information about where the bimodal Z3 encoding is too slow to decide. (1) TIMEOUT-CONDITIONAL SKIPS: oracle/bimodal_logic/tests/test_oracle_interface.py converts an OracleTimeoutError into pytest.skip() at two sites (around lines 635 and 779) rather than failing. The rationale is correct -- a timeout is a budget/performance outcome, not a semantic regression -- but the consequence is that formulas the oracle cannot decide within budget disappear silently inside a green run. Worse, the first site's own skip message states that the affected example's ACTIVE_EXAMPLES expected_sat 'may itself have been measured under the old timeout-conflated contract', i.e. a recorded expectation may be wrong and nothing will ever report it. Make these skips visible and actionable: enumerate which formulas actually skip on a quiet machine, and for each, determine whether its recorded expected_sat is trustworthy or was measured under the old contract. Produce a prioritized worklist of formulas whose encoding needs performance work. Do NOT convert the skips into failures as a way of 'surfacing' them, and do NOT widen any timeout to make them decide -- the point is to measure and record, not to move budgets. (2) EXHAUSTIVE SCAN NEVER RUNS: oracle/run-oracle-suite.sh deselects '@pytest.mark.slow' from BOTH of its passes, so the exhaustive complexity<=5 self-consistency scan (oracle/run-oracle-exhaustive-scan.sh) runs only when invoked by hand, which nothing automated does. Run it on a quiet machine, record its result and runtime, and recommend whether it should be gated, scheduled periodically, or left manual -- with the cost in wall-clock time stated. Also worth checking while in this area: bimodal.get_theory(config) accepts a config argument and ignores it entirely (its own docstring says 'currently unused'), so a caller passing ['extensional'] silently receives the full bimodal theory including all temporal and modal operators. That makes a nominally trivial extensional example solve over a world-history x time search space. Assess whether any caller relies on the restriction that does not happen, and either implement the restriction or make the argument fail loudly. Adjudicate everything inside 'nix develop' only -- bare-PATH python gives false greens on this repo, including from missing test plugins, not just interpreter version differences.

---

### 141. Triage the 9 stale local-only branches, salvage anything of value, then retire them
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: architecture
- **Dependencies**: None
- **Research**: [141_triage_stale_local_branches_and_salvage_value/reports/01_stale-branch-triage.md]
- **Plan**: [141_triage_stale_local_branches_and_salvage_value/plans/01_stale-branch-retirement.md]
- **Summary**: [141_triage_stale_local_branches_and_salvage_value/summaries/01_stale-branch-retirement-summary.md]

**Description**: Nine local branches predate the repository restoration and have never been merged or pushed. Decide what in them is still worth keeping, extract exactly that, and only then retire them. Do NOT open by deleting branches.

WHY THIS IS NOT A CLEANUP CHORE: every one of these branches is local-only. A check against the remote confirms none of them exists on origin -- origin carries a different, older set (exclusion_attempt_9, false_premise, finean_exclusion, iterate, new_defined_operator, old_jupy, pre-full-skolem, reduced_exclusion, refactor_exclusion_single_strategy). So for these nine, the local clone is the ONLY copy in existence. `git branch -D` on any of them puts its history beyond reach once gc runs.

THE BRANCHES (last commit date; commits not reachable from current HEAD):
  bimodal_refactor                   2025-10-02   2046
  feature/bimodal-cvc5-pilot         2025-11-05   2066
  feature/bimodal_witness            2025-09-24   1992
  feature/bimodal_witness_backup     2025-09-23   1978
  feature/cvc5-feasibility-test      2025-10-02   2050
  feature/quantifier-free-witnesses  2025-10-02   2051
  feature/witness-falsity-attempt    2025-10-02   2047
  new_claude                         2026-01-10   2108
  refactor/exclusion                 2025-10-01   2049

READ THE COUNTS CORRECTLY -- they are the single easiest thing to get wrong here. The ~2000-commit
figures are NOT two thousand commits of unique work. They are inflated by an old divergence point:
main-line development was rebuilt during the restoration effort, so almost the entire shared
history now reads as "not reachable from HEAD". The genuinely distinct content on each branch is
very likely a small fraction of that. Establish the real delta per branch (diff against the merge
base, not the commit count) BEFORE judging any branch's worth. A triage that treats 2046 as
"2046 commits of lost work" will reach the wrong conclusion on every branch.

THEMATIC GROUPING, for cheaper triage -- five of the nine concern one line of inquiry (bimodal
witness predicates and quantifier-free encodings: bimodal_refactor, feature/bimodal_witness,
feature/bimodal_witness_backup, feature/quantifier-free-witnesses, feature/witness-falsity-attempt),
two concern a cvc5 solver evaluation (feature/bimodal-cvc5-pilot, feature/cvc5-feasibility-test),
one is an exclusion-theory refactor (refactor/exclusion), and one is a docs/tooling branch
(new_claude, and the most recent of the set at 2026-01-10). Triage by theme rather than
branch-by-branch; within a theme the later branch usually supersedes the earlier.

SPECIFIC THING TO LOOK FOR: the cvc5 branches represent an alternative-solver investigation that
has no counterpart in the current tree. Whether or not the code is reusable, the FINDING (does
cvc5 handle the countermodel examples Z3 struggles with, and at what cost) may be worth preserving
as a short written record even if every line of code is discarded. The same applies to
feature/witness-falsity-attempt, whose name suggests a recorded negative result. A negative result
that is cheap to write down and expensive to rediscover is exactly the kind of thing that should
survive a branch deletion.

WORK:
  1. For each branch, compute the real delta against its merge base with master, not the raw
     commit count. Classify each as: (a) superseded by the restoration, (b) contains reusable
     code, (c) contains a finding worth recording even though the code is dead, or (d) unclear.
  2. For (b), port the specific change onto a working branch off current master, with tests, as
     ordinary work -- do not merge the stale branch wholesale. These branches diverge from before
     the restoration and a wholesale merge would reintroduce superseded structure.
  3. For (c), write the finding into the appropriate place under docs/ or as a short design note.
     Cite what the branch demonstrated and why the code was not kept.
  4. For (d), say so explicitly and keep the branch. "Unclear" is a legitimate terminal state
     here; it is strictly better than a guess that destroys the only copy.
  5. ONLY after 1-4 are recorded, retire the branches judged (a) or fully salvaged under (b)/(c).
     Before deleting any branch, write it to a git bundle outside the repo and verify the bundle
     restores (`git bundle verify`), so retirement stays reversible even after gc.

HARD CONSTRAINTS:
  - Do not delete any branch before its triage verdict is recorded in this task's artifacts.
  - Do not push or delete anything on origin. Remote branches are out of scope for this task.
  - Do not merge a stale branch directly into master.

VERIFICATION BAR:
  - Every one of the nine branches has a recorded verdict with its measured real delta.
  - Any branch deleted has a verified bundle, and the bundle's location is recorded here.
  - Anything classified (c) has its finding written down somewhere a future reader will find it
    without knowing the branch ever existed.

---

### 140. Fix bimodal order dependence and oracle timeouts
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: bimodal/oracle residual defects
- **Dependencies**: None

**Description**: Diagnose and fix the residual RED that plan v2 of the refactor-verification gate (`code/scripts/verify-refactor.sh`) correctly and honestly reports at Steps 4, 6, and 7 -- pre-existing product defects the refactor did not introduce and whose diagnosis was an explicit non-goal of both the refactor task and the oracle-suite rebaseline task. This task owns that residual RED and carries forward all five of the following items, none of which may be dropped or merged away: 1) `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_cases[BM_CM_1-example_case7]` fails on both attempts inside `nix develop`, and is the same example case as the oracle-side `test_regression_all_active_examples[BM_CM_1-example_case7]`. 2) The bidirectional order-dependence / cross-test state leakage finding: the bimodal example-case tests are order-dependent in both directions, independent of environment. `BM_CM_1-example_case7` passes alone in 8.36s but fails inside the full `bimodal/tests/` run under `nix develop`; conversely `BM_CM_2-example_case8` and `BM_CM_4-example_case9` pass inside the full run but fail reproducibly ("2 failed, 41 passed", twice) when `test_bimodal.py` is run alone -- which is exactly how `compare_bimodal_baseline.sh` invokes it. This is the sharpest handle on the defect: deterministic, fast, and environment-reproducible. Start here. 3) `code/scripts/compare_bimodal_baseline.sh`'s masking defect: it runs its pytest pipeline under `set -euo pipefail` (line 7), pytest exits 1, and the script aborts after printing only "Running bimodal test suite..." -- so the verification gate's message "compare_bimodal_baseline.sh reported regressions" is misleading because nothing was ever compared. Fixing the masking does not make the step green: the recorded baseline is 43 passing and the current isolated run yields 41, which trips the script's own "REGRESSIONS DETECTED: 2 fewer passing tests" branch (line 66) regardless. 4) The two pass-1 oracle `OracleTimeoutError` failures, `test_mixed_and_box_next` and `test_mixed_and_all_future_neg`, plus the 900s non-termination of `test_temporal_propositional_interleaving` in pass 2, all recorded across two independent quiet-machine runs of the gating oracle suite (`oracle/run-oracle-suite.sh`). 5) The environment warning: adjudicate all of the above only inside `nix develop`. On bare-PATH python (3.13.13), Step 4 of the verification gate passes 298/298 and looks fixed; inside `nix develop` (python 3.12.13, same z3 4.16.0, xdist 3.8.0), it reliably fails. Any "it is fixed now" claim originating from a bare-PATH run is an artifact and must be rejected. Hard constraints inherited verbatim: this task may fix the underlying defects, but it may not weaken, widen, delete, or relax any pin, timeout budget, conclusive floor, xfail marker, assertion, `strict=True` requirement, or guard anywhere in the repository to reach a green result -- including in `code/scripts/verify-refactor.sh`, `oracle/bimodal_logic/tests/test_oracle_interface.py`, or `code/scripts/compare_bimodal_baseline.sh`. The gating oracle suite must continue to be described as RED until Step 6 is genuinely green end to end.
