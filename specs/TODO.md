---
next_project_number: 142
---

# TODO

## Task Order

*Updated 2026-08-10. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 140,141 | -- | architecture, bimodal/oracle residual defects |

**Grouped by Topic** (indented = depends on parent):

### Architecture

141 [NOT STARTED] — Nine local branches predate the repository restoration and have n

### Bimodal/Oracle Residual Defects

140 [NOT STARTED] — Diagnose and fix the residual RED that plan v2 of the refactor-ve

## Tasks

### 141. Triage the 9 stale local-only branches, salvage anything of value, then retire them
- **Status**: [NOT STARTED]
- **Task Type**: general
- **Topic**: architecture
- **Dependencies**: None

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
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: bimodal/oracle residual defects
- **Dependencies**: None

**Description**: Diagnose and fix the residual RED that plan v2 of the refactor-verification gate (`code/scripts/verify-refactor.sh`) correctly and honestly reports at Steps 4, 6, and 7 -- pre-existing product defects the refactor did not introduce and whose diagnosis was an explicit non-goal of both the refactor task and the oracle-suite rebaseline task. This task owns that residual RED and carries forward all five of the following items, none of which may be dropped or merged away: 1) `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_cases[BM_CM_1-example_case7]` fails on both attempts inside `nix develop`, and is the same example case as the oracle-side `test_regression_all_active_examples[BM_CM_1-example_case7]`. 2) The bidirectional order-dependence / cross-test state leakage finding: the bimodal example-case tests are order-dependent in both directions, independent of environment. `BM_CM_1-example_case7` passes alone in 8.36s but fails inside the full `bimodal/tests/` run under `nix develop`; conversely `BM_CM_2-example_case8` and `BM_CM_4-example_case9` pass inside the full run but fail reproducibly ("2 failed, 41 passed", twice) when `test_bimodal.py` is run alone -- which is exactly how `compare_bimodal_baseline.sh` invokes it. This is the sharpest handle on the defect: deterministic, fast, and environment-reproducible. Start here. 3) `code/scripts/compare_bimodal_baseline.sh`'s masking defect: it runs its pytest pipeline under `set -euo pipefail` (line 7), pytest exits 1, and the script aborts after printing only "Running bimodal test suite..." -- so the verification gate's message "compare_bimodal_baseline.sh reported regressions" is misleading because nothing was ever compared. Fixing the masking does not make the step green: the recorded baseline is 43 passing and the current isolated run yields 41, which trips the script's own "REGRESSIONS DETECTED: 2 fewer passing tests" branch (line 66) regardless. 4) The two pass-1 oracle `OracleTimeoutError` failures, `test_mixed_and_box_next` and `test_mixed_and_all_future_neg`, plus the 900s non-termination of `test_temporal_propositional_interleaving` in pass 2, all recorded across two independent quiet-machine runs of the gating oracle suite (`oracle/run-oracle-suite.sh`). 5) The environment warning: adjudicate all of the above only inside `nix develop`. On bare-PATH python (3.13.13), Step 4 of the verification gate passes 298/298 and looks fixed; inside `nix develop` (python 3.12.13, same z3 4.16.0, xdist 3.8.0), it reliably fails. Any "it is fixed now" claim originating from a bare-PATH run is an artifact and must be rejected. Hard constraints inherited verbatim: this task may fix the underlying defects, but it may not weaken, widen, delete, or relax any pin, timeout budget, conclusive floor, xfail marker, assertion, `strict=True` requirement, or guard anywhere in the repository to reach a green result -- including in `code/scripts/verify-refactor.sh`, `oracle/bimodal_logic/tests/test_oracle_interface.py`, or `code/scripts/compare_bimodal_baseline.sh`. The gating oracle suite must continue to be described as RED until Step 6 is genuinely green end to end.
