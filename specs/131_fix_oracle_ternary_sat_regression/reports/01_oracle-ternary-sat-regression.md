# Research: Oracle Ternary-SAT "Regression" Is a Timeout-Budget Boundary Issue, Not a Semantic Change

## Summary

The prior task's classification of `test_all_sat_task_relation_ternary` as a "refactor-introduced
regression" does not survive controlled re-testing. Five isolated runs of the single failing test
— three on the current branch, two on a read-only `git worktree` pinned at the pre-refactor
baseline commit — all landed in the same **52.8s-58.9s** wall-clock band, comfortably close to but
under the test's own 60000ms SAT-search budget for `next_A`. No difference in central tendency
exists between the two commits. Every constraint-building function the oracle's pipeline touches
(`build_frame_constraints`, `build_grounded_abundance_constraints`,
`capped_skolem_abundance_constraint`, `build_forward_comp_constraint`, `build_converse_constraint`,
`build_nullity_identity_constraint`) is byte-identical between the baseline and HEAD, and the
`oracle/` tree itself has zero diff in the same range. The one behaviorally-relevant diff in this
range (`code/src/model_checker/models/structure.py`'s UNKNOWN-outcome classification) is proven
below to be a no-op for this specific test's None/not-None decision. The correct fix is to widen
the test's own timeout budget, not to hunt for a semantic bug in `code/` or `oracle/`.

## 1. Reproducing the failure at HEAD

Ran the single test three times in isolation (`ps aux | grep pytest` confirmed no other test
session competing at run time, beyond one leftover read-only worktree left by a sibling task —
see section 5):

```
PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src python3 -m pytest \
  oracle/bimodal_logic/tests/test_oracle_interface.py::TestTernarySerializationAll::test_all_sat_task_relation_ternary -v
```

| Run | Result | Wall clock |
|-----|--------|-----------|
| 1 | PASSED | 58.91s |
| 2 | PASSED | 58.47s |
| 3 | PASSED | 55.08s |

All three passed. All three landed within 5s of the test's own 60000ms budget for depth>0
formulas (`oracle/bimodal_logic/tests/test_oracle_interface.py:1048`:
`timeout = 60000 if depth > 0 else 10000`). This is not the "20x variance" pattern documented in
`code/docs/core/TESTING_GUIDE.md` section 8.6 for a *different*, simpler bimodal example — the
spread here is a much tighter ~7%, but it is centered close enough to the hard 60000ms cap that a
slightly slower run (more CPU contention, different Z3 internal search order, etc.) plausibly tips
over it. The prior task's own recorded failure at HEAD reproduces this exactly: its isolated re-run
of this test took **"1:00"** (~60s) before returning `None` — i.e., the same near-boundary
runtime, on the losing side of the cap instead of the winning side.

## 2. Ruling out (not just noting) the timeout hypothesis at the baseline commit

The decisive test: does the baseline commit actually run *faster*, or did it just get lucky on a
single sample? Built a read-only `git worktree` at `6cfb7f48` (removed after use, per the
task's constraint against checking out over the working branch) and ran the same single test
twice:

| Run | Result | Wall clock |
|-----|--------|-----------|
| 1 (baseline) | PASSED | 52.80s |
| 2 (baseline) | PASSED | 56.68s |

Combined across both commits, five runs, wall-clock range **52.80s-58.91s** — no separation between
"HEAD" and "baseline" populations; if anything HEAD's samples are marginally *higher* than
baseline's, but the two ranges overlap heavily and n=5 is nowhere near enough to call that a real
effect. **This is the same near-60s solve time at both commits.** The prior task's conclusion
("passes at baseline, fails at HEAD -> refactor-introduced regression") was drawn from exactly one
sample per commit — a coin flip on both sides of a shared boundary, not a reproducible difference.

## 3. Diff audit: is there *any* candidate semantic change in the exercised code path?

`git diff 6cfb7f48..HEAD --stat` restricted to `code/src/model_checker/theory_lib/bimodal`,
`code/src/model_checker/models`, and `oracle/` shows 17 changed files, but:

- **`oracle/` has zero diff in this range.** `provider.py` (the `Z3OracleProvider.find_countermodel`
  pipeline the test exercises), `translation.py` (`temporal_depth`, `json_to_prefix`), and the test
  file itself are unchanged.
- **`code/src/model_checker/theory_lib/bimodal/operators.py` has zero diff.** `DefNextOperator`
  (`\next`, defined as `Until(phi, Bot)` — the operator `next_A` in the test exercises) is
  unchanged.
- **The bimodal `semantic.py` -> `semantic/core.py` + `semantic/model.py` split (task 126 phases
  20-21) is a pure file move for the functions that matter here.** Extracted
  `build_frame_constraints`, `build_grounded_abundance_constraints`,
  `capped_skolem_abundance_constraint`, `build_forward_comp_constraint`,
  `build_converse_constraint`, and `build_nullity_identity_constraint` from both the baseline
  `semantic.py` and the HEAD `core.py`+`model.py` pair by function body (not by line number) and
  diffed them programmatically: **all six are byte-identical**, including the M>=3 MBQI-avoidance
  dispatch logic in `build_frame_constraints` (the "Task 114 fix" the oracle's own docstring
  references, exercised here since `next_A` has `temporal_depth=1` -> `M=max(1+2,3)=3`, exactly the
  M>=3 boundary).
- **The one real behavioral diff in range is `code/src/model_checker/models/structure.py`'s
  `solve()`/`re_solve()` UNKNOWN-outcome classification**, changed from:
  ```python
  if self.solver.reason_unknown() == "timeout":
      return self._create_result(True, None, False, start_time)
  return self._create_result(False, self.solver.unsat_core(), False, start_time)
  ```
  to:
  ```python
  if SolverResult.is_unsat(result):
      return self._create_result(False, self.solver.unsat_core(), False, start_time)
  return self._create_result(True, None, False, start_time)  # any UNKNOWN -> timeout
  ```
  **This diff cannot explain the test's None-vs-SAT outcome.** `_create_result`'s signature is
  `(is_timeout, model_or_core, is_satisfiable, start_time)`. For *any* UNKNOWN result under either
  the old or new code, `is_satisfiable` is `False` in both branches (only the `is_timeout` flag
  changes between the two UNKNOWN sub-cases). `Z3OracleProvider.find_countermodel`
  (`oracle/bimodal_logic/provider.py:255`) checks `if structure.timeout or not
  structure.z3_model_status: return None` — an `or`, so `not z3_model_status` alone (False in
  both old and new UNKNOWN paths) is already sufficient to return `None` regardless of which way
  `is_timeout` is set. The two code paths are observationally equivalent for this test. (The change
  is a real, independently-motivated soundness fix — the old code silently treated
  `reason_unknown() != "timeout"` UNKNOWN outcomes, e.g. Z3's actual `"canceled"` string on
  timeout, as if they were a de facto UNSAT — but it is not the cause of this test's failure.)
- Everything else in the diffed range (`__init__.py`, `utils/api.py`'s `get_theory` relocation,
  docs, new test files, `iterate.py`, `conftest.py`) is either doc/test-only or on a code path the
  oracle's `find_countermodel` pipeline does not call (`provider.py` imports `ModelConstraints`,
  `Syntax`, and the bimodal semantics/proposition/structure classes directly, never
  `model_checker.get_theory`).

**Conclusion**: no semantic change exists anywhere in the code path this test exercises. The
observed failure is fully explained by wall-clock variance around a tightly-set timeout, which
both commits share identically.

## 4. Why this specific case sits so close to its own budget

`next_A` is the only formula in `sat_formulas` with `temporal_depth > 0` (the others -
`atom_A`, `imp_A_B`, `and_A_B`, `diamond_A` - are depth-0 and get the 10000ms budget instead).
Depth 1 forces `M = max(1+2, 3) = 3`, which is exactly the boundary where
`Z3OracleProvider.find_countermodel`'s own docstring (`oracle/bimodal_logic/provider.py:80-94`)
says the disabled `task_restriction` constraint would otherwise blow up MBQI, and where
`build_frame_constraints` (per its Task 114 comment, byte-identical at both commits) dispatches to
the more expensive `capped_skolem_abundance_constraint`/`build_grounded_abundance_constraints`
path instead of the cheap M<=2 path. This is a known, inherently slow region of the solver's
search space — not new, not introduced by the refactor — and the test's 60000ms allowance for it
was set with essentially no margin (5 runs clustered at 88-98% of budget). This is precisely the
anti-pattern `code/docs/core/TESTING_GUIDE.md` section 8.6 warns against: "Do not derive `max_time`
from a measured solve time plus a small margin."

## 5. Dependency / environment questions (user focus for this batch)

Re-verified rather than assumed; all match the prior task's findings from `specs/127_close_oracle_suite_regression_baseline/reports/01_oracle-baseline-environment.md`, with nothing changed since:

- **`z3-solver` and `pytest`**: both importable/runnable from the interactive
  `/home/benjamin/.nix-profile/bin/python3` (the interpreter actually used for every run in this
  report) — `z3` imports fine (via `/nix/store/h99b4fiz9liwhpcxsfcg48qs4p2k2afl-python3-3.13.13-env/lib/python3.13/site-packages/z3`,
  a Nix-provided site-package, not pip-tracked, hence `pip show z3-solver` reports "not found" even
  though the import succeeds) and `pytest` reports version 9.0.3 via `pip show`.
- **`pytest-xdist` is still absent from this interactive interpreter** (`ModuleNotFoundError` /
  `importlib.metadata` reports it missing), confirming the sibling task's premise for *that*
  interpreter. It is **not** absent from the project's own environment: `flake.nix:66-72` still
  declares `pytest-xdist` inside `devPython` for `devShells.default`, and the previously-built Nix
  store derivation is still present and usable without any rebuild:
  `/nix/store/kykgmi6vxjzw76miazjf3yfn59kp7phd-python3-3.12.13-env`. No action needed beyond using
  `nix develop` (or that store path directly) for any run that needs `-n <N>` parallelism.
  `curl -sI https://pypi.org/simple/pytest-xdist/` returns `HTTP/2 200` right now too, so the
  "package index unreachable" premise is stale, though moot given the Nix path needs no install.
- **`oracle/` has no dependency manifest of its own** (`find oracle -maxdepth 2 -iname
  "pyproject.toml" -o -iname "requirements*.txt" -o -iname "setup.py"` returns nothing) — it relies
  entirely on the repo root's own dependency surface (`code/src` on `PYTHONPATH` for
  `model_checker`, plus the `bimodal_harness` sibling checkout for the oracle-interface tests
  specifically). Both were satisfied for every run in this report via
  `PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src`, and the sibling checkout is
  confirmed present on disk at `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness`.
- **One live observation worth flagging to the batch**: `git worktree list` shows a second,
  pre-existing read-only worktree at
  `/tmp/claude-*/scratchpad/baseline-wt` still checked out at `6cfb7f48` (detached HEAD),
  evidently left by a concurrent sibling task's agent (consistent with the recent
  "spawn tasks 131-133" commit dispatching parallel work). It was not created or touched by this
  research and was left alone. Its mere presence is a reminder that concurrent sessions are active
  in this sandbox right now — exactly the contention condition section 8.6 warns about — so
  another agent picking up the fix here should re-check `ps aux | grep pytest` immediately before
  timing anything.

## Recommended fix

**Do not modify `code/` or `oracle/bimodal_logic/provider.py`/`operators.py`/`core.py` — there is
no semantic bug there.** The fix belongs entirely in the test's own timeout budget:

- **File**: `oracle/bimodal_logic/tests/test_oracle_interface.py:1048`
- **Current**: `timeout = 60000 if depth > 0 else 10000`
- **Change**: widen the depth>0 branch to give real headroom over the observed ~53-59s typical
  solve time — e.g. `180000` (3 minutes), a ~3x margin over the observed maximum, consistent with
  TESTING_GUIDE 8.6's "set budgets generously, not tightly" guidance and its own worked example
  (30s budget over a ~1.7s-10s typical solve). A smaller bump (e.g. 90000-120000ms) would likely
  suffice given the observed 52.8-58.9s cluster, but 180000ms removes the boundary risk with
  margin to spare without meaningfully lengthening a passing run (the actual solve still finishes
  in ~55-59s; only the ceiling moves).
- Optional, non-blocking secondary note for a future task (not this one): the `next_A` case's
  ~55s solve time at M=3 is itself a slow spot in the solver's search (the MBQI-avoidance dispatch
  in `build_frame_constraints`); `build_grounded_abundance_constraints` was already tried as a
  faster M>=3 alternative per a prior task's note in that function's own docstring and "found it
  caused regressions for both" correctness and performance, so there is no known cheap win here —
  raising the timeout is the correct near-term fix, not a solver-performance rewrite.
- After the timeout bump, re-run this single test several times (5-10x) in isolation to confirm
  the new budget clears the observed variance band with margin, then let a follow-up task
  (continuing task 127's blocked baseline) re-run the full 550-test suite to confirm no other test
  in the suite has a similarly tight budget before promoting a clean baseline.

## References

- `oracle/bimodal_logic/tests/test_oracle_interface.py:1029-1070` (`TestTernarySerializationAll`,
  `test_all_sat_task_relation_ternary`)
- `oracle/bimodal_logic/provider.py:169-260` (`Z3OracleProvider.find_countermodel`)
- `code/src/model_checker/models/structure.py:210-267` (`solve()`, the UNKNOWN-classification diff
  analyzed and ruled out in section 3)
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (`build_frame_constraints` et al.,
  confirmed byte-identical to pre-refactor `semantic.py`)
- `code/docs/core/TESTING_GUIDE.md` section 8.6 ("Solver Timing Budgets and Machine Variance")
- `specs/127_close_oracle_suite_regression_baseline/reports/01_oracle-baseline-environment.md` and
  `specs/127_close_oracle_suite_regression_baseline/summaries/01_close-oracle-regression-baseline-summary.md`
  (prior task's environment findings, reconfirmed unchanged here, and the single-sample
  baseline/HEAD comparison this report supersedes)
