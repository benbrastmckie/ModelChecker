# Phase 4: Root-Cause Attribution

## Method

`z3_version_pinned = 4.16.0` (Phase 3 found no flip across any tested version, so no repinning
needed; nixpkgs' installed 4.16.0 doubles as the "no drift found" control). Bisection performed
via isolated `git worktree` checkouts (never touching the shared main working tree, since this
task runs alongside other concurrent agent sessions in the same repo) at the candidate commits,
running `repro_m3.py` against each worktree's `code/src` under a clean, single-process,
zero-contention environment (no `pytest-xdist`, no other test running concurrently).

## Bisection Results

| Commit | Description | Environment | Result | rlimit_count | wall_seconds |
|---|---|---|---|---|---|
| `c8821e96` | task 172's originally-observed-failure commit (2026-08-31 12:05) | isolated single-process | **SAT** | 7,850,279 | 8.2039 |
| `f9cc081e^` | immediately before task 153 phase 4 (parent of `f9cc081e`) | isolated single-process | **SAT** | 7,850,279 | 3.2607 |
| `f9cc081e` | task 153 phase 4: Skolemized Seriality/Interpolation landed (2026-08-31 13:35) | isolated single-process | **UNKNOWN/canceled** | 29,028,028 | 15.0004 |
| HEAD (`6686356f`) | current | isolated single-process | **UNKNOWN/canceled** (5/5 runs, Phase 1) | 32.5M-46.5M | 15.0003-15.0070 |

`c8821e96` and `f9cc081e^` produce **byte-identical `rlimit_count`** (7,850,279) despite different
wall-clock times (8.20s vs 3.26s) -- confirming the underlying constraint work is unchanged
between them (consistent with Phase 2's finding that no semantic-affecting commit landed in that
window; task 153 phases 1-3, `36afcf30`/`ad660b72`/`b7bc19c3`, are harness/RED-test-only per their
own commit messages and do not touch `build_frame_constraints`).

The `f9cc081e^` -> `f9cc081e` transition (task 153 phase 4's own diff, isolated to exactly the two
new axioms) **flips the verdict from SAT to UNKNOWN/canceled** and **roughly quadruples
`rlimit_count`** (7.85M -> 29.0M) in a zero-contention, single-process environment where wall-clock
noise cannot explain a deterministic-metric jump of that size. This is a direct, reproducible,
bisection-isolated causal link: `f9cc081e`'s `build_seriality_constraint()` and
`build_interpolation_constraint()` additions are **a genuine, machine-load-independent cost
regression** for this exact formula.

## Reconciling the Pre-153 Timeline (the plan's required check)

The plan is explicit that `f9cc081e` (13:35) postdates task 172's 2/2 recorded failures at
`c8821e96` (12:05) and the spawn analysis (`3224df24`, 12:14), so `f9cc081e` **cannot be the sole
or original cause** of those specific observed failures. The bisection above is consistent with,
not contradictory to, that timeline: at `c8821e96` itself, this task's own clean single-process
re-run finds **SAT in 8.20s** -- not a failure. The rlimit (7.85M) is small and identical to
`f9cc081e^`'s, i.e. the code at `c8821e96` was never the over-budget encoding HEAD has now; it was
already close to budget (8.2s against a 15s ceiling, consistent with the task description's
recorded "2-8s historical headroom" -- 8.2s sits at the top of that documented range, not outside
it).

**Attribution for the original (pre-153) 2/2 failures**: task 172's own full-suite runs used
`bash oracle/run-oracle-suite.sh` pass 1, which is `pytest-xdist -n 6` -- six concurrent worker
processes competing for CPU. A formula whose rlimit-bound work takes 8.2s single-process can
plausibly exceed 15s wall-clock under 6-way parallel CPU contention -- the exact same *mechanism*
(machine-load-dependent wall-clock timeout) task 172 was created to fix, but reaching this test via
a different code path (`BimodalStructure`'s own `max_time`/`solver.set_timeout()`, not
`find_countermodel()`/`timeout_ms=5000`) than task 172's `xdist_serial` remedy addresses -- which is
exactly why the spawn analysis in the first place ruled this test outside task 172's mechanism and
spawned this task. This task's own single-process bisection cannot directly re-create parallel
contention (that would require re-running the full 6-way suite at each candidate commit, which is
far outside this phase's budget), so this attribution is recorded as **the best-supported
explanation given the evidence, not independently re-measured contention data** -- it is
consistent with every fact this task has gathered (identical rlimit at `c8821e96` and `f9cc081e^`,
8.2s wall time at the very top of the documented 2-8s range, and task 172's own full-suite
`-n 6` methodology) but is not itself a new contention measurement.

## Two-Cause Verdict

1. **Original 2/2 failures (pre-153, `c8821e96`/`3224df24`)**: attributed to **CPU contention
   under `pytest-xdist -n 6` parallel execution** pushing an already-near-budget formula (8.2s
   single-process, matching the documented 2-8s historical range) past the 15s wall-clock ceiling.
   Not a code defect at that commit -- confirmed SAT, correctly, in isolation.
2. **Current HEAD failure (post-153, deterministic 5/5 even single-process, zero contention)**:
   attributed to `f9cc081e`'s `build_seriality_constraint()` and `build_interpolation_constraint()`
   additions, which roughly quadruple this formula's `rlimit_count` (7.85M -> ~29-46M) --
   a genuine, machine-load-independent cost regression, isolated by direct bisection to that single
   commit's diff. This is now the **sole and sufficient explanation for HEAD's failure**: HEAD's
   failure reproduces deterministically without any contention (Phase 1's 5/5 single-process runs).

## Consistency with Task 153's Own Recorded Observation

`f9cc081e`'s own commit message records "a pre-existing MBQI pathology in
`capped_skolem_abundance_constraint`'s bare-satisfiability check at M=3, confirmed present
pre-Phase-4 too" (worked around there with `temporal_depth=0`). This is a **different function**
(`capped_skolem_abundance_constraint`, the M<=2/no-depth-bound path) than the one this task's
formula dispatches to (`depth_bounded_skolem_abundance_constraint`, since `temporal_depth=1` is
explicitly set) -- so it is not a direct restatement of this task's finding. It is, however, an
independent sighting of the same *general* symptom class (M=3 abundance-axiom solve cost being
close to the edge of tractability even before task 153's own changes), which is consistent with
this task's finding that the pre-153 code was already running close to budget (8.2s of a 15s
ceiling) rather than comfortably inside it -- i.e. M=3's abundance-family constraints were already
a known-fragile area, and task 153 tipped a specific instance of it over the edge.

## Confidence

**High** for cause 2 (the HEAD regression): directly bisected, single-commit-isolated, reproduced
in a zero-contention environment, with a large and deterministic-metric (`rlimit_count`) effect
size.

**Medium** for cause 1 (the original pre-153 failures): well-supported by every fact gathered
(identical rlimit, wall time at the top of the documented historical range, task 172's own `-n 6`
methodology) but not independently re-measured via an actual 6-way-parallel run at the historical
commit, which is out of this phase's scope. Recorded honestly as inference from consistent
evidence, not as a directly re-measured contention data point.

## Consequence for Phase 5

The fix target is `f9cc081e`'s two new axioms' interaction with `depth_bounded_skolem_abundance_constraint`
at M=3/temporal_depth=1 -- the ~4x `rlimit_count` increase they introduce for this formula. Per
the plan's Non-Goals, reverting the axioms is out of scope (task 153 explicitly deferred that
decision); Phase 5 must find an encoding-level mitigation that keeps both axioms' logical content
while reducing the combined MBQI instantiation cost for this formula back under budget.
