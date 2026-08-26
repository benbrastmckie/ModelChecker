# Research: Flaky TestMixedFormulas failures (test_mixed_or_diamond_prev, test_mixed_and_all_future_neg)

## Task

Determine the root cause of nondeterministic pass/fail outcomes for
`TestMixedFormulas::test_mixed_or_diamond_prev` and
`TestMixedFormulas::test_mixed_and_all_future_neg` in
`oracle/bimodal_logic/tests/test_oracle_interface.py`, and recommend a remedy. Starting
hypotheses: (a) Z3 solver nondeterminism, (b) test ordering / state leakage, (c) a genuine
semantics defect.

## Summary verdict

The evidence supports **(a), narrowed specifically to wall-clock timeout sensitivity under
ambient CPU load** — not solver-internal (seed) nondeterminism, and not test
ordering/state leakage. **(b) is ruled out** by direct evidence. **(c) is ruled out**: nothing in
this investigation, or in the extensive prior investigation already recorded in the test file's
own docstrings, points at a semantics defect — every prior probe found the *same* countermodel,
just at varying wall-clock cost. This is a **known, previously-diagnosed, and only partially
remedied** flakiness pattern, not a new one — see "Prior work already on this exact bug" below.

## What each test actually does, and why timing variance becomes a hard failure

`Z3OracleProvider.find_countermodel()` (`oracle/bimodal_logic/provider.py`) maps its
`timeout_ms` argument directly to the Z3 solver's `max_time` setting (a real wall-clock budget,
not a step/resource-bound budget). If the solve does not decide within that budget,
`structure.timeout` is true and the method **raises `OracleTimeoutError`** rather than
returning `None` (this separation is deliberate — see the docstring at
`oracle/bimodal_logic/provider.py:200-215` — because collapsing "gave up" into "proven valid"
would be unsound).

Both `test_mixed_or_diamond_prev` (`timeout_ms=150000`) and `test_mixed_and_all_future_neg`
(`timeout_ms=60000`) call `find_countermodel` and assert on the result **without catching
`OracleTimeoutError`** (contrast with the sibling `test_deeply_nested_enriched` in the same
class, which explicitly catches it as a valid third outcome). So for these two tests
specifically: any solve that fails to decide within its budget is a hard test failure, and the
sole variable governing pass/fail is real wall-clock solve time versus a fixed budget — there is
no semantic branch that could fail differently. This is the mechanism by which ordinary
wall-clock variance becomes visible as intermittent pass/fail rather than intermittent
skip/xfail.

## Prior work already on this exact bug

Both tests' docstrings (as they exist in the tree today) are not original commentary — they are
the accumulated record of at least three prior investigations into this same flakiness, across
commits `caf20bea` (2026-08-07), `7f7269d6` (2026-08-10), and `6ea94522` (2026-08-11):

- `test_mixed_or_diamond_prev`: genuine solve cost increased from ~1.5s to ~73s after an
  unrelated quantifier bound-variable-aliasing fix (commit `3c0cf210`) stopped sibling
  quantified operators from accidentally sharing Z3 term identity. `timeout_ms` was widened
  60000 -> 150000 (~2x headroom over the measured 72.6s worst case at the time), and the test was
  marked `@pytest.mark.xdist_serial` because under `-n 6` six-way CPU contention, the solve was
  observed to exceed even the widened 150000ms budget.
- `test_mixed_and_all_future_neg`: an isolated-seed measurement campaign (14 seeded draws across
  two rounds) found 0/14 draws exceeding the existing 60000ms budget; the one observed
  gating-suite failure occurred specifically under `-n 6` parallel contention. The test was
  marked `xdist_serial` on that basis, and the 60000ms budget was **deliberately left
  unchanged**. Critically, the same docstring records an unresolved **watch item**: a later,
  wider-budget 7-seed probe on previously-unsampled seeds measured two heavier isolated draws —
  **80.6s and 107.4s** — both already exceeding the 60000ms budget with no contention involved.
  The docstring explicitly instructs: "If this test ever fails SERIALLY, treat that as new
  measurement contradicting the 60000ms figure and recalibrate from a fresh uncensored probe —
  do not tweak the budget reactively."

In other words: the maintainers already identified, with direct measurement, that
`test_mixed_and_all_future_neg`'s solve-time distribution has a heavy right tail that is known to
exceed its own budget in isolation (i.e., **not requiring `-n` contention**) at roughly the rate
one would expect from a genuinely flaky test, but chose not to act on it yet because the
gating-suite failures observed up to that point were all attributable to `-n 6` contention. This
task's report of a bare/full-file run failing is consistent with that watch item finally
materializing, rather than a new phenomenon.

`run-oracle-suite.sh` correctly routes both tests away from `-n 6` contention today: pass 1 runs
`-n 6 -m "not xdist_serial and not slow and not unstable"`, pass 2 runs (no `-n`)
`-m "xdist_serial and not slow and not unstable"`. Neither pass currently applies `unstable`
deselection differently for these two tests — they carry `xdist_serial` only, not `unstable`.
The just-landed `unstable`/`unstable-watch.yml` infrastructure (marking
`TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` `unstable`, and its
`MAX_TIME_BY_NODEID_FRAGMENT`/`GATING_FLOOR_NODEID_FRAGMENT` TIMING classifier in
`.github/scripts/unstable_watch_classify.py`) is a **parallel, currently-unconnected**
mechanism: it exists for tests deliberately deselected from gating and watched separately, and
right now only recognizes two node-id patterns (`BM_CM_1-example_case7` and the gating-floor
test). It does not reference either `test_mixed_or_diamond_prev` or
`test_mixed_and_all_future_neg`, and `xdist_serial` deselection is independent of `unstable`
deselection — so this recently-landed work does not currently interact with (help or hurt) the
flakiness under investigation. It is, however, a ready-made *pattern* to extend if the team
decides to accept this as a documented, watched instability rather than eliminate it (see
Recommendation, option B).

## Direct measurement performed in this task

Constraints: single-file/class-scoped, foreground, bounded `timeout`, no background runs, capped
repetition. Machine load throughout was `load average` ≈ 6–10 on a 24-core box (ambient,
non-isolated — other work was plausibly running concurrently on this shared host), which is
itself a relevant condition, not just background noise, since it is exactly the kind of ambient
contention the existing docstrings already flag as the mechanism.

| Run | Test(s) | Order/mode | Result | Wall time |
|---|---|---|---|---|
| 1 | `test_mixed_and_all_future_neg` | isolated | pass | 31.70s |
| 2 | `test_mixed_and_all_future_neg` | isolated | pass | 52.86s (88% of 60s budget) |
| 3 | `test_mixed_and_all_future_neg` | isolated | pass | 31.70s |
| 4 | `test_mixed_and_all_future_neg` | isolated | pass | 27.47s |
| 5 | `test_mixed_or_diamond_prev` | isolated | pass | 87.30s (58% of 150s budget) |
| 6 | `test_mixed_or_diamond_prev` | isolated | pass | 84.71s (56% of 150s budget) |
| 7 | both, source order (diamond_prev then all_future_neg) | combined, serial, no `-n` | 2 passed | 114.86s total |
| 8 | both, reversed order (all_future_neg then diamond_prev) | combined, serial, no `-n` | 2 passed | 110.20s total |

**Observed flake rate in this task's measurement: 0/8 outright failures.** No reproduction of
the reported failure was obtained within the bounded budget available. However:

- `test_mixed_and_all_future_neg`'s isolated timings (31.70s, 52.86s, 31.70s, 27.47s) show
  ~2x variance run-to-run under ordinary (non-`-n`) invocation with no code change between runs
  — directly corroborating the "heavy tail" the existing docstring already measured, and
  consistent with (not statistically confirming, given n=4) draws in the 80–107s range being
  possible under adverse ambient load, which would exceed the 60000ms budget outright.
- `test_mixed_or_diamond_prev`'s two isolated runs (87.30s, 84.71s) were much more consistent
  with each other, comfortably inside the 150s budget (56–58% used) — no near-miss observed here
  in this task's sampling, though the 150s budget has less measured headroom margin
  historically (~2.07x over a 72.6s baseline) than its current 58%-used empirical result would
  suggest, and the docstring's own basis sample is small.
- Combined-order runs 7 and 8 show no dependence on execution order: total time and pass/fail
  outcome were consistent between source order and reversed order (114.86s vs. 110.20s), and
  each test's approximate individual contribution within the combined run was consistent with
  its isolated-run range (no inflation attributable to running adjacent to the other test).

## Hypothesis (b): test ordering / state leakage — ruled out

Four independent pieces of evidence rule this out as the driver:

1. `find_countermodel()` wraps every solve in `model_checker.utils.context.isolated_z3_context()`
   (`oracle/bimodal_logic/provider.py:255`), which swaps Z3's C-level `_main_ctx` to a fresh
   `z3.Context()` for the duration of each call specifically — per its own module docstring — to
   prevent "Z3 state leakage" from "accumulat[ing] learned lemmas and heuristic state from
   earlier tests," which the docstring says can otherwise "make later tests 2-10x slower and
   cause non-deterministic timeouts in the full suite." This is exactly the mechanism hypothesis
   (b) would need, and it is already explicitly guarded against on the call path both target
   tests use.
2. `TestMixedFormulas.setup_method` creates a brand-new `Z3OracleProvider()` per test method —
   there is no shared/cached provider or solver instance across test methods in this class.
   `Z3OracleProvider.__init__` also explicitly resets `self._semantics = None` "to prevent
   cross-call state leakage," and `find_countermodel` clears it again in a `finally` block.
3. Running the two target tests together in both source order and reversed order (runs 7 and 8
   above) produced no failure and no order-dependent timing divergence.
4. No `pytest-randomly` plugin is installed in this environment
   (`ModuleNotFoundError: No module named 'pytest_randomly'`), and `code/pyproject.toml`'s
   `addopts = "--durations=0 -v --import-mode=importlib"` carries no `-n`/xdist flag by default.
   A bare `pytest oracle/bimodal_logic/tests/test_oracle_interface.py` (no explicit `-n`) collects
   and executes tests in fixed source order, in a single process — not randomized, not
   worker-distributed. This means the task's "full-file run… fails… passes… with no code
   change" report is **not explained by nondeterministic collection/execution order** under a
   default invocation; whatever produced that observed failure was almost certainly wall-clock
   solve-time variance crossing the budget boundary (hypothesis (a)), possibly compounded if the
   run in question happened to pass `-n` explicitly (which would reintroduce exactly the
   contention mechanism the existing `xdist_serial` marker exists to route around, and would
   still apply even to a "full file" run if `-n` were passed without also filtering by marker).

## Hypothesis (a): Z3 solver behavior — supported, but narrowed

- No fixed Z3 random seed (`sat.random_seed` / `smt.random_seed` / `set_param`) is set anywhere
  in the oracle path (`provider.py`, `BimodalSemantics`, `ModelConstraints`) or in
  `isolated_z3_context()`. (One *other*, unrelated test in this tree —
  `test_boundary_regression.py:375` — mentions "pinned smt/sat.random_seed" as something done
  for a specific uncensored probe, confirming the mechanism exists and is usable, but it is not
  applied to the two target tests' normal execution path.)
- Two isolated runs of `test_mixed_and_all_future_neg` (runs 1 and 3, non-adjacent, same
  process-per-run) produced an **identical** wall time (31.70s, 31.70s), suggesting Z3's search
  is largely input-deterministic for this formula absent external contention — i.e., the
  variance is not obviously coming from Z3's own internal branching/heuristic randomness, but
  from external wall-clock scheduling pressure on an unpinned real-time budget. This is
  suggestive, not a rigorous proof (n=2 matching draws is a small sample, and same-machine
  caching effects could coincide).
- The already-recorded 80.6s/107.4s heavy-tail draws for `test_mixed_and_all_future_neg`, and
  the historical ~1.5s -> ~73s jump for `test_mixed_or_diamond_prev` from an unrelated quantifier
  fix, both point at genuine, input-sensitive Z3 solve-cost variance (not flakiness from a race
  or a bug) that simply sits close enough to the chosen timeout budget that ordinary real-world
  variance (this task's own measurement environment included, at load average 6–10/24 cores)
  can cross it.

**Distinguishing the two variance mechanisms**: I was not able to cleanly separate
"Z3-internal search-path variance for fixed input" from "OS/host scheduling variance" within
this task's bounded budget — doing so rigorously would require either pinning
`sat.random_seed`/`smt.random_seed` across many repeated draws (to hold Z3's own choices fixed
and observe only wall-clock/CPU-time variance) or, conversely, running on an otherwise-idle,
dedicated machine with CPU affinity pinned (to hold external contention near-zero and observe
only Z3-internal variance across repeated cold solves of the same input). Neither was
practical inside this task's bounded, foreground-only, capped-repetition constraint. This is the
one open item from the research goal I could not fully resolve — see Limitations.

## Hypothesis (c): genuine semantics defect — ruled out

No test in this investigation, nor any of the three prior investigations recorded in the
docstrings, ever found a *different* verdict (SAT vs. UNSAT, or a structurally different
countermodel) across runs — every characterization is in terms of the *same* countermodel being
found at varying wall-clock cost, or (in the tail case) not being found within budget at all
(`OracleTimeoutError`, an inconclusive result, not a wrong one). `find_countermodel`'s own
contract explicitly treats a timeout as distinct from and never collapsible into a semantic
verdict. Nothing in this task's measurement produced a wrong-verdict outcome either.

## Recommendation

Do not "fix" this by further ad hoc budget bumps without measurement — the existing
`test_mixed_and_all_future_neg` docstring already explicitly warns against reactive budget
tweaking, and a naive bump risks repeating the churn history visible in the commit log
(60000 -> 150000 for the sibling test, then still insufficient under contention). Two viable,
non-exclusive paths:

**A. Eliminate the flakiness (make outcomes deterministic), per the task's stated goal.**
Run a proper uncensored probe campaign (the same methodology the docstrings already used: N
isolated seeded draws, pinning `sat.random_seed`/`smt.random_seed` for reproducibility of each
draw while still sampling enough distinct seeds to see the tail) specifically for
`test_mixed_and_all_future_neg`'s formula, sized to actually capture the already-observed
80.6s/107.4s tail with statistical confidence, then set `timeout_ms` to a budget with genuine
headroom over the *measured worst tail*, not the median (the sibling `test_mixed_or_diamond_prev`
used ~2.07x of its measured worst as its own convention — apply the same convention here rather
than leaving 60000ms sitting below already-observed 80.6s/107.4s draws). This is the only path
that satisfies "make the outcomes deterministic" in the literal sense the task asks for, since
`xdist_serial` alone does not fix a budget that is already too tight for the input's *isolated*
tail — it only fixes budget shortfall caused by `-n` contention specifically, which is a
different mechanism from the one this task's watch item and this task's own measurement both
point at.

**B. If (A) is judged too expensive relative to how rarely the tail actually surfaces**, follow
the pattern the codebase just built and applied to
`TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`: mark both tests
`@pytest.mark.unstable` (or extend the existing `xdist_serial` semantics — TBD by the team,
`unstable` currently means "fully deselected from gating, watched separately"), add both node-id
fragments and their `max_time` (150 and 60, matching current budgets) to
`MAX_TIME_BY_NODEID_FRAGMENT` in `.github/scripts/unstable_watch_classify.py` so a future
timing-tail failure is auto-classified `TIMING` and does not fail CI, and let
`unstable-watch.yml` accumulate the same kind of run-history evidence it is now building for the
gating-floor test. This documents the instability explicitly rather than eliminating it, and is
a smaller, already-proven-pattern change — but it does not satisfy "make the outcomes
deterministic" as literally stated in the task; it makes the *non-determinism* explicit and
non-gating instead.

Given the task's explicit framing ("make the outcomes deterministic"), **A is the better fit for
what was asked**, with B available as a fallback if a follow-up measurement campaign shows the
true worst-case tail is impractically large relative to any reasonable CI budget.

## What I could not determine

1. **Could not reproduce an outright failure** in 8 bounded local runs (4 isolated
   `all_future_neg`, 2 isolated `diamond_prev`, 2 combined-order runs). The task's own report of
   an observed failure-then-pass with no code change is corroborated only indirectly, via
   (a) the pre-existing docstring's own uncensored-probe evidence of 80.6s/107.4s draws already
   exceeding `all_future_neg`'s 60000ms budget, and (b) this task's own measurement showing a
   52.86s draw (88% of budget) in the same direction. I did not get a direct, in-this-task repro
   of the reported failure itself.
2. **Could not cleanly separate "Z3-internal search variance" from "OS/host scheduling
   variance"** as the proximate cause of the wall-clock spread (see Hypothesis (a) above) —
   doing so needs a seed-pinned repeated-draw campaign or a dedicated/affinity-pinned host,
   neither of which fit this task's bounded, shared-host, foreground-only constraint.
3. **Did not attempt to reproduce under actual `-n` contention** (e.g. `-n 6`, matching
   `run-oracle-suite.sh` pass-1 conditions) — both target tests are `xdist_serial`-marked and
   `run-oracle-suite.sh` correctly excludes them from the `-n 6` pass, so reproducing under `-n`
   would only be relevant if some other invocation path (a developer's ad hoc `-n auto`, or a CI
   job not going through `run-oracle-suite.sh`) is actually what produced the task's reported
   failure — I could not determine which invocation path produced the originally reported
   failure, since the task description does not say how the "full-file run" was invoked (with or
   without `-n`).
4. **Did not mine actual CI run history** (GitHub Actions logs) for a real-world flake-rate
   number; all measurement in this report is local, on a shared, non-isolated host with ambient
   load average 6–10 on 24 cores throughout the measurement window — a plausibly relevant but
   uncontrolled variable I did not attempt to isolate or quantify further within the task's
   bounded budget.

## Files referenced

- `oracle/bimodal_logic/tests/test_oracle_interface.py` (`TestMixedFormulas` class, lines
  956-1066; target tests at lines 1002-1053)
- `oracle/bimodal_logic/provider.py` (`Z3OracleProvider.find_countermodel`, lines 130-296)
- `oracle/conftest.py` (`xdist_serial` marker registration and rationale, lines 55-63)
- `oracle/run-oracle-suite.sh` (two-pass parallel/serial split, lines ~191-218)
- `code/src/model_checker/utils/context.py` (`isolated_z3_context`, the Z3 state-leakage guard)
- `.github/scripts/unstable_watch_classify.py` (the just-landed `unstable`/TIMING classifier;
  currently unconnected to these two tests)
- `code/pyproject.toml` (`addopts`, `xdist_serial` marker registration, lines 50, 82-96)
