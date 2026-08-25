# Research: Fix Bimodal Solver-Timing Flakes and Introduce `unstable` Test Category

## Scope and method

This report investigates the two defects named in the task: (a) the intermittent
`test_bimodal.py::test_example_cases[BM_CM_1-example_case7]` timing flake, and (b) the
`TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` conclusive-count
shortfall in the oracle differential suite. Both were probed empirically (seed sweeps, an
encoding experiment, a local re-run of the exact CI-failing test, and a review of real GitHub
Actions run logs via `gh run view`) rather than assessed from the code alone. This machine is a
24-core / 30 GB workstation (AMD Ryzen AI 9 HX 370); GitHub's standard `ubuntu-latest` runners are
4 vCPU / 16 GB (per GitHub's own docs, current as of this report).

## Current state of the file scope

- `code/src/model_checker/theory_lib/bimodal/examples.py`: `BM_CM_1_settings` carries a detailed
  2026-08-11 comment recording a 15->60s `max_time` recalibration, a 7-seed pinned probe (median
  ~7.2s, decided draws up to ~10s) plus **one divergent draw undecided at 600s (~64x median)**,
  and the explicit conclusion "the divergent-draw residual is accepted and recorded: no budget
  closes it." `BM_CM_4_settings` (same `\Future`/temporal-quantifier family, `\past` side) carries
  a parallel comment: 7-seed probe, median 6.9s, worst decided draw 57.1s, recalibrated to 120s
  (~2.1x worst).
- `code/src/model_checker/theory_lib/bimodal/operators.py`: `_fresh_bound_int()`'s docstring
  documents that a **prior task (144) already investigated and exhaustively rejected** two
  encoding-improvement avenues for exactly this quantifier family: (1) `z3.FreshInt` in place of
  a counter-suffixed `z3.Int` -- causes even non-aliased single-instance formulas to blow the
  budget (a deterministic Z3/MBQI interaction, not solver-seed noise); (2) explicit
  `patterns=[...]` triggers on `ForAllTime`/`ExistsTime` -- Z3 rejects the only syntactically
  discoverable body-derived candidate with `invalid pattern` at construction time. Both dead ends
  are documented in-line at the `ForAllTime` definition (`semantic/core.py:432-460`).
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py`: `ForAllTime`/`ExistsTime`
  (lines 396-504) quantify over the finite time domain `D = (-M, M)` using a genuine `z3.ForAll`
  / `z3.Exists` with an `is_valid_time` guard, not an unrolled ground formula.
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`: `TestGatingConclusiveScan`
  (line 2298) re-solves the persisted 103-formula known-conclusive manifest at
  `GATING_RECHECK_SOLVE_TIMEOUT_MS = 20000` (line 114) and asserts `conclusive >=
  MIN_CONCLUSIVE_GATING_FORMULAS = 100` (line 183, ~97.1% retention of 103). The floor's own
  derivation comment records "the slowest conclusive solve observed in the re-deriving run was
  10.094s" against the unrelated 10000ms **derivation** budget -- it does not say what hardware
  that derivation ran on.
- `code/docs/core/TESTING_GUIDE.md`: sections **8.6** ("Solver Timing Budgets and Machine
  Variance") and **8.8** ("Oracle Suite: Gating vs. Exhaustive Split") already exist and already
  document this exact class of variance in detail, including a prior two-run swing (103 vs 105 of
  274 conclusive on the exhaustive scan) attributed to contention. Section 8.6's own convention
  ("set budgets generously... prefer the 30s convention... give timing assertions generous
  tolerances") is the standard any new `unstable`/floor-change work should match.
- `code/pyproject.toml`: `[tool.pytest.ini_options] markers` (line 86) has `slow` as the model to
  follow; no `unstable` marker exists yet.
- `.github/workflows/tests.yml:73`: `pytest tests/ src/model_checker -m "not packaging and not
  performance" -n 6 -q` -- runs the bimodal suite including BM_CM_1 (not in
  `KNOWN_TIMEOUT_EXAMPLES`).
- `.github/workflows/release.yml`: **does not currently run the bimodal/general pytest suite at
  all.** `test-and-release` only builds the wheel, installs it, and smoke-tests import/CLI/version
  match; `build` runs only `tests/packaging/ -m packaging`. There is therefore no `-m` expression
  in this file to extend for BM_CM_1 today (see "Correction" below).
- `.github/workflows/differential-tests.yml`: line 48 runs
  `-m "not slow and not differential"` (lets `TestGatingConclusiveScan` through, unmarked); lines
  56-62 run an explicit `TestCIGate`/... list that does **not** include
  `TestGatingConclusiveScan`.
- `.github/workflows/unstable-watch.yml`: does not exist. No workflow in this repo currently uses
  `schedule:` -- this will be the first.

### Correction to the task's release.yml claim

The task states BM_CM_1 "PASS[ed] in release.yml's own matrix." Reading `release.yml` shows its
`test-and-release` job never invokes pytest at all (confirmed via `git log -p` back to its
creation) -- there is nothing there to fail or pass on BM_CM_1. Checking real run history via
`gh run list`/`gh run view` resolves this: for the v1.3.0 tag push
(`e6ab4868`), the **`Tests` workflow** run on `headBranch: v1.3.0` failed on BM_CM_1 while the
**`Release` workflow** run on the identical commit succeeded (build+twine+packaging-contract, no
bimodal pytest), and the **`Tests` workflow** run on the preceding `master` push at the same SHA
passed. So "release.yml's own matrix... passing" is more precisely "the Release workflow's own
gate (which doesn't run this test) reported success" -- not a second, independent pytest pass of
BM_CM_1. This doesn't change the task's verdict (still genuinely intermittent: red on one
`Tests` run, green on the adjacent `master` push of the identical commit) but it does mean
phase (4)'s file-scope instruction to extend release.yml's "matrix" exclusion expression has no
literal target in the current file -- see Recommendations.

## Defect (a): BM_CM_1 empirical probe

### Seed sweep (baseline, unmodified code)

Ran BM_CM_1 at its exact example settings (N=2, M=2, contingent=True, `max_time` raised to 90s as
a probe-only ceiling) across `smt.random_seed`/`sat.random_seed` in {1..7}, each in a fresh
isolated Z3 context:

| seed | result | elapsed (s) |
|------|--------|-------------|
| 1 | True | 4.76 |
| 2 | True | 47.78 |
| 3 | True | 1.99 |
| 4 | True | 7.96 |
| 5 | True | 11.18 |
| 6 | True | 6.75 |
| 7 | True | 16.52 |

Median ~8s, all 7/7 decided (found the genuine countermodel) within 90s, but with one draw
(seed 2) landing at 47.78s -- close enough to the current 60s `max_time` that on slower/more
contended hardware it would plausibly tip over. A second run of the same sweep (used for the
encoding experiment below) reproduced the same shape with different exact numbers (45.14s,
1.94s, 7.83s, 10.74s, 7.16s, 16.14s for seeds 2-7) -- itself corroborating TESTING_GUIDE 8.6's
point that even a pinned seed does not give byte-identical timing, only a similar distribution.

This is consistent with, not a re-derivation superseding, the settings comment's own 7-seed probe
(median ~7.2s, one 600s-undecided draw) -- a 7-run sample from either probe is far too small to
reliably re-sample a rare tail event, so the absence of a >90s draw in my sample is expected
rather than contradicting the documented 600s outlier.

**Direct evidence of the tail biting in real CI**: the actual GitHub Actions failure log for the
v1.3.0-tag `Tests` run shows `60.94s call
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_cases[BM_CM_1-example_case7]`
immediately followed by the assertion failure -- i.e. this specific draw landed just past the 60s
budget, not anywhere near the documented 600s divergent extreme. This matches "a near-budget draw
tipped over," exactly the class of event my seed-2 (47.78s / 45.14s) sample already sits close to.

### Prior investigation already exhausted (task 144)

Before running new experiments, note what has already been tried and rejected, per
`operators.py`'s `_fresh_bound_int` docstring (`semantic/core.py:432-460`):

1. **`z3.FreshInt` instead of counter-suffixed `z3.Int`** -- Z3's own built-in remedy for the
   aliasing hazard this counter exists to avoid. Empirically causes even *non-aliased, single-
   instance* formulas (no nesting hazard at all) to go from ~1-2s to not deciding within 60s,
   confirmed deterministic (not seed noise) by holding the encoding fixed and varying only
   Int-vs-FreshInt.
2. **Explicit `patterns=[...]` triggers on `ForAllTime`** -- the only syntactically-discoverable
   body-derived trigger candidate (from `\next(B)`'s `Until(B, bot)` translation) is rejected by
   Z3 at construction time with `invalid pattern`, not merely ineffective.
3. **Explicit `patterns=[...]` triggers on `ExistsTime`** -- not attempted; every target formula's
   `ExistsTime` gets Skolemized away by Z3's own preprocessing before search begins (no enclosing
   universal to guide), so a pattern there is provably inert.

This means the "obvious" trigger/pattern-tuning avenue for this exact quantifier family is not an
open question -- it was already investigated with real measurements and closed.

### New experiment: finite unrolling of `ForAllTime`/`ExistsTime`

Since the time domain `D = (-M, M)` is always finite and known statically (M is a plain Python int
at `BimodalSemantics` construction), I tested a genuinely different avenue task 144 did not try:
replacing the `z3.ForAll`/`z3.Exists` quantifier with an explicit ground conjunction/disjunction
over every valid integer time point (`z3.substitute(body, (time_var, z3.IntVal(t)))` for each `t`
in range), removing MBQI-driven quantifier instantiation from the time dimension entirely (the
world dimension still needs genuine Skolemization/quantification -- only time was unrolled).

Same 7-seed sweep, `quantified` (baseline) vs `unrolled` (patched), 90s probe ceiling:

| seed | quantified (s) | unrolled (s) | unrolled result |
|------|----------------|---------------|------------------|
| 1 | (baseline run 1: 4.76) | **90.27 (timed out)** | False |
| 2 | 45.14 | 5.88 | True |
| 3 | 1.94 | 1.97 | True |
| 4 | 7.83 | 9.52 | True |
| 5 | 10.74 | **90.30 (timed out)** | False |
| 6 | 7.16 | 0.23 | True |
| 7 | 16.14 | 4.04 | True |

**Verdict: not a reliable fix.** Unrolling helps dramatically on some seeds (seed 6: 7.16s ->
0.23s, ~30x; seed 2: 45.14s -> 5.88s, ~8x; seed 7: 16.14s -> 4.04s, ~4x) but two of seven seeds
(1 and 5) went from deciding comfortably under the baseline to **not deciding at all within the
same 90s probe budget** -- a regression, not an improvement, for those draws. This is the classic
bounded-unrolling trade-off: flattening a quantifier into a large ground formula can help Z3's
search on some instances and hurt it on others (different clause structure interacts differently
with the SAT/DPLL(T) core), and this experiment shows both directions are live for this specific
formula. Given `pyproject.toml`'s "no backwards compatibility, complete migration" philosophy and
`ForAllTime`/`ExistsTime`'s use by every temporal operator (not just `\Future`), adopting this
would require a full soundness and regression pass across the whole bimodal suite for an approach
that is not demonstrated to help on net -- **not recommended** within this task's scope. It is,
however, a genuinely new (not previously attempted) avenue worth recording as tried-and-inconclusive
for anyone revisiting this later, distinct from task 144's already-exhausted pattern/trigger line.

### Systemic corroboration (this is not BM_CM_1-specific)

`oracle/bimodal_logic/tests/test_boundary_regression.py`'s `BM_CM_4` inline copy documents the
identical phenomenon independently: 7-seed probe, median 6.9s, worst decided draw 57.1s, plus
separate prose noting a **"~1-in-7 chance across the seeded draw distribution"** of a divergent,
budget-blowing draw for the sibling `next_A`/`some_future(A)` formulas in the same operator
family (a 600s-budget run measuring `rlimit 1.026B = 7.5x a good draw`). `oracle/conftest.py`
already carries a standing `xdist_serial` marker specifically for `BM_CM_1` in its own regression
test (`test_regression_all_active_examples[BM_CM_1...]`), independent evidence this contention
sensitivity is a recognized, cross-cutting property of this operator family, not an isolated
one-off in `test_bimodal.py`.

### Conclusion for (a)

No genuine encoding fix was found. Two encoding avenues are now demonstrably exhausted (task 144's
trigger/pattern work, confirmed by its own in-line record) and a third, newly-tried avenue
(finite unrolling) is empirically inconclusive-to-negative. The instability is heavy-tailed
(median ~7-8s, rare draws into the tens of seconds, a documented once-in-7-seeds 600s-undecided
outlier), is not semantic (every decided draw finds the genuine countermodel; 0 disagreements
anywhere in this investigation), and matches the strict `unstable` entry criteria in the task
description. **Recommend marking BM_CM_1 `unstable`** rather than attempting a further
recalibration or encoding change.

## Defect (b): oracle conclusive-population floor

### Local re-run of the exact failing CI test

Ran `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` unmodified,
twice, on this machine:

- **Unrestricted (24 cores)**: `agreements=103 disagreements=0 timeout_count=0
  conclusive=103/103`, PASSED, 194.64s wall clock.
- **CPU-restricted to 2 cores** (`taskset -c 0,1`, approximating a weak/shared runner's core
  *count*): `agreements=103 disagreements=0 timeout_count=0 conclusive=103/103`, PASSED, 176.06s
  wall clock -- no degradation at all; if anything slightly faster (within run-to-run noise).

### Real CI run data (via `gh run view`)

Pulled the actual failing logs for two independent GitHub Actions `Differential Oracle Tests`
runs on `master`/tag pushes in the last several days:

- Run `31628414697` (v1.3.0 tag push, 2026-08-12): `AssertionError: Only 96 of 103 formulas were
  conclusive (floor=100)`; `agreements=96 disagreements=0 timeout_count=7 conclusive=96/103`.
  Total step wall clock: 744.54s (well inside the 900s `--timeout`, so this is real per-formula
  solve degradation, not a suite-level timeout artifact).
- Run `31628228088` (master push, 2026-08-12): `AssertionError: Only 95 of 103 formulas were
  conclusive (floor=100)`; `agreements=95 disagreements=0 timeout_count=8 conclusive=95/103`.

Both real CI runs: **zero disagreements**, matching the task's own framing ("a budget/performance
regression to investigate, not a semantic one") and matching every local measurement here.
(A third, unrelated CI failure on 2026-08-10, `31429388027`, failed at the install step in 13s
with exit 127 -- an environment/setup problem, not this defect; it is not further evidence either
way for the floor question.)

### Which hypothesis the evidence supports

Of the three hypotheses the task poses:

- **"Genuine cost growth in the oracle harness"**: not supported. The identical code, identical
  manifest, identical `GATING_RECHECK_SOLVE_TIMEOUT_MS=20000` budget resolves 103/103 with zero
  slack margin issues on this machine, twice, under two very different CPU-availability
  conditions (24 cores vs 2 cores). If the *formulas themselves* had grown genuinely more
  expensive, restricting to 2 cores locally should have started exposing that; it did not.
- **"Shared-runner contention a larger per-formula budget would absorb"**: partially supported,
  and the most actionable explanation. GitHub's standard `ubuntu-latest` runners are 4 vCPU / 16GB
  (per GitHub's own current documentation) versus this 24-core/30GB workstation -- a real,
  large hardware gap, not merely a core-count difference my `taskset` experiment could isolate
  (that experiment only reduces *my own* core count; it cannot reproduce GitHub's weaker
  per-core clock/IPC or its shared/virtualized-neighbor contention). The pattern (0
  disagreements, consistent ~92-93% conclusive on CI vs 100% locally under any local core
  restriction) is exactly what "CI hardware/contention is slower per-formula than the
  derivation host" predicts.
- **"A floor calibrated on quiet-host measurements that was never valid on CI hardware"**: also
  supported and not mutually exclusive with the point above -- the floor's own derivation comment
  (`MIN_CONCLUSIVE_GATING_FORMULAS`'s docstring) never states what hardware the derivation ran on,
  and nothing in this investigation found the derivation invalid *in general* (my local host
  reproduces it perfectly) -- only that it does not transfer to GitHub's actual runner class.

### Conclusion for (b)

**Recommend widening `GATING_RECHECK_SOLVE_TIMEOUT_MS` first**, not lowering
`MIN_CONCLUSIVE_GATING_FORMULAS`. This is the same class of remedy already used for BM_CM_1/BM_CM_4
(a budget recalibration backed by measurement, not an assertion weakening) and it preserves the
floor's meaning (100 of 103, ~97.1%) rather than accepting a lower bar. A 2x widening (20000ms ->
40000ms, matching the ~2x-of-measured-worst convention used elsewhere in this codebase) is a
reasonable first move to propose in the plan, but **this report does not have access to a real
GitHub Actions runner to validate a specific new number** -- the taskset experiment shows local
core-restriction alone doesn't reproduce the shortfall, so the right multiplier can only be
confirmed by re-running the actual workflow (`workflow_dispatch` on `differential-tests.yml`) a
few times after widening, per this codebase's own existing evidence discipline (see
`code/docs/core/TESTING_GUIDE.md` 8.6/8.8, and the `_reader-verifies-on-two-real-runs` precedent
already used for the 274-formula exhaustive floor). If, after a genuinely widened and CI-verified
budget, GitHub's runners still cannot consistently clear a floor within reasonable slack, marking
`TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` `unstable` is the
documented fallback -- but the entry criteria (genuine fix attempted, non-semantic, exit
criterion) point first to attempting the budget widening on real CI, which the implementation
phase should try before reaching for the marker on this test.

## `unstable` marker: exact `pyproject.toml` addition

Add to `[tool.pytest.ini_options] markers` in `code/pyproject.toml`, following the `slow` entry's
style exactly as specified in the task:

```toml
    "unstable: Tests with a documented, investigated non-semantic instability (e.g. a heavy-tailed solver draw). Deselected from release-gating runs with `-m \"not unstable\"`; run on their own by the unstable-watch workflow so they stay observed rather than forgotten.",
```

### Candidate markings (this research's recommendation)

- **`test_bimodal.py::test_example_cases[BM_CM_1-example_case7]`**: mark `unstable` now. Entry
  criteria met: documented (`BM_CM_1_settings` comment + this report), non-semantic (genuine
  countermodel found on every decided draw, 7/7 in this probe, corroborated by the settings
  comment's own history), genuine fix attempted and failed (task 144's trigger/pattern work +
  this report's unrolling experiment), exit criterion to write: e.g. "N consecutive
  unstable-watch runs (recommend N=20, matching a ~3-week nightly cadence) with zero
  non-timing-signature failures, or a genuine encoding fix that empirically collapses the tail
  across a >=20-seed sweep."
- **`TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`**: do **not**
  mark `unstable` yet. Attempt the budget-widening fix first (this is a genuine, not-yet-tried
  remedy backed by strong evidence above); only fall back to `unstable` if a CI-verified widened
  budget still leaves a persistent shortfall.

## Workflow wiring notes for the plan/implementation phase

- `.github/workflows/tests.yml:73`: append `and not unstable` to the existing `-m "not packaging
  and not performance"` expression.
- `.github/workflows/release.yml`: **no literal target exists today** (see Correction above) --
  release.yml's `test-and-release` job runs no pytest suite to append a marker filter to. The
  plan should either (a) note this file needs no change for BM_CM_1 specifically (nothing there
  currently runs it), or (b) if the intent is that release.yml *should* run the general suite
  gated the same way `tests.yml` does (closing the gap this report surfaced), that is new scope
  beyond a marker-append and should be flagged as a decision for the plan, not silently assumed.
- `.github/workflows/differential-tests.yml:48`: append `and not unstable` to `-m "not slow and
  not differential"`. Line ~56-62's explicit `TestCIGate`/... list is unaffected (it never
  included `TestGatingConclusiveScan`).

## `unstable-watch.yml` design sketch

No scheduled (`schedule:`) workflow exists anywhere in this repo yet -- this will be the first.
Suggested shape, modeled on `differential-tests.yml`'s structure:

- Triggers: `schedule` (weekly cadence recommended, matching the exhaustive-scan cadence already
  established in TESTING_GUIDE 8.8) + `workflow_dispatch`.
- Runs `pytest -m unstable` across both `code/tests/`+`src/model_checker` (for BM_CM_1) and
  `oracle/bimodal_logic/tests/` (for any oracle-side markings), never gating (no effect on
  `needs:`/branch protection).
- Job summary: pass/fail per test, ideally an append-only record (a small JSON/CSV artifact
  committed or uploaded, not required to design in the research phase but should follow the
  `SCAN_COMPLETE`-marker / `progress.jsonl` completion-signal discipline already established in
  `oracle/`'s own instrumentation, since this repo already has that pattern to reuse rather than
  reinvent) so the decided/undecided ratio is legible over time, per the task's requirement.
- A new failure signature (assertion text differing from the documented timing-signature failure)
  must be surfaced loudly (distinct from an ordinary timeout) -- reuse the "resolved-and-wrong vs
  inconclusive" bucketing pattern already used throughout `test_cross_oracle_differential.py`
  (e.g. `_assert_scan_report`, `test_known_invalid_return_countermodel`) as the template for this
  distinction.

## TESTING_GUIDE.md documentation target

Extend section 8 of `code/docs/core/TESTING_GUIDE.md` (a new **8.9 "The `unstable` Marker"**
subsection, sibling to 8.6-8.8) rather than inventing a new top-level section -- it directly
continues 8.6's machine-variance discussion and 8.8's gating-floor discussion. Should record:
entry criteria (verbatim from the task/marker docstring), exit criteria and the promotion path
back to gating, review cadence (recommend matching the weekly exhaustive-scan cadence already
established in 8.8), and the standing rule that an indefinitely-quarantined test is itself a
defect to escalate.

## Follow-up task guidance (per phase 7)

Given neither defect closed completely in this research phase (BM_CM_1 has no fix, only a
documented `unstable` marking; the oracle floor has a promising but CI-unverified remedy), a
follow-up task will very likely be needed after implementation, carrying forward:

- BM_CM_1: marked `unstable`, exit criterion as drafted above, and the standing verdict (from the
  settings comment and this report) that **no budget closes the tail** -- do not re-tune
  `max_time` in the follow-up either.
- Oracle floor: whatever the implementation phase's widened `GATING_RECHECK_SOLVE_TIMEOUT_MS`
  turns out to be, plus real CI verification results (or their absence, if CI access to re-run
  `workflow_dispatch` several times wasn't exercised at implementation time) -- the 95/103 and
  96/103 measurements from this report, the do-not-lower-the-floor instruction, and whether
  `TestGatingConclusiveScan` ended up marked `unstable` or genuinely fixed.
- Both ruled-out avenues from this report (task 144's trigger/pattern work; this report's
  unrolling experiment; the 2-core `taskset` non-reproduction for defect (b)) so the follow-up
  starts from the frontier, not the beginning.

## Recommended next steps for the plan phase

1. Add the `unstable` marker to `code/pyproject.toml` (text above).
2. Mark `test_example_cases[BM_CM_1-example_case7]` `unstable` with an in-line comment matching
   the entry-criteria evidence in this report.
3. Widen `GATING_RECHECK_SOLVE_TIMEOUT_MS` (propose 40000ms) with an in-comment justification of
   the same rigor as `BM_CM_1`/`BM_CM_4`'s recalibrations (cite this report's local-vs-CI
   measurements), then verify via `workflow_dispatch` on `differential-tests.yml` before deciding
   whether `TestGatingConclusiveScan` also needs `unstable`.
4. Wire `-m` deselection into `tests.yml` and `differential-tests.yml`; resolve the `release.yml`
   ambiguity explicitly (decision, not silent assumption) rather than editing a file with no
   current target.
5. Add `.github/workflows/unstable-watch.yml` per the design sketch above.
6. Add TESTING_GUIDE.md section 8.9.
7. After implementation, assess whether a follow-up task is needed per the guidance above -- very
   likely yes for the reasons stated.
