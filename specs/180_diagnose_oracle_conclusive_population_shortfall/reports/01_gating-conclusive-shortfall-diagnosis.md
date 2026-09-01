# Diagnosis: Oracle gating conclusive-population shortfall (unstable-watch, 2026-08-27 → 2026-09-01)

**Status of this report: diagnosis complete for the CI-observed failures; the task's explicit
MEASUREMENT REQUIREMENT (an idle-host reproduction at current, axiom-bearing HEAD, with the
conclusive count and wall clock recorded) is OUTSTANDING — attempted, did not finish within this
dispatch, and is not silently assumed either way. See (b) below for the full account and what a
follow-on should run to close it.**

## Summary

The `test_known_conclusive_population_self_consistent` failures observed nightly on
`unstable-watch.yml` since 2026-08-27 are **not a new defect and not caused by the 2026-08-31
Skolemized Seriality/Interpolation frame axioms**. Two independent, already-diagnosed conditions
compound to produce exactly the symptom described in this task:

1. **A stale CI checkout.** `origin/master` on GitHub was frozen at commit `98d3ad8d` (tagged
   `v1.3.7`, authored 2026-08-26) for roughly five days. Every `unstable-watch.yml` run from
   2026-08-27 through the 2026-09-01 09:48 UTC run named in this task's symptom — six runs total —
   checked out that identical, stale `headSha`. Local work (tasks 172–182, including a classifier
   bugfix and the frame-axiom commit) accumulated on the local `master` but did not reach
   `origin/master` until shortly after the 09-01 run (the next push-triggered
   `differential-tests.yml` run, at 11:04 UTC that day, is the first to run at a newer commit).
   `git fetch origin master` at research time shows local `HEAD` and `origin/master` now fully
   synced (0 commits ahead/behind either direction), so this gap has since closed on its own — the
   observed runs are exactly the ones caught in it.
2. **An already-fixed classifier defect that never reached CI.** `.github/scripts/
   unstable_watch_classify.py`'s `DISAGREEMENT_SIGNATURE` was a bare substring
   (`"Self-comparison produced"`) at `98d3ad8d`. Because `_assert_scan_report`'s two asserts fire
   in sequence and pytest's traceback embeds the *unrendered f-string source* of the first
   (passing) assert when the *second* assert fails, that bare substring always appears in the
   failure text of a genuine floor-only failure — with no digit after "produced". The bare
   substring therefore matched on every conclusive-population-floor failure, laundering it into a
   false "genuine disagreement" signal and forcing `classify()` to return `NEW` instead of
   `TIMING`, unconditionally. This defect was diagnosed and fixed locally in commit `cfb9cb4a`
   ("task 175 phase 2: fix the laundering guard (GREEN)", 2026-08-31 11:07 -0700, replacing the
   bare substring with `re.compile(r"Self-comparison produced \d+ disagreements")`), and is
   covered by 43 passing tests in `code/tests/ci/test_unstable_watch_classifier.py` at current
   HEAD. But `cfb9cb4a` is *not* an ancestor of `98d3ad8d` — the fix postdates the frozen
   checkout — so it has never been exercised by any real CI run to date, including the run this
   task was opened against.

Reconstructing the exact failure text from the 2026-09-01 job log and feeding it to both
classifier versions confirms this directly:

```
STALE classify()  (checked out at 98d3ad8d, what CI actually ran): NEW
FIXED classify()  (current HEAD, never yet run on CI for this test): TIMING
```

Under the fixed classifier, all six "NEW FAILURE MODE" alerts issued since 2026-08-27 would have
been (and, once the classifier's own fix reaches a real run, will be) correctly recorded as
`TIMING` — the expected, already-quarantined budget/performance shortfall, not a semantic
regression and not a drift from the documented signature. The classifier's misfire is a pure
CI/deployment synchronization artifact, not a bug in the test, the oracle, or bimodal semantics.

## (a) Which formulas, and is the shortfall set stable?

**Individual formula identities are not recoverable from available CI artifacts** — this is a
pre-existing, already-documented limitation (see `GATING_RECHECK_SOLVE_TIMEOUT_MS`'s own comment
block in `test_cross_oracle_differential.py`, criterion (3)): `unstable-watch.yml`'s pytest
invocation for the oracle tree passes none of `_generate_differential_report`'s
`progress_path`/`heartbeat_every`/`artifact_dir` instrumentation, and only the aggregate `scan
report: ...` line is captured. This diagnosis did not add that instrumentation (it would be a
remediation change, out of scope per the task's non-goals).

What *is* recoverable — the aggregate counts across all six real runs, pulled directly from each
run's job log (`gh run view --job <id> --log`), all with **zero disagreements**:

| Date (UTC) | Run ID | Conclusive | Timeouts | Duration (s) | Classifier verdict (actual, stale) | Verdict under fixed classifier |
|---|---|---|---|---|---|---|
| 08-27 | 33091941820 | 98/103 | 5 | 761.61 | NEW (false) | TIMING |
| 08-28 | 33193518591 | 96/103 | 7 | 824.89 | NEW (false) | TIMING |
| 08-29 | 33250263772 | 98/103 | 5 | 749.10 | NEW (false) | TIMING |
| 08-30 | 33306220265 | 96/103 | 7 | 898.78 | NEW (false) | TIMING |
| 08-31 | 33386925098 | 96/103 | 7 | 808.64 | NEW (false) | TIMING |
| 09-01 | 33494135668 | 97/103 | 6 | 788.74 | NEW (false, this task's trigger) | TIMING |

The shortfall **varies night to night** (5–7 timeouts out of 103, i.e. 96–98/103 conclusive,
93.2%–95.1%), all under the `MIN_CONCLUSIVE_GATING_FORMULAS=100` floor but consistently close to
it and consistently zero-disagreement. This is the same shape (a heavy-tailed, load-dependent
subset near the timeout budget, not a fixed deterministic set) already recorded for the pre-
quarantine real-CI runs cited in the source file's own history (96/103 and 95/103 on 2026-08-12;
96/103 again on 2026-08-25 at 2x budget). If anything, three of the six nights (08-27, 08-29, and
marginally 09-01) show a *smaller* shortfall (5–6 timeouts) than the historical 7–8 that originally
justified the floor and the `unstable` marking — no evidence of a worsening trend.

## (b) Budget/contention vs. a real cost regression

Evidence points to budget/contention on GitHub's standard runner, exactly as already established
and documented at length in `GATING_RECHECK_SOLVE_TIMEOUT_MS`'s comment block, with no new
evidence of a genuine oracle-encoding or in-package-semantics cost regression:

- **Zero disagreements on all six runs.** `_assert_scan_report` asserts `disagreements == 0`
  first and unconditionally; it has never fired across this entire window. Every failure is
  exclusively the performance floor, never a changed verdict.
- **The oracle solve path itself is unchanged since the last local 103/103 derivation.** Diffing
  `oracle/` between the stale CI checkout (`98d3ad8d`) and current HEAD shows only test-marker and
  comment changes to `test_cross_oracle_differential.py`/`test_soundness_regression.py`/
  `conftest.py`/`run-oracle-suite.sh` (190 lines, all four files test-tree-only) — `provider.py`,
  `translation.py`, `errors.py`, and the persisted manifest are byte-identical across that range.
  Task 167's `max_rlimit` plumbing (already present in the stale checkout) is opt-in and never
  passed by `TestGatingConclusiveScan`'s call sites, so it does not affect this test's budget
  behavior either way — it stays purely `max_time`-driven, exactly as documented.
- **Idle-host re-measurement — ATTEMPTED, DID NOT COMPLETE WITHIN THIS DISPATCH. The
  MEASUREMENT REQUIREMENT is therefore OUTSTANDING, not satisfied.** A local run of
  `test_known_conclusive_population_self_consistent` was started on this research host (24-core /
  30GB, load average ~4.7-5.1 on 24 cores — the same class of machine as the original derivation
  workstation, though not perfectly idle: a handful of unrelated `nvim`/`claude`/build processes
  were present, and a concurrent `pytest tests/integration/...` invocation from a sibling session
  was observed mid-run) via `PYTHONPATH=code/src timeout 1000 python3 -m pytest
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestGatingConclusiveScan::test_known_conclusive_population_self_consistent
  -v -m unstable -s`, run in the background so other research could continue concurrently. At the
  time this dispatch was closed out, the run had been executing for ~356s (of its 1000s timeout)
  with no result yet written to its log (`collecting ... collected 1 item` was the last line
  observed; the test itself had not finished). The process was independent of this dispatch's own
  lifecycle (started via `&`/`disown`) and may still be running or may have since completed or
  timed out, but this report does not rely on or guess at any outcome from it — no number from
  that run is reported here, measured or inferred, because none was actually observed to
  completion.

  **What this means concretely:** every claim above in this subsection (unchanged solve path,
  zero disagreements on all six real CI runs, historical 103/103 local derivations) is real,
  measured evidence, but all of it either (i) predates the 2026-08-31 Skolemized
  Seriality/Interpolation axioms landing inside `BimodalSemantics.build_frame_constraints` — which
  `Z3OracleProvider` calls internally — or (ii) comes from CI runs whose checkout also predates
  those axioms (see the ordering finding in (c) and the forward-looking risk it flags). **No
  fresh, axiom-bearing, idle-host measurement of this specific test exists as of this report.**
  The task's explicit instruction — "If the shortfall does not reproduce idle, that is itself the
  finding and should be recorded with the numbers" — cannot be honored either way (reproduce or
  not) without that run finishing. This is recorded here as an open gap, not silently dropped: a
  follow-on task (or a re-run of this one) should execute that command to completion — expect
  roughly 200-900s wall clock based on the range this report's other evidence spans — and record
  whichever outcome it produces (conclusive count, timeout count, wall clock) before treating the
  budget/contention hypothesis as measured, rather than well-supported-but-inferred, for the
  axiom-bearing code now at `origin/master`.

## (c) Ordering against the Skolemized Seriality/Interpolation axioms (commit f9cc081e)

Verified rather than assumed, per the task's explicit instruction, from two independent angles:

1. **Wall-clock ordering.** `f9cc081e` ("task 153 phase 4: implement and wire Skolemized
   Seriality/Interpolation") was authored 2026-08-31 13:35 -0700. The watch began failing
   2026-08-27 — four days *before* the axioms landed even locally.
2. **Code-content ordering (the decisive check).** Every one of the six real CI runs analyzed
   above checked out `98d3ad8d`, dated 2026-08-26 — and `git merge-base --is-ancestor f9cc081e
   98d3ad8d` fails: `f9cc081e` is not an ancestor of the commit CI actually ran. **None of the six
   observed shortfall runs executed any code containing the new axioms at all.** The frame-axiom
   commit cannot be the cause of any run analyzed in this diagnosis, full stop — not because the
   ordering happens to look clean, but because the axiom code was structurally absent from every
   CI process that produced these failures.

**Forward-looking risk, not yet observed:** `Z3OracleProvider` (the oracle
`TestGatingConclusiveScan` exercises) constructs its own `BimodalSemantics(settings)` internally
(`oracle/bimodal_logic/provider.py:275`) and calls `build_frame_constraints()`, which is exactly
the function `f9cc081e` modified. `core.py` (home of `build_frame_constraints`) differs by 152
lines between the stale checkout and current HEAD. Now that `origin/master` has caught up, the
*next* `unstable-watch` run will, for the first time, exercise this gating test's oracle solves
with the two new TaskFrame axioms present — a variable none of the six analyzed runs tested.
Task 178 (tracked separately, scoped to a different test —
`TestShiftClosure::test_shift_closure_on_extracted_worlds_m3`) already measured a real, `rlimit`-
count-confirmed 4–6x solver-cost increase from these same two axioms in a different Z3 constraint
context. Whether that cost increase propagates into `TestGatingConclusiveScan`'s 103-formula
resolve budget is genuinely unknown and untested by anything in this diagnosis's evidence — it is
a real, specific, and previously-uncontrolled-for risk for whoever owns the next observation of
this test, flagged here explicitly rather than left implicit.

## (d) Should TESTING_GUIDE.md section 8.9's documented signature be updated?

No change to the *entry-criteria record* is warranted — the four-criteria block at
`GATING_RECHECK_SOLVE_TIMEOUT_MS` and the "Currently marked" list in TESTING_GUIDE.md 8.9 both
still accurately describe the phenomenon (a CI-verified, zero-disagreement, budget-only shortfall,
with a written 20-run-or-verified-fix exit criterion). The drift the classifier flagged is not a
change in the test's real-world behavior; it is that automated `classify()` output disagreed with
the human-authored narrative in the comment block, because the two were derived from different
sources of truth (the actual CI job's classify-step exit code vs. a person manually reading
durations/counts out of the job log without cross-checking the classify step's own verdict).

One documentation gap is worth closing in a follow-on task: the "(3b) ZERO-CONTENTION
RE-CONFIRMATION" paragraph (lines ~208–224 of `test_cross_oracle_differential.py`) cites the same
five 08-27→08-31 runs' durations as evidence of "the identical 96/103 conclusive, 7-timeout,
0-disagreement result," but (i) the actual per-run counts vary more than that single figure
suggests (96–98/103, 5–7 timeouts, per the table above) and (ii) the paragraph does not mention
that the automated classifier recorded `NEW` for all five of them at the time — a materially
misleading omission for a future reader who trusts the step summary/promotion-streak mechanism,
since a per-node-id streak reset to 0 on every one of these six nights and nothing in the source
comment currently explains why. This is a documentation-accuracy fix, not a behavior change, and
belongs with the classifier-sync remediation below.

### The `unstable` marker's continued presence, checked against section 8.9's standing rule

TESTING_GUIDE.md 8.9 is explicit: "An indefinitely-quarantined test is itself a defect to
escalate, not a steady state that the marker lets a codebase settle into. A test still marked
`unstable` after two review cycles (roughly two months) with no promotion and no active repair
work in progress must get a task opened against it." This test's `unstable` marking dates to task
160 (2026-08-25, commit `25eadae8`) — roughly one week old as of this report, well inside the
two-review-cycle window, so the standing rule's escalation trigger has not fired on age alone. But
the rule also requires "no active repair work in progress" as a *joint* condition with staleness,
and that condition is worth addressing explicitly rather than left implicit, per this task's own
instruction that a "leave it quarantined" conclusion must be justified against 8.9, not assumed:

- **This is not a settle-and-forget quarantine.** Real repair work is actively in progress and
  partially landed: the classifier laundering-guard fix (`cfb9cb4a`) is done and tested, just not
  yet CI-verified (see the classifier-sync remediation below); the budget-widening avenue was
  tried and its failure recorded (2x widen, zero additional conclusive formulas, per this file's
  own `GATING_RECHECK_SOLVE_TIMEOUT_MS` comment); the `xdist_serial`/sibling-worker-contention
  avenue was tried and closed. This diagnosis adds one more closed avenue (the axioms) and opens
  one new, concrete lead (whether the axioms affect this specific gating path going forward) —
  which is itself the definition of active investigation, not indefinite parking.
- **The exit criterion is written, concrete, and unmet for a legitimate reason.** Per 8.9's
  default: 20 consecutive `unstable-watch` runs recording zero (TIMING-classified) failures, or a
  verified fix. Zero of the last six real runs count toward that streak — not because the test is
  actually flapping between TIMING and NEW, but because every one of the six was misclassified
  NEW by a bug that has already been fixed and simply never reached CI. That is a *measurement*
  gap in the promotion mechanism, not evidence the underlying instability is unrepaired or
  worsening.
- **What "leave it quarantined" means here, precisely:** this diagnosis does not recommend
  de-quarantining (the underlying performance floor shortfall is real, unresolved, and this task's
  non-goals forbid changing bimodal semantics or the oracle soundness core to fix it) or
  re-quarantining (nothing here indicates the existing marking is wrong or needs re-derivation).
  It recommends the marker **stay exactly as it is**, on the affirmative record above — active
  repair work in progress, one closed avenue added, one new avenue opened, and a promotion streak
  that is blocked by a now-fixed measurement artifact rather than a live semantic problem — not on
  the default inertia the standing rule exists to catch.
- **What would flip this conclusion:** if a follow-on task lands the classifier-sync remediation
  and 20 consecutive nights still fail to reach a clean TIMING streak (i.e., the real shortfall
  worsens or a new failure mode appears), 8.9's escalation trigger applies in full and a dedicated
  remediation task (distinct from this diagnosis) would be warranted at that point — plausibly
  converging with task 178's frame-axiom-cost work if the forward-looking risk in (c) materializes.

## What this diagnosis rules out

- **Not a semantic/soundness regression** — zero disagreements on all six runs, unconditionally.
- **Not caused by the Skolemized Seriality/Interpolation axioms** — those axioms were absent from
  the code that produced every one of the six failures (see (c)).
- **Not `xdist_serial`/sibling-worker contention** — already closed by prior investigation (see
  the source file's criterion (3) and (3b)); `unstable-watch.yml` runs the oracle tree with no
  `-n` flag at all, strictly stronger isolation than the marker provides, and this diagnosis found
  nothing to reopen that lead.
- **Not `max_rlimit`-related** — opt-in, never passed by this test's call sites.
- **Not a change in the oracle's own solve path** — `provider.py`/`translation.py`/the manifest
  are byte-identical between the stale CI checkout and current HEAD.
- **Not something `GATING_RECHECK_SOLVE_TIMEOUT_MS` or `MIN_CONCLUSIVE_GATING_FORMULAS` should be
  retuned to fix** — per this task's hard constraints, and because the shortfall is
  budget-independent in this range (already established: doubling the budget 20000→40000ms in
  2026-08-12/08-25 bought zero additional conclusive formulas).

## What remains open (for a follow-on remediation task, not this one)

0. **Complete the idle-host measurement this task required.** Run
   `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestGatingConclusiveScan::test_known_conclusive_population_self_consistent
   -v -m unstable -s` to completion on an idle (or at least uncontended) host at current HEAD, and
   record the resulting conclusive count, timeout count, and wall clock. This is the single
   concrete gap left by this report — see (b) above. Until it is done, "budget/contention, not a
   regression" remains well-supported by indirect evidence (code-path diffing, six real CI runs'
   zero-disagreement history, prior same-class-hardware derivations) but not itself a fresh
   measured fact for the axiom-bearing code now on `origin/master`.
1. Confirm the classifier fix (`cfb9cb4a`) actually reaches a real `unstable-watch` run now that
   `origin/master` has caught up, and confirm the next run(s) classify TIMING rather than NEW.
2. Re-measure this gating test's conclusive count once a real CI run finally executes the
   Skolemized Seriality/Interpolation axioms inside `Z3OracleProvider`'s `BimodalSemantics`
   construction — the forward-looking risk in (c) above is currently untested.
3. Close the documentation gap in (d): correct or annotate the "(3b)" paragraph to record the
   actual per-run classify verdicts, not just durations.
4. Per TESTING_GUIDE.md section 8.9's standing rule (an indefinitely-quarantined test is itself a
   defect to escalate), this diagnosis's own conclusion — that the underlying performance floor
   shortfall is real, unresolved, and unrelated to a fixable bug — means the `unstable` marker
   itself is the correct steady state for now (its 20-consecutive-`TIMING`-run exit criterion has
   not been reached and cannot be, retroactively, given six runs' worth of `NEW`
   misclassification); this diagnosis does not recommend de-quarantining or re-quarantining, per
   the task's own constraint, and explicitly does not treat "leave it quarantined" as the default
   without this justification.
