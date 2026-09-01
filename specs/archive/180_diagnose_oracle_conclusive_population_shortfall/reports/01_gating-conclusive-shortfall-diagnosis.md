# Diagnosis: Oracle gating conclusive-population shortfall (unstable-watch, 2026-08-27 → 2026-09-01)

**Status of this report: diagnosis complete for the CI-observed failures, and the task's explicit
MEASUREMENT REQUIREMENT has now been executed to completion and recorded — see (b) below. The
local run reproduced the shortfall, at axiom-bearing current HEAD, and numerically *worse* than
every one of the six historical CI runs (93/103 conclusive vs. 96–98/103; 951.21s vs. 749–899s).
The measurement host was demonstrably **not idle** (load average ~5.9→~5.0 on 24 cores, several
concurrent `claude` sessions and editors running throughout), so this result does not cleanly
isolate contention from a possible axiom-driven cost increase — both remain live explanations,
honestly reported as such rather than picking one. See (b) for the full numbers and the
interpretive caveat.**

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
- **Idle-host re-measurement — COMPLETED. The shortfall REPRODUCED locally, and reproduced worse
  than every historical CI run.** `test_known_conclusive_population_self_consistent` was run to
  completion in the foreground on this research host at `HEAD=9ce3b4ad` (2026-09-01 05:21 -0700,
  "task 181: create implementation plan") via
  `PYTHONPATH=code/src timeout 2400 python3 -m pytest
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestGatingConclusiveScan::test_known_conclusive_population_self_consistent
  -v -m unstable -s`. `git merge-base --is-ancestor f9cc081e HEAD` confirms this run is
  axiom-bearing — the first measurement of this specific test with the 2026-08-31 Skolemized
  Seriality/Interpolation axioms actually present in the `BimodalSemantics` construction
  `Z3OracleProvider` calls internally, unlike any of the six CI runs in the table above.

  **Result:** `agreements=93 disagreements=0 timeout_count=10 conclusive=93/103`
  (`floor=100`), wall clock **951.21s (0:15:51)**, in `1 failed`. Zero disagreements — the
  soundness claim is intact, exactly as on all six CI runs; the failure is exclusively the
  performance floor, as designed. Individual timed-out-formula identities are **not recoverable**
  from this log, for the same pre-existing instrumentation-gap reason given in (a): pytest's
  assertion-introspection repr of the `report` dict truncates `entries` with `...`, and
  `unstable-watch`-style invocations of this test still pass none of
  `_generate_differential_report`'s `progress_path`/`heartbeat_every`/`artifact_dir` options.
  Getting the per-formula timeout set would require a second run with that instrumentation wired
  in — out of scope for this dispatch (no second multi-hundred-second run was started, per
  instruction), and it is remediation-shaped work regardless.

  **Host load — explicitly NOT idle, reported honestly rather than mislabeled:**

  | | 1-min | 5-min | 15-min |
  |---|---|---|---|
  | Before (`uptime`, 05:13:45) | 5.91 | 5.93 | 5.61 |
  | After (`uptime`, 05:29:59) | 4.77 | 5.14 | 5.28 |

  24 cores (`nproc`), 30GB RAM with 15GB used and **7.3GB of swap in use** at completion time. A
  `ps aux` snapshot taken immediately after the run shows at minimum four concurrent
  `claude --dangerously-skip-permissions` sessions (PIDs 1850738, 2092138, 2093786, plus this
  session), several `nvim` instances, and a `sioyek` PDF viewer, all resident and competing for
  the same 24 cores and 30GB throughout the run. A load average of ~5–6 on 24 cores is not the
  same severity of contention as a maxed-out box, but it is unambiguously **not idle**, and the
  swap usage is a second, independent contention signal beyond raw CPU load. This measurement
  should be read as "best available host, honestly characterized," not as a clean idle baseline.

  **Interpretation — two live explanations, deliberately not collapsed into one:** This local
  result (93/103, 951.21s) is numerically worse on both axes than every one of the six historical
  CI runs (96–98/103, 749–899s; see the table in (a)) — CI's supposedly-more-generic runner did
  *better* than this "idle-host" attempt. Two candidate explanations exist and this single,
  confounded data point cannot discriminate between them:
  1. **Axiom-driven cost increase.** This is the first measurement of this exact test with
     `f9cc081e` present. Task 178 already measured a real, `rlimit`-confirmed 4–6x solver-cost
     increase from the same two axioms in a different Z3 constraint context (the forward-looking
     risk this report's (c) already flagged, before any HEAD measurement existed). A worse result
     here is consistent with that risk having materialized in this path too.
  2. **Host contention.** Load ~5–6 plus active swapping on a shared, multi-session box is a real,
     independent alternative explanation for both the lower conclusive count and the longer wall
     clock, with no need to invoke the axioms at all.
  **What would discriminate between them:** a run of this same test, at this same `HEAD`, on a
  verifiably idle CI-class runner (load ~0, no swap) — or, cheaper, a run at the pre-axiom
  `98d3ad8d` checkout on *this* host under comparable (~load 5–6) contention, to see whether the
  contention alone reproduces a 93/103-class shortfall without the axioms. Neither run was
  performed in this dispatch (both are additional multi-hundred-second measurements, out of
  scope for a diagnosis-only dispatch that was explicitly told not to start another long run).
  This report does not pick one explanation over the other without that evidence — both are
  recorded as live, and the forward-looking risk in (c) is upgraded from "untested" to
  "consistent with one real, confounded data point," not to "confirmed."

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

**Forward-looking risk — partially observed as of this report, still not confirmed.**
`Z3OracleProvider` (the oracle `TestGatingConclusiveScan` exercises) constructs its own
`BimodalSemantics(settings)` internally (`oracle/bimodal_logic/provider.py:275`) and calls
`build_frame_constraints()`, which is exactly the function `f9cc081e` modified. `core.py` (home
of `build_frame_constraints`) differs by 152 lines between the stale checkout and current HEAD.
Task 178 (tracked separately, scoped to a different test —
`TestShiftClosure::test_shift_closure_on_extracted_worlds_m3`) already measured a real, `rlimit`-
count-confirmed 4–6x solver-cost increase from these same two axioms in a different Z3 constraint
context, which is what originally motivated flagging this as a risk before any HEAD measurement
of this specific test existed.

That measurement now exists (see (b)): a local, axiom-bearing run at `HEAD=9ce3b4ad` (which
includes `f9cc081e`) produced 93/103 conclusive in 951.21s, worse on both axes than every one of
the six pre-axiom CI runs (96–98/103, 749–899s). This is **consistent with** the axiom-cost risk
having propagated into this gating path, but the run was also on a demonstrably non-idle host
(load ~5–6 on 24 cores, active swapping — see (b)), so host contention remains an equally live,
untested-apart explanation. This report does **not** treat the risk as confirmed on this single
confounded data point, and does not treat it as ruled out either — (b) states explicitly what a
discriminating follow-up run would need to look like (same `HEAD`, verifiably idle CI-class
runner). Whoever owns the next observation of this test should treat this as a real, specific,
still-open risk, now backed by one suggestive (not conclusive) local measurement rather than pure
inference.

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

A second, now-concrete gap: this report's own (b) local measurement (93/103 conclusive, 10
timeouts, 951.21s at axiom-bearing HEAD) sits outside the "96/103 conclusive, 7-timeout" range
that "(3b)" and TESTING_GUIDE.md 8.9's "Currently marked" entry both cite as the test's signature.
That local run is a single, host-contended, non-CI data point — not itself grounds to rewrite the
documented signature, which is derived from six real CI runs this diagnosis has no reason to
distrust — but it is grounds to add one sentence noting that the signature was last confirmed
against pre-axiom code, and that the first post-axiom real CI run should be checked against it
explicitly rather than assumed to still hold. This is folded into the classifier-sync/documentation
remediation in item 3 below, not treated as an update to the signature itself.

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

- **Not a semantic/soundness regression** — zero disagreements on all six CI runs, and zero again
  on this report's own axiom-bearing local measurement (see (b)) — seven-for-seven now,
  unconditionally.
- **Not caused by the Skolemized Seriality/Interpolation axioms, for the six CI runs specifically**
  — those axioms were structurally absent from the code that produced every one of the six
  failures (see (c)). This does **not** extend to current, axiom-bearing `HEAD`: a local
  measurement at `HEAD` (which does contain the axioms) reproduced the shortfall worse than any
  CI run, and whether the axioms contributed to that or host contention alone explains it is an
  open question this diagnosis states explicitly rather than resolving one way or the other (see
  (b) and (c)'s forward-looking-risk paragraph).
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

**Cross-reference (added at task 180's closure):** items 0a, 1, and 2 below have been consolidated into task 183 ("discriminate_gating_shortfall_axiom_vs_contention"), which carries their full context and this diagnosis's hard constraints forward verbatim. Item 3 (the "(3b)" documentation gap) was closed directly by task 180's own plan, not deferred — see the corrected entry-criteria block in `test_cross_oracle_differential.py`. Item 4 (the marker's continued presence) is this diagnosis's own recorded conclusion and needs no further task.

0. ~~Complete the idle-host measurement this task required.~~ **DONE, see (b).** A local run at
   axiom-bearing `HEAD=9ce3b4ad` completed in 951.21s with 93/103 conclusive (10 timeouts, 0
   disagreements) — the shortfall reproduced, and reproduced worse than every CI run. The host was
   not idle (load ~5–6 on 24 cores, active swapping, four-plus concurrent `claude` sessions), so
   this closes the measurement gap honestly rather than by mislabeling a contended run as idle;
   item 0a below is the residual, genuinely still-open sub-question this measurement opens up.
0a. **New, more specific open question this measurement raises:** discriminate axiom cost from
    host contention as the cause of the 93/103/951.21s result. Needs either (i) the same test at
    the same `HEAD` on a verifiably idle CI-class runner, or (ii) the same test at the pre-axiom
    `98d3ad8d` checkout on a comparably-loaded host, to see whether contention alone reproduces a
    93/103-class shortfall without the axioms. Neither run is performed by this diagnosis (both
    are additional multi-hundred-second measurements and this is a diagnosis-only dispatch).
1. Confirm the classifier fix (`cfb9cb4a`) actually reaches a real `unstable-watch` run now that
   `origin/master` has caught up, and confirm the next run(s) classify TIMING rather than NEW.
2. Re-measure this gating test's conclusive count once a real CI run finally executes the
   Skolemized Seriality/Interpolation axioms inside `Z3OracleProvider`'s `BimodalSemantics`
   construction on an uncontended runner — this report's (b) local measurement is suggestive
   (worse than every historical CI run) but confounded by host load, so the forward-looking risk
   in (c) remains open rather than confirmed; a clean CI-runner data point at axiom-bearing HEAD
   would resolve it either way.
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
