# Research: Marking `TestGatingConclusiveScan` Unstable, the 7-Formula Question, and the `xdist_serial` Lead

## Task

Task 160. The oracle floor's `GATING_RECHECK_SOLVE_TIMEOUT_MS` widening (20000ms -> 40000ms) has
now been verified on real CI at commit 93cda5b9 (2026-08-25) and bought zero additional conclusive
formulas (identical 96/103, 7 timeouts, 0 disagreements to the pre-widening measurement). Per the
task description this closes the "widen the budget" avenue and unblocks the documented fallback:
mark `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` `unstable` under
the same four entry criteria used for `BM_CM_1`. This report covers the three sub-questions the
task poses: (a) the exact mechanical steps and marker text, (b) whether the same 7 formulas
time out across runs, (c) the `xdist_serial` isolation lead. No CI verification was re-run and no
widening of `GATING_RECHECK_SOLVE_TIMEOUT_MS` or lowering of `MIN_CONCLUSIVE_GATING_FORMULAS` is
proposed anywhere below, per the task's explicit constraints.

## (c) The `xdist_serial` lead — checked first, because it changes the shape of (a)

The task description frames `xdist_serial` isolation as "one open lead the widening never
tested," on the premise that "this test is not `xdist_serial`-marked, so
`oracle/run-oracle-suite.sh`'s `-n 6` pass runs it alongside five other workers on a 4-vCPU
runner." That premise does not hold against the current repository state:

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` line 2340 carries
  `@pytest.mark.xdist_serial` directly on `class TestGatingConclusiveScan` (the class holding
  exactly one test method, `test_known_conclusive_population_self_consistent`). This was added in
  commit `b81c2912` ("task 138 phase 5: gating conclusive-population assertion", 2026-08-06) — six
  days before either CI shortfall run — not something landed after the fact. The class docstring
  states the rationale explicitly: "Marked `xdist_serial`, not `slow`: this runs in
  `oracle/run-oracle-suite.sh`'s contention-free serial pass (zero sibling pytest workers), so
  `MIN_CONCLUSIVE_GATING_FORMULAS` is a deterministic floor rather than a contention-dependent
  one."
- `oracle/run-oracle-suite.sh`'s own header comment corroborates: "The gating conclusive-population
  scan (`TestGatingConclusiveScan`, see TESTING_GUIDE.md section 8.8) is marked `xdist_serial` for
  the same contention reason and so runs in this second pass" (the zero-sibling-worker serial
  pass, not the `-n 6` parallel pass).
- More directly: the CI workflow that actually recorded both shortfall runs,
  `.github/workflows/differential-tests.yml`, invokes this file with a **plain, non-`-n`** pytest
  call: `pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py -v -m "not slow and
  not differential and not unstable" --timeout=1500`. There is no `pytest-xdist` `-n` flag
  anywhere in that step, so no sibling pytest workers exist to contend with in the first place —
  `run-oracle-suite.sh`'s two-pass split is a different entry point (used for the full oracle
  suite locally/nightly), not the one `differential-tests.yml` uses. The workflow's own inline
  comment already says as much: "`TestGatingConclusiveScan`... is `xdist_serial` (it already runs
  alone, so this is a genuine budget-too-tight issue rather than worker contention)."

**Conclusion on (c):** the `xdist_serial` isolation lead, as literally described in the task text,
is not an untried remedy — the marker has been in place since before either recorded shortfall,
and the specific CI job that produced both shortfall runs (and the 40000ms re-verification run)
never had `pytest-xdist` worker contention to isolate from in the first place (no `-n` flag is
used there at all). Applying `xdist_serial` isolation a second time, or to a workflow that already
runs the test alone, would not change anything measurable. This also strengthens item (3)'s
existing "CI hardware/contention" hypothesis by elimination: `pytest-xdist` sibling-worker
contention specifically is ruled out (the mechanism was never live for this workflow's failing
runs), narrowing the live candidates to (i) the runner's raw hardware being weaker than the
24-core/30GB derivation host (already the leading hypothesis per item 3's `taskset` finding, which
showed 2-core restriction alone does *not* reproduce the shortfall locally) or (ii) noisy-neighbor
contention from other work sharing the same physical GitHub-hosted VM host — a different
mechanism than `pytest-xdist` worker contention, and one that cannot be tested by any marker
change in this repository. Neither hypothesis is actionable without infrastructure the task does
not ask this report to pursue (and both are consistent with "genuinely not budget-independent
noise, therefore `unstable` is the correct category").

One correction worth logging at the marker site so a future reader does not re-open this lead:
record that `xdist_serial` was already in place for both shortfall-producing runs, not merely
"not yet tried."

## (b) Are the same 7 formulas timing out across the recorded runs?

**Not determinable from currently available CI logs or artifacts, and this report does not
re-run CI to find out (per the task's explicit constraint).** Concretely:

- `differential-tests.yml` has no `actions/upload-artifact` step anywhere in the file — nothing
  from the run is preserved beyond the captured stdout/stderr log that `gh run view --log-failed`
  already surfaces.
- The captured logs for both shortfall runs (`31628414697`, 2026-08-12, v1.3.0 tag push; and
  `31628228088`, 2026-08-12, master push — both pulled fresh via `gh run view <id> --log-failed`
  for this report) print only the aggregate line `_assert_scan_report` unconditionally emits:
  `scan report: agreements={N} disagreements=0 timeout_count={N} conclusive={N}/103`. Neither
  run's log contains a per-formula breakdown.
- `_generate_differential_report()` (the shared scan core) supports three optional
  instrumentation parameters that would make per-formula identity recoverable: `progress_path`
  (JSONL, one record per formula), `heartbeat_every` (stdout lines for every disagreement/timeout/
  slow-solve), and `artifact_dir` (writes `report.json` plus a `SCAN_COMPLETE` marker).
  `TestGatingConclusiveScan.test_known_conclusive_population_self_consistent`'s actual call site
  passes none of them — only `oracle`, `conclusive_formulas`, `ref_fn`, `oracle_ids`, and
  `timeout_ms`. So even a fully successful re-fetch of CI logs cannot recover per-formula
  identity; the instrumentation that would have recorded it was never enabled for this call site.
- The manifest file consumed by this test,
  `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json`, records only `index` and
  `formula_json` per entry (103 entries) plus aggregate metadata (`conclusive_count`,
  `disagreements`, `wall_clock_seconds`, a prose `notes` field). It carries no per-formula solve
  time or historical timeout-membership field that could substitute for direct CI evidence.

What the counts alone do show: run `31628414697` recorded `timeout_count=7`, run `31628228088`
recorded `timeout_count=8`. The counts differ, which is itself evidence against a single, always-
identical fixed subset across every run (a strictly deterministic same-7-every-time story is ruled
out by the 8 in the second run) — but it does not rule out a *largely* stable, heavy-tailed subset
where most of the same formulas recur with occasional membership churn at the margin (which is
exactly the pattern task 159's investigation documented for `BM_CM_1`'s heavy-tailed draws, and
for `MIN_CONCLUSIVE_GATING_FORMULAS`'s own derivation note describing "7 formulas gained
conclusiveness and 7 different formulas lost it" between manifest re-derivations). Distinguishing
"same core subset with 1-formula churn" from "genuinely different formulas each run" requires
per-formula data this report cannot fabricate and was instructed not to go generate via a fresh CI
run.

**Recommendation for the marker's entry-criteria text:** record honestly that formula-level
identity is unknown with currently available evidence, rather than asserting a same-7 claim that
cannot be backed. If a future round of work wants this data without spending a full re-verification
CI run's worth of ambiguity, the actionable path is to route `TestGatingConclusiveScan` through
`_generate_differential_report`'s existing `progress_path` or `artifact_dir` parameters on a
future (non-gating, since it would already be `unstable` by then) run — infrastructure this repo
already has, unused only because this call site never opted in. This is a note for a possible
future round, not a step this task performs.

## (a) Mechanical steps and marker text to mark the test `unstable`

### Code change 1 — the marker itself

`test_known_conclusive_population_self_consistent` is the sole method of `TestGatingConclusiveScan`
in `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (currently at line ~2366,
directly below the class's existing `@pytest.mark.xdist_serial` and `setup_method`). Add
`@pytest.mark.unstable` directly above the method (method-level, not class-level — precise and
consistent with how `test_bimodal.py`'s `UNSTABLE_EXAMPLES` marks individual parametrized cases
rather than a whole class):

```python
@pytest.mark.xdist_serial
class TestGatingConclusiveScan:
    """...(existing docstring, unchanged)..."""

    def setup_method(self):
        from bimodal_logic import Z3OracleProvider
        self.oracle = Z3OracleProvider()

    # `unstable`-marked: see the entry-criteria block immediately above
    # GATING_RECHECK_SOLVE_TIMEOUT_MS's definition and TESTING_GUIDE.md section 8.9.
    # Both `xdist_serial` (class-level, unaffected by this marking -- the two markers
    # are orthogonal, one about worker contention, one about a documented residual
    # instability) and `unstable` apply to this single test method.
    @pytest.mark.unstable
    def test_known_conclusive_population_self_consistent(self):
        """...(existing docstring, unchanged)..."""
```

### Code change 2 — the four-criteria entry-comment block

Per TESTING_GUIDE.md 8.9, all four criteria must be recorded explicitly at the marker's source
site. The most natural location is directly above `GATING_RECHECK_SOLVE_TIMEOUT_MS`'s existing
comment block (which already documents items 1-3's measurement history in full and already
predicted this exact fallback — its final lines say "The documented fallback is therefore
UNBLOCKED... deferred to the follow-up task"), extended to record that the fallback has now been
exercised. Proposed text (to append to/amend that existing comment block, replacing its stale
"USER ACTION REQUIRED... NOT YET VERIFIED" tail):

```
# VERIFIED ON REAL CI (2026-08-25, commit 93cda5b9, Differential Oracle Tests workflow):
# scan report: agreements=96 disagreements=0 timeout_count=7 conclusive=96/103 -- BYTE-FOR-BYTE
# IDENTICAL to the pre-widening 20000ms measurement (run 31628414697: 96/103, 7 timeouts, 0
# disagreements). Doubling the budget bought zero additional conclusive formulas: the shortfall
# is budget-independent in this range on CI hardware, exactly as this comment's own "essentially
# budget-independent" prediction (above) anticipated. Do not widen this constant again and do not
# re-verify expecting a different answer.
#
# THE FALLBACK IS NOW EXERCISED: test_known_conclusive_population_self_consistent is marked
# `unstable` (see @pytest.mark.unstable directly above that method) per TESTING_GUIDE.md section
# 8.9's four entry criteria, recorded here:
#
# (1) WHAT FAILS AND WHY -- `_assert_scan_report`'s performance-floor assertion
#     (`conclusive >= min_conclusive`) fails on real CI: 96/103 conclusive, 7 timeouts (run
#     31628414697, v1.3.0 tag push, 2026-08-12); 95/103, 8 timeouts (run 31628228088, master
#     push, 2026-08-12); 96/103, 7 timeouts again at 2x budget (commit 93cda5b9, 2026-08-25).
#     Local runs of the identical unmodified test resolve 103/103 with zero timeouts, both
#     unrestricted on 24 cores (194.64s) and CPU-restricted to 2 cores via `taskset -c 0,1`
#     (176.06s, no degradation) -- ruling out genuine per-formula solver cost growth and pointing
#     at CI-runner-specific hardware/contention (GitHub's 4 vCPU/16GB standard runner vs. the
#     24-core/30GB derivation host) as the live, still-unconfirmed hypothesis.
#
# (2) DEMONSTRABLY NOT SEMANTIC -- zero disagreements on every recorded CI run, including the
#     shortfall runs and the re-verification run. `_assert_scan_report` asserts disagreements==0
#     and the conclusive floor as two SEPARATE assertions, in that order; only the second has
#     ever fired. The failure is always `conclusive < min_conclusive` reported as "budget/
#     performance regression to investigate, not a semantic one" (that literal string is this
#     assertion's own message), never a changed verdict on any decided formula.
#
# (3) GENUINE FIX ATTEMPTED AND ITS FAILURE RECORDED -- GATING_RECHECK_SOLVE_TIMEOUT_MS doubled
#     20000 -> 40000ms (2026-08-12) and verified on real CI (2026-08-25, commit 93cda5b9):
#     identical 96/103, 7 timeouts -- zero additional conclusive formulas bought by 2x budget.
#     2-core local CPU restriction does not reproduce the shortfall (103/103 either way), ruling
#     out genuine harness cost growth. This test already carries `@pytest.mark.xdist_serial`
#     (added task 138 phase 5, 2026-08-06, six days before either shortfall run) and
#     differential-tests.yml's invocation of it uses no `pytest-xdist` `-n` flag at all -- so
#     pytest-xdist sibling-worker contention was never live for either recorded shortfall run,
#     ruling that specific mechanism out too (distinct from the still-live shared-host noisy-
#     neighbor hypothesis, which no marker change can test). MIN_CONCLUSIVE_GATING_FORMULAS is
#     deliberately NOT lowered -- it encodes a real quality property; lowering it is the
#     assertion-weakening this policy exists to forbid.
#
# (4) EXIT CRITERION -- verbatim per TESTING_GUIDE.md section 8.9's default: the marker comes off
#     when EITHER 20 consecutive unstable-watch runs record zero (TIMING-classified) failures
#     (nightly cadence, ~3 weeks), OR a genuine fix (a CI-runner/harness change, NOT a further
#     budget widening -- see (3) above) demonstrated to close the shortfall across a re-
#     verification run with 103/103 conclusive and 0 disagreements. A single green run never
#     qualifies.
```

Cross-reference this new block from `test_known_conclusive_population_self_consistent`'s own
docstring with a one-line pointer, mirroring how `test_bimodal.py` keeps its four-criteria prose
at the `UNSTABLE_EXAMPLES` site rather than duplicating it at the parametrize call site.

### Workflow change 1 — `unstable-watch.yml`'s classifier must be extended, not left as-is

This is the step most likely to be missed by treating "mark unstable" as pure copy-paste from
`BM_CM_1`'s pattern, and it matters: **without it, this test would fail the nightly `unstable-watch`
job loudly every time the underlying shortfall reproduces, which both defeats the point of quiet
observation and prevents the 20-consecutive-green-run streak from ever accumulating on nights the
flake actually manifests** — exactly backwards from what marking it `unstable` is meant to buy.

The mechanics: `unstable-watch.yml`'s `watch_oracle` step already selects `-m unstable` against
`oracle/bimodal_logic/tests/`, so this test will automatically be picked up once marked — no
workflow-level *inclusion* edit is needed there. But its `classify()` function's TIMING signature
is hard-coded to `BM_CM_1`'s shape: `MAX_TIME_BY_NODEID_FRAGMENT` maps a nodeid substring to a
single numeric `max_time`, and TIMING requires `duration >= 0.8 * max_time` **and**
`FAILURE_SIGNATURE ("Test failed for example:") in failure_text`. Neither half transfers:

- There is no single `max_time` for this test — its budget is `GATING_RECHECK_SOLVE_TIMEOUT_MS`
  (40000ms) applied *per formula*, up to 103 formulas, so total wall-clock varies with how many
  formulas actually hit the per-formula budget (observed ~450s for the method itself across the
  two recorded failing runs). A single duration threshold analogous to BM_CM_1's is not a natural
  fit.
- The failure text is structurally different: `_assert_scan_report`'s conclusive-floor assertion
  raises `"Only {conclusive} of {total} formulas were conclusive (floor={min_conclusive}); this is
  a budget/performance regression to investigate, not a semantic one."` — never
  `"Test failed for example:"`. Any node id not present in `MAX_TIME_BY_NODEID_FRAGMENT` falls
  through `classify()`'s explicit `if max_time is None: return "NEW"` branch, so every occurrence
  would be classified `NEW` (and fail the job, per the script's own contract: "Exits non-zero...
  only when a NEW-classified failure is found") without a dedicated code path.

Critically, `_assert_scan_report` has a **second**, semantically different assertion
(`disagreements == 0`, message `"Self-comparison produced {N} disagreements among conclusive
results: {list}"`) that must never be classified TIMING under any circumstance — a disagreement is
a real soundness bug, not the documented residual instability. Any classifier extension must gate
strictly on the conclusive-floor message text (and ideally also confirm `disagreements=0` appears
in the surrounding captured output) so a genuine future disagreement failure on this same test
still surfaces loudly as `NEW`, not silently absorbed as TIMING.

Concretely, this requires a second signature branch in `classify()` (or an equivalent generalized
dispatch), something in the shape of:

```python
GATING_FLOOR_SIGNATURE = "budget/performance regression to investigate, not a semantic one"
GATING_FLOOR_NODEID_FRAGMENT = "test_known_conclusive_population_self_consistent"

# inside classify(), before falling back to the max_time-based BM_CM_1 path:
if GATING_FLOOR_NODEID_FRAGMENT in nodeid:
    if GATING_FLOOR_SIGNATURE in failure_text and "disagreements=0" in failure_text:
        return "TIMING"
    return "NEW"
```

(The exact shape is an implementation decision for whoever lands this, not prescribed further
here — this report's job is to establish that the classifier extension is a necessary, not
optional, companion change, and to name the precise message strings and the disagreements-must-
never-be-masked constraint a correct implementation has to honor.)

Two more small `unstable-watch.yml` touch-ups belong alongside the classifier change:
- The `watch_oracle` step's inline comment currently reads "After this task's landing, the oracle
  tree has no unstable-marked test, so this branch is expected to hit exit code 5 every run" —
  this becomes false once this marking lands and must be corrected (the oracle tree will then have
  exactly one unstable-marked test, this one).
- `MAX_TIME_BY_NODEID_FRAGMENT`'s own comment ("UPDATE THIS DICT whenever a new test is marked
  `unstable`") should be updated to point at wherever the new signature constant/branch lives, so
  a future third `unstable` marking has one place to look, not two divergent patterns to discover
  independently.

### Workflow change 2 — `differential-tests.yml` (verify, likely no functional edit needed, one stale comment)

The gating step's `-m` expression is already `"not slow and not differential and not unstable"` —
the `and not unstable` clause is already present, so no functional edit is needed there; the test
will be automatically excluded from this gating step the moment the marker lands. What *is* now
stale: the step's large inline comment justifying `--timeout=1500` (raised from 900) walks through
an estimate that assumes `TestGatingConclusiveScan` still runs in this step, factoring in "7-8
formulas timing out... roughly another 140-160s, landing near ~780s against the OLD 900s cap."
Once this test is excluded via the `unstable` marker, that rationale no longer describes what the
step actually runs and should be annotated (not necessarily reverted — 1500s is still a safe,
harmless value, and TESTING_GUIDE.md 8.9 does not require the timeout be re-tightened) so a future
reader does not treat the stale estimate as live reasoning about the current step's composition.

### TESTING_GUIDE.md section 8.9 update

The "Currently marked" paragraph (lines ~964-969) currently names only `BM_CM_1`. It should be
extended with a second bullet for `TestGatingConclusiveScan::test_known_conclusive_population_
self_consistent`, following the same one-line-pointer-to-the-source-of-truth convention already
used for `BM_CM_1` rather than duplicating the full four-criteria text into the guide itself.

### Verification of the mechanical change (no CI re-run required)

Local-only checks that confirm the marker mechanics work without touching CI:
- `pytest --collect-only -m unstable oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
  should collect exactly this one test.
- `pytest --collect-only -m "not unstable" oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
  should now exclude it (confirming it drops out of `differential-tests.yml`'s gating step without
  needing to run the suite on CI).
- `oracle/conftest.py`'s `pytest_configure` registration for `unstable` (already present, shared
  with `test_bimodal.py`) needs no change — the marker is already a registered, repo-wide name.

## Summary of findings against the task's three sub-questions

- **(a)** The mechanical marker addition is a one-line `@pytest.mark.unstable` plus a four-criteria
  comment block (drafted above, extending `GATING_RECHECK_SOLVE_TIMEOUT_MS`'s existing comment
  rather than duplicating it) — but the marking is not complete without also extending
  `unstable-watch.yml`'s `classify()` function with a new, message-content-based TIMING signature
  for this test's distinct failure shape, since its existing `max_time`-based, `BM_CM_1`-specific
  signature does not and cannot recognize this test's failures, and leaving it unextended would
  cause every real occurrence to be misclassified `NEW`, defeating the entire point of the
  marking.
- **(b)** Per-formula identity of the timing-out formulas is not recoverable from any currently
  available CI log or artifact (no artifact upload exists, and the call site does not pass any of
  `_generate_differential_report`'s available instrumentation parameters). The raw counts (7 vs. 8
  timeouts across the two recorded shortfall runs) show the timeout set is not perfectly identical
  run-to-run, but cannot distinguish a mostly-stable subset with minor churn from a genuinely
  different set each time.
- **(c)** The `xdist_serial` isolation lead is not actually untried: the test has carried
  `@pytest.mark.xdist_serial` since 2026-08-06 (task 138 phase 5), predating both recorded
  shortfall runs, and the specific CI workflow that produced those runs never invokes
  `pytest-xdist` with `-n` in the first place — so there was no sibling-worker contention to
  isolate from. This rules out `pytest-xdist` worker contention specifically as the shortfall's
  cause (narrowing, not just failing to narrow, the live hypothesis space toward CI-host
  hardware/noisy-neighbor contention already named in item 3), and should be corrected at the
  marker site rather than re-attempted.

## Files referenced

- `/home/benjamin/Projects/ModelChecker/oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
  (lines ~96-171 for `GATING_RECHECK_SOLVE_TIMEOUT_MS`/`MIN_CONCLUSIVE_GATING_FORMULAS`; ~700-734
  for `_assert_scan_report`; ~1626-1686 for `_generate_differential_report`'s signature; ~2340-2396
  for `TestGatingConclusiveScan`)
- `/home/benjamin/Projects/ModelChecker/oracle/run-oracle-suite.sh`
- `/home/benjamin/Projects/ModelChecker/.github/workflows/differential-tests.yml`
- `/home/benjamin/Projects/ModelChecker/.github/workflows/unstable-watch.yml`
- `/home/benjamin/Projects/ModelChecker/oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`
  (lines ~56-110, `UNSTABLE_EXAMPLES` pattern)
- `/home/benjamin/Projects/ModelChecker/code/docs/core/TESTING_GUIDE.md` (section 8.9, lines ~900-970)
- `/home/benjamin/Projects/ModelChecker/specs/archive/159_fix_bimodal_flake_and_unstable_category/reports/01_bimodal-flake-and-unstable-category.md`
- CI runs consulted via `gh run view <id> --log-failed`: `31628414697`, `31628228088` (both
  2026-08-12); run history for commit `93cda5b9` (2026-08-25 re-verification, referenced from the
  task description; not independently re-fetched beyond what the task description already quotes,
  per the "do not re-run/re-verify" constraint)
