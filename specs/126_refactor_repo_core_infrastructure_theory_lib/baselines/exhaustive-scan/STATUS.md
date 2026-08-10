# Exhaustive-scan coverage record

**Run:** 2026-08-10T02:20:56Z-03:29:12Z (68m16s wall clock, `SCAN_COMPLETE`'s own
`wall_clock_seconds: 3555.065` for the scan itself; the extra ~2 min is pytest session
start/teardown plus the `-m slow` collection of the second test below).
**Command:** `nix develop --command bash oracle/run-oracle-exhaustive-scan.sh` (attempt 3; attempts
1 and 2, both unadjudicable on CPU contention, are recorded in `../oracle-baseline-STATUS.md` and
`../gate-run-2026-08-09/exhaustive-attempt{1,2}-*`).
**Output directory:** `oracle/scan-results/20260810T022056Z/` (gitignored; `report.json` and
`SCAN_COMPLETE` promoted here, `progress.jsonl` deliberately not copied per the plan — the report
supersedes it).

## Completion (marker-established, never PID-inferred)

`SCAN_COMPLETE` exists:

```json
{
  "status": "complete",
  "total_formulas": 274,
  "conclusive": 105,
  "disagreements": 0,
  "timeout_count": 169,
  "wall_clock_seconds": 3555.065
}
```

This is attempt 3's headline result: unlike attempts 1 and 2, **this run reached completion** and
is therefore adjudicable.

## Two `slow` tests ran; one passed, one failed

`pytest oracle -m slow -s` selects exactly 2 tests (matching Phase 1's collection count). Both ran
in the same invocation:

| Test | Class | Result |
|---|---|---|
| `TestFullScanReport::test_complexity_5_scan_self_consistent` | writes `report.json`/`SCAN_COMPLETE`; asserts zero self-disagreements with a `conclusive >= MIN_CONCLUSIVE_SCAN_FORMULAS` (90) floor | **PASSED** — 105 conclusive >= 90, 0 disagreements |
| `TestBimodalHarnessIntegration::test_temporal_only_agreement_complexity_5` | 5 ordered assertions cross-checking MC against BimodalHarness Z3 at complexity<=5 (the same assertions Phase 5 re-scoped `verify-refactor.sh` Step 5 against) | **FAILED** — signature-check assertion (line 1454) |

Because the runner drives both tests in one `pytest` invocation, the summary block's overall
`pytest: FAILED (exit 1)` reflects the second test, not the scan itself. Read literally against
Phase 4's two pre-declared verification branches, this run satisfies neither branch cleanly (the
scan completed and its own self-consistency test passed, but the invocation's aggregate exit is
non-zero) — so both outcomes are recorded explicitly here rather than forced into either bucket.

### 1. Self-consistency scan: PASSED, completed, adjudicable

`test_complexity_5_scan_self_consistent` is the test that fulfils Phase 4's goal (accounting for
the exhaustive population). It passed: 0 disagreements among 105 conclusive formulas out of 274
enumerated, comfortably above the 90-formula floor.

**Contention caveat — read the timeout count as an upper bound, not a clean characterization.**
`specs/127_close_oracle_suite_regression_baseline/run3/contention-watch-phase4.log` recorded 68
samples at 60s intervals: 58 quiet, **9 CONTENTION** (foreign `lean`/`runLinter` processes above
50% CPU), peaking at `lean` 577% (02:31Z) and `runLinter` 772% (03:00Z), with load1 spiking to
7.78-8.88 around 03:00-03:01Z. Unlike attempts 1 and 2, this contention did **not** invalidate the
run — it still completed, and the self-consistency assertions still passed — but with 169/274
formulas (62%) hitting the 10s solve-budget timeout, sibling-project CPU contention during
~9/68 sampled minutes is a plausible contributor to some of those timeouts. The 169-timeout figure
is therefore recorded as an observation made under **partial** contention, not as a clean
characterization of solver capability at the deployed `SELF_SCAN_SOLVE_TIMEOUT_MS=10000` budget.
The 0-disagreements finding is unaffected by this caveat: it is scoped to the 105 formulas both
sides actually decided, and contention degrades decisiveness, not correctness.

### 2. Cross-oracle agreement test: FAILED — a new, undocumented external-defect signature

`test_temporal_only_agreement_complexity_5` failed on its 5th (signature-check) assertion:

```
1 entr(y/ies) in external_bh_defect do not match the documented signature
(mc_sat=False, bh_sat=True) -- this may be a DIFFERENT external defect than the one
recorded in oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md and requires its own
investigation, not silent inclusion in this bucket:
  {'tag':'imp','left':{'tag':'untl','event':{'tag':'atom','name':'p'},
   'guard':{'tag':'bot'}},'right':{'tag':'atom','name':'p'}}: MC=True, BH=False
```

The documented defect in `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md` has signature
`mc_sat=False, bh_sat=True`. This formula has the **opposite polarity**
(`mc_sat=True, bh_sat=False`), so the test's own assertion message is correct that this "may be a
different external defect" — it is not silently absorbed into the existing bucket, and this run
does not classify it further. **This is a genuine, non-environmental finding**, not a contention
artifact: the failure is a deterministic content check on classified formulas, not a timing-based
solve outcome.

Per this plan's own non-goals (Phase 3(c): "Diagnosing or repairing the underlying defects is an
explicit non-goal of this baselining task"), this finding is recorded and left for a follow-up
task, not investigated or reclassified here. `classify_disagreement`, `KNOWN_EXTERNAL_DEFECTS.md`,
and the assertion itself were **not** touched.

## Integrity

`git diff --stat -- oracle/bimodal_logic/` is empty. `SELF_SCAN_SOLVE_TIMEOUT_MS` (10000),
`MIN_CONCLUSIVE_SCAN_FORMULAS` (90), and `MIN_CONCLUSIVE_TEMPORAL_BH_FORMULAS` (45) are unchanged
from Phase 1's guard inventory. `known_conclusive_complexity5.json` was not re-derived.
`ORACLE_EXHAUSTIVE_TIMEOUT` was not altered (default 7200s budget; run finished in ~4096s of
pytest time, well inside it).

## Evidence

- `report.json`, `SCAN_COMPLETE`, `exhaustive-run.txt` (this directory) — the promoted scan
  artifacts and full tee'd pytest output, including the failure traceback.
- `../gate-run-2026-08-09/exhaustive-attempt3-machine-before.txt` — quiet-machine capture at
  launch (load1 0.97, no foreign process >50% CPU).
- `../gate-run-2026-08-09/exhaustive-attempt3-contention-watch.log` — the 68-sample, 60s-interval
  contention watch referenced above.
