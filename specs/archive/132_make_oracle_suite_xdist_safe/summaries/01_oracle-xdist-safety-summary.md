# Implementation Summary: Make the Oracle Suite xdist-Safe

- **Task**: 132 - make_oracle_suite_xdist_safe
- **Status**: COMPLETED
- **Plan**: specs/132_make_oracle_suite_xdist_safe/plans/01_oracle-xdist-safety.md
- **Research**: specs/132_make_oracle_suite_xdist_safe/reports/01_oracle-xdist-safety.md

## Overview

The `oracle/` test suite's five xdist-only failures were not caused by any shared state between
worker processes — each affected test builds its own private `Z3OracleProvider()`, and the one
process-local module attribute involved (`z3.z3._main_ctx`) cannot cross xdist's worker-process
boundary. The real mechanism is CPU-contention-induced Z3 solve-time inflation tripping tight
`max_time`/`timeout_ms` budgets, which the oracle pipeline reports as `None` (no countermodel)
rather than as an error (see `code/docs/core/TESTING_GUIDE.md` section 8.6). This implementation
introduces a new `xdist_serial` pytest mark, an `oracle/conftest.py` that registers it (plus the
previously ini-discovery-orphaned `differential` and `slow` marks), and a two-invocation split
runner script that runs the bulk of the suite under `-n 6` and the seven contention-sensitive
tests serially with zero sibling workers.

## What Was Implemented

### Phase 1 — `oracle/conftest.py`

New file registering three marks via `pytest_configure`: `differential` and `slow` (mirroring
`code/pyproject.toml`'s existing descriptions, closing an ini-discovery gap — `code/pyproject.toml`
is a sibling of `oracle/`, not an ancestor, so a `pytest oracle/`-rooted invocation never reaches
it) and the new `xdist_serial` mark. A `pytest_collection_modifyitems` hook applies
`xdist_serial` to exactly two parametrized cases by matching both function name and id fragment:
`test_enriched_vs_primitive_sat_agreement[some_past]` and
`test_regression_all_active_examples[BM_CM_1...]`. This idiom was required instead of the more
obvious `pytest.param(..., marks=...)` because `ENRICHED_PRIMITIVE_PAIRS` feeds three
`ids=[p[0] for p in ENRICHED_PRIMITIVE_PAIRS]` comprehensions and `regression_examples` feeds
several `.items()` consumers — both would break under the `pytest.param` wrapping idiom.

### Phase 2 — static decorators

Added `@pytest.mark.xdist_serial` at class level to `TestStateIsolationRegression`
(`oracle/bimodal_logic/tests/test_soundness_regression.py`), covering all four methods — the two
originally observed failing plus two same-risk siblings that share the identical `setup_method`
and unmodified `timeout_ms=5000` default. Added the mark at method level to
`TestOracleMFormulaBoundarySafe.test_oracle_m_formula_depth1_boundary_safe` only (the sibling
depth0 test has ample margin; the depth2 test asserts `result is None`, so a spurious timeout
cannot invert its verdict).

### Phase 3 — runner script and documentation

New executable `oracle/run-oracle-suite.sh`: guards against running outside the Nix devShell
(checks `import xdist`), defaults `PYTHONPATH` to `code/src` resolved from the script's own
location, runs pass 1 (`-n 6 -m "not xdist_serial"`) then pass 2 (`-m "xdist_serial"`, no `-n`),
captures both exit codes, and prints a two-line pass/fail summary. `set -uo pipefail` (not `-e`)
so pass 1 failing does not prevent pass 2 from running. Added a "Running the Test Suite" section
to `oracle/bimodal_logic/README.md` documenting the one-command invocation, the contention
mechanism the split routes around, and the convention for marking future tight-budget tests.

### Phase 4 — validation

Ran the serial pass first, then the parallel pass in the background (run_in_background, given its
~44-minute wall-clock exceeds the foreground Bash ceiling), and compared verdicts.

## Measured Results

| Pass | Command | Result | Wall-clock |
|------|---------|--------|------------|
| Serial | `pytest oracle/ -m "xdist_serial" -q` | `7 passed, 543 deselected` | 374.27s (0:06:14) |
| Parallel | `pytest oracle/ -n 6 -m "not xdist_serial" -q` | `1 failed, 533 passed, 9 xfailed` | 2779.96s (0:46:19) |

Combined two-pass wall-clock: ~52:33. A hypothetical fully-serial run of the whole 550-item suite
(extrapolating from the 90-minute full `-n 6` baseline referenced in the research report, which
takes ~44 min under `-n 6` for the parallel-eligible 543 alone) would be substantially slower;
the two-pass split preserves nearly all of the `-n 6` wall-clock benefit for the bulk of the
suite while isolating only the 7 tight-budget items.

**Coverage accounting**: 1 (failed) + 533 (passed) + 9 (xfailed) = 543 (parallel pass) + 7 (serial
pass, all passed) = 550. Full accounting — no tests lost or double-counted between the two passes.

**Failure count**: went from 7 (the original full-`-n 6` baseline that motivated this task) to 1
in this validation run. The two-pass split cleared all five previously-observed xdist artifacts,
plus the two `TestStateIsolationRegression` siblings that were marked as same-risk (never
independently observed failing, but sharing the identical setup and timeout default).

**Sole remaining failure**: `test_cross_oracle_differential.py::TestFullScanReport::
test_complexity_5_scan_self_consistent` — the known pre-existing self-consistency defect. This
fails at HEAD and at the pre-refactor baseline alike; it is owned by a separate task and was not
touched here.

## Correction to a Plan Assumption: `all_future`

The plan's Non-Goals section, following the research report, treated
`test_enriched_vs_primitive_sat_agreement[all_future]` as a confirmed slow-solver-path defect that
"genuinely exceeds even the widened 180000ms budget" (based on two isolated samples of 195.47s /
187.63s). **This measured validation run corrects that assumption**: `all_future` is not in the
7-item `xdist_serial` set and does not appear in the parallel pass's failure list — it passed
while running under full six-way CPU contention, strictly worse conditions than the isolated
samples that motivated the original claim. Given the ~20x Z3 solve-time variance documented in
`code/docs/core/TESTING_GUIDE.md` section 8.6, the honest characterization is that this case is
**marginal/flaky, straddling the 180s budget** rather than a confirmed slow-solver defect.
Resolving which it actually is would require repeat sampling (5-10 isolated runs), which remains
out of scope for this task and is recorded here for whichever task next touches oracle solve
budgets.

## Two-Pass Invocation for Downstream Use

```bash
nix develop --command bash oracle/run-oracle-suite.sh
```

Or manually:

```bash
pytest oracle/ -n 6 -m "not xdist_serial" -q   # pass 1: bulk, parallel
pytest oracle/ -m "xdist_serial" -q             # pass 2: 7 contention-sensitive tests, serial
```

The script's overall exit code will remain non-zero as long as
`test_complexity_5_scan_self_consistent` stays in the tree — this is expected and is not a defect
in this task's work; a downstream baseline task should treat this failure as pre-existing and
out of scope, exactly as this task did.

## Files Modified

- `oracle/conftest.py` — new: mark registration (`differential`, `slow`, `xdist_serial`) plus
  `pytest_collection_modifyitems` per-parametrize-case marking.
- `oracle/bimodal_logic/tests/test_soundness_regression.py` — one class-level and one
  method-level `@pytest.mark.xdist_serial` decorator, with explanatory comments.
- `oracle/run-oracle-suite.sh` — new executable: the two-pass invocation.
- `oracle/bimodal_logic/README.md` — new "Running the Test Suite" section (lines ~73-100).
- `specs/132_make_oracle_suite_xdist_safe/run/serial-pass.log`,
  `specs/132_make_oracle_suite_xdist_safe/run/parallel-pass.log` — validation logs.

## Residual Risk (Recorded, Not Acted On)

Per the plan's Non-Goals, a full margin audit of all 43 active examples in
`code/src/model_checker/theory_lib/bimodal/examples.py` was out of scope. `BM_CM_1`
(`max_time=15`) is one of several examples in the 5-15s `max_time` band; other examples in that
band could still surface as new, unmarked xdist artifacts in a future `-n 6` run even after this
fix. A future oracle-suite triage should treat this as a known pattern rather than re-diagnosing
it from scratch.

## Plan Deviations

- None (implementation followed plan). The one correction recorded above (the `all_future`
  characterization) is a factual update to an assumption carried into the plan from the research
  report, discovered during Phase 4's own measurement — not a deviation from what the plan
  directed the implementation to do.

## Testing & Validation

All plan verification commands passed:
- Zero `PytestUnknownMarkWarning` on collection.
- `-m xdist_serial` selects exactly 7 items; `-m "not xdist_serial"` selects exactly 543; sum is
  550.
- `test_temporal_depth_identical[some_past]` confirmed NOT marked.
- `oracle/run-oracle-suite.sh` executable, guards verified, both passes run independently of each
  other's exit status.
- No task-number citations in `oracle/conftest.py`, `oracle/run-oracle-suite.sh`, or the new
  README section.
- Serial pass: 7 passed. Parallel pass: 1 failed (known, out of scope), 533 passed, 9 xfailed.
