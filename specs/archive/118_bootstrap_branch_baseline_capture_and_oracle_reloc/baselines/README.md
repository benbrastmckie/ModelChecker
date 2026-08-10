# Phase 2 Baseline: Pre-Change State (task 118)

Captured on branch `task-117-restore-model-checker`, before any oracle relocation or restore
work (Phase 4+). This is the "before" snapshot New Task 5 (root-causing the differential test
failures) and other downstream tasks compare against.

## Commands Run and Outputs

### 1. Live bimodal suite (pass/fail + timing)

Command:
```bash
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests -q
```

The full suite (818 tests) was run in two segments due to wall-clock length (~70 minutes
combined). Segment boundaries were chosen for operational convenience only; both segments
together constitute one full run of the suite in its current (pre-relocation) state:

- `bimodal-suite-segment1.txt` — first segment: **5 failed, 534 passed in 2875.30s (0:47:55)**,
  `EXIT_CODE=1`.
- `bimodal-suite-remainder.txt` — remaining tests: **279 passed in 1325.56s (0:22:05)**,
  `EXIT_CODE=0`.

**Combined baseline total: 818 tests collected, 813 passed, 5 failed, ~4200.86s (~70 minutes)
wall-clock.**

The 5 failures are all in
`code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py`:
- `TestKnownFormulaBaseline::test_known_invalid_return_countermodel`
- `TestBimodalHarnessIntegration::test_temporal_only_agreement_complexity_3`
- `TestBimodalHarnessIntegration::test_temporal_only_agreement_complexity_5`
- `TestMockOracleSpotCheck::test_spot_check_all`
- `TestCIGate::test_oracle_baseline_agreement`

These are pre-existing cross-oracle differential assertion failures (the in-package bimodal
semantics vs. the external `bimodal_logic` oracle disagree on specific formulas/complexity
classes). They are **expected and pre-existing** — not introduced by this task. Root-causing
them is explicitly a non-goal of this task (New Task 5's responsibility per the plan).

Two earlier, superseded attempts at capturing this baseline (`bimodal-suite.txt`, a two-chunk
run, and `bimodal-suite-full.txt`, a single full-suite run) were aborted mid-run by the session
limit and have been deleted; `bimodal-suite-segment1.txt` + `bimodal-suite-remainder.txt` are the
authoritative, complete baseline captures superseding them.

### 2. Collect-only snapshot (canonical test tree)

Command:
```bash
PYTHONPATH=code/src pytest code/tests/ --collect-only -q
```

Output: `collect-only-before.txt`. Result: **269 tests collected, 2 errors** during collection —
both are pre-existing `ModuleNotFoundError` failures unrelated to this task:
- `code/tests/e2e/test_simple_output_verify.py`: `ModuleNotFoundError: No module named
  'model_checker.output.manager'`
- `code/tests/integration/test_model_building_sync.py`: `ModuleNotFoundError: No module named
  'model_checker.builder'`

These reflect the pre-restoration state of the package (the `builder/` and `output/manager.py`
modules have not yet been restored — that is New Task 2/New Task 3's responsibility per the
parent plan) and are recorded here only as a before-state reference, not something this task
fixes.

### 3. `--help` snapshot

Command:
```bash
PYTHONPATH=code/src python -m model_checker --help
```

Output: `help-before.txt`. Result: **fails** with `ModuleNotFoundError: No module named
'model_checker.builder'` (`EXIT=1`) — same pre-existing missing-module condition as above.

## Files in This Directory

| File | Description |
|------|--------------|
| `bimodal-suite-segment1.txt` | First segment of the live bimodal suite run: 5 failed, 534 passed, 2875.30s |
| `bimodal-suite-remainder.txt` | Remaining segment of the live bimodal suite run: 279 passed, 1325.56s |
| `collect-only-before.txt` | `pytest code/tests/ --collect-only -q` snapshot: 269 collected, 2 errors |
| `help-before.txt` | `python -m model_checker --help` snapshot: fails, `ModuleNotFoundError` |
| `restore-inventory.md` | Phase 3 restore-point SHA -> path confirmation table |
| `README.md` | This file |

## Before/After Comparison Guidance (for New Task 5 and later)

After the parent plan's later restoration phases land, re-run the same three commands above and
diff against these files:
- The `--help` and `--collect-only` errors should disappear once `builder/`, `output/manager.py`,
  and related modules are restored.
- The 5 `test_cross_oracle_differential.py` failures should be evaluated independently — a
  regression is any *new* failure beyond this set of 5; a fix is any of these 5 flipping to pass.
