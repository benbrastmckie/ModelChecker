# Pre-Fix Baseline Summary

Captured before any Phase 3 production edit lands, per the plan's "baseline before behavior
change" decision.

## Four-theory directory gate

Command:
```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ code/src/model_checker/theory_lib/exclusion/ code/src/model_checker/theory_lib/imposition/ code/src/model_checker/theory_lib/bimodal/ -q
```

Result: `1 failed, 1694 passed in 280.42s`

Already-failing test (pre-existing, not caused by this task):
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py::TestLiveIteration::test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`

Full output: `baselines/01_pre-fix-theory-suites.txt`

## Shared-engine iterate suite

Command:
```
PYTHONPATH=code/src pytest code/src/model_checker/iterate/ -q
```

Result: `238 passed in 1.26s` — no failures.

Full output: `baselines/01_pre-fix-iterate.txt`

## Representative iterate > 1 example captures (per affected theory)

See `baselines/01_pre-fix-logos-iteration.txt`, `baselines/01_pre-fix-exclusion-iteration.txt`,
`baselines/01_pre-fix-imposition-iteration.txt` for the printed model 2+ output on each theory's
representative example, captured via `./dev_cli.py`. These are the diffs Phase 6 reviews against
the post-fix behavior.
