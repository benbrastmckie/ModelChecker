# Phase 6 Evidence — Full Packaging Contract Suite + Generate-Then-Execute

## Full suite run

```
PYTHONPATH=code/src pytest code/tests/packaging/ -v
```

Result: `106 passed, 4 skipped in 103.82s` (0 failures, 0 errors, 0 deselections). The 4 skips are
the pre-existing, notebook-conditional `test_notebooks_present_where_on_disk` cases
(`[wheel-bimodal]`, `[wheel-logos]`, `[sdist-bimodal]`, `[sdist-logos]`) — unrelated to this task.

All of `test_inclusions.py`, `test_exclusions.py`, `test_parity.py`, `test_build_smoke.py`,
`test_entry_point.py`, `test_cli_console_script.py`, and `test_generate_then_execute.py` ran.

## Test count reconciliation

| Stage | Passed | Skipped |
|---|---|---|
| Phase 1 baseline (VERSION present, contracts not yet relaxed) | 114 | 4 |
| Phase 6 (VERSION removed, contracts relaxed) | 106 | 4 |

Drop: 8 passed tests, matching Phase 3's expected 4 theories x 2 artifacts = 8
`REQUIRED_ROOT_FILES`/`test_root_metadata_file_present` `VERSION` parametrizations removed from
`test_inclusions.py`. No other test count changed.

## test_generate_then_execute.py — every registered theory

```
test_generate_then_execute.py::test_registry_is_non_empty PASSED
test_generate_then_execute.py::test_generate_then_execute[bimodal] PASSED
test_generate_then_execute.py::test_generate_then_execute[logos] PASSED
test_generate_then_execute.py::test_generate_then_execute[exclusion] PASSED
test_generate_then_execute.py::test_generate_then_execute[imposition] PASSED
test_generate_then_execute.py::test_parametrization_count_matches_live_registry PASSED
```

This is the end-to-end scaffolding check: it installs the wheel into a real venv, generates a
project via the `model-checker` console script, and executes it — for all four registered
theories.

## Independent unpacked-wheel spot-check

Unpacked the freshly built `code/dist/model_checker-1.3.0-py3-none-any.whl` to a temp dir via
`python3 -m zipfile -e`, then with `PYTHONPATH` pointed at the unpacked tree:

```python
from model_checker.builder.project import BuildProject
bp = BuildProject('logos')
bp.source_dir  # -> <unpack_dir>/model_checker/theory_lib/logos
bp.generate('demo')  # -> <temp>/project_demo, succeeded
```

Generation succeeded (no `FileNotFoundError`, confirming the risk-closure experiment's finding
that this path reads from the installed package holds under remedy (a): `VERSION` is now
`OPTIONAL_COPY_ITEMS`, so its absence from the unpacked wheel is tolerated).

`find <temp>/project_demo -name VERSION` returned no matches — the generated project contains no
`VERSION` file, confirmed.

Both the temp unpack directory and the temp generation directory were removed after the check.

## No skips or deselections used to force the suite green

Confirmed via `grep -iE "FAILED|ERROR|deselect"` over the full `-v` log: zero matches.
