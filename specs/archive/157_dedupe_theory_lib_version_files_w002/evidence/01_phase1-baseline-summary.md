# Phase 1 Baseline Evidence

## Fresh build (before any source change)

```
cd code
rm -rf dist build src/model_checker.egg-info
python3 -m build --no-isolation --outdir dist
```

Result: `Successfully built model_checker-1.3.0.tar.gz and model_checker-1.3.0-py3-none-any.whl`

## check-wheel-contents baseline (no --ignore)

```
$ check-wheel-contents dist/*.whl
dist/model_checker-1.3.0-py3-none-any.whl: W002: Wheel contains duplicate files:
  model_checker/theory_lib/bimodal/VERSION
  model_checker/theory_lib/exclusion/VERSION
  model_checker/theory_lib/imposition/VERSION
  model_checker/theory_lib/logos/VERSION
exit_code=1
```

Full raw output: `01_baseline-check-wheel-contents.txt` (this directory).

## Packaging contract suite baseline (before any source change)

```
PYTHONPATH=code/src pytest code/tests/packaging/ -v
```

Result: `114 passed, 4 skipped in 106.59s`. The 4 skips are
`test_notebooks_present_where_on_disk[wheel-bimodal]`, `[wheel-logos]`, `[sdist-bimodal]`,
`[sdist-logos]` — pre-existing, notebook-conditional, unrelated to this task.

## file_scope widening confirmed

`jq '.active_projects[]|select(.project_number==157).file_scope|length' specs/state.json` returns
`11` (4 declared + 4 widened + `code/tests/packaging/` + `code/pyproject.toml` + `code/MANIFEST.in`).
No prior entry was dropped (widening had already landed in `specs/state.json` prior to this
dispatch; confirmed by inspection — all 4 VERSION files, `theory_lib/__init__.py`,
`THEORY_ARCHITECTURE.md`, `test_theory_conformance.py`, `builder/project.py`,
`code/tests/packaging/`, `code/pyproject.toml`, `code/MANIFEST.in` are present).
