# bimodal_logic — Standalone Z3 Oracle Package

`bimodal_logic` is a standalone Z3-based cross-oracle harness for the ModelChecker's bimodal
(temporal + modal) logic theory. It provides an independent countermodel/theorem checker used to
differentially validate the in-package `model_checker.theory_lib.bimodal` semantics against a
second, separately-implemented Z3 encoding.

As of task 118 (branch `task-117-restore-model-checker`), this package lives at the top-level
`oracle/bimodal_logic/` directory, outside the shipped `model_checker` package (previously at
`code/src/bimodal_logic/`). This keeps the oracle/harness code out of the PyPI-distributed wheel
while still being available for local differential testing.

## Layout

```
oracle/bimodal_logic/
├── __init__.py          # Public API: Z3OracleProvider, translation helpers
├── cli.py                # `bimodal-logic check` CLI entry point
├── provider.py            # Z3OracleProvider — the oracle's find_countermodel() implementation
├── serialization.py       # Z3 model -> JSON countermodel serialization
├── translation.py         # Formula JSON <-> prefix/infix, fold/unfold, temporal_depth
├── tests/                 # Oracle's own test suite (see "Running Tests" below)
└── README.md              # This file
```

## Not Fully Self-Contained: Depends on `model_checker`

Unlike a typical standalone package, `bimodal_logic` is **not** independent of `model_checker`.
Its purpose is cross-oracle differential testing, so parts of it must construct and inspect the
in-package bimodal semantics objects to compare against:

- `provider.py` imports `model_checker.utils.context.isolated_z3_context`,
  `model_checker.ModelConstraints`, `model_checker.Syntax`, and symbols from
  `model_checker.theory_lib.bimodal`.
- `serialization.py` imports `model_checker.solver.is_true`.
- `__init__.py` eagerly imports `provider` (which imports `serialization`), so **merely importing
  `bimodal_logic` requires `model_checker` to be importable** — this is not limited to the
  differential test files.

`cli.py` is the one exception that defers its `provider` import to inside `main()`, but any test
or script that does `import bimodal_logic` or `from bimodal_logic import <anything>` transitively
needs `model_checker` on `sys.path` as well.

## Standalone Development Setup

There is no `oracle/bimodal_logic/pyproject.toml` (yet) — the package's build/project metadata
(`name = "bimodal-logic"`, the `bimodal-logic` console script, and the
`bimodal_harness.oracle_providers` entry point registering `z3_base =
"bimodal_logic.provider:Z3OracleProvider"`) currently still lives in `code/pyproject.toml`, left
in place pending the package-identity work that reconciles `pyproject.toml`/`MANIFEST.in`
include/exclude rules (out of scope for this task; see the parent restore plan's package-identity
phase). Until that lands, treat this directory as a `PYTHONPATH`-based package:

```bash
# Both entries are required — bimodal_logic itself, and the model_checker it cross-checks against.
export PYTHONPATH=oracle:code/src

# Run the oracle's own test suite:
pytest oracle/bimodal_logic/tests -v

# Collect-only (no execution):
pytest oracle/bimodal_logic/tests --collect-only -q

# Use the CLI directly (once model_checker is importable):
python -m bimodal_logic.cli check '{"tag": "atom", "name": "p"}'
```

`PYTHONPATH=oracle` alone is **not** sufficient — `pytest oracle/bimodal_logic/tests
--collect-only -q` with only `oracle` on the path fails at collection with
`ModuleNotFoundError: No module named 'model_checker'` (verified during task 118 Phase 6),
because of the `__init__.py` import chain described above.

## Relationship to the In-Package Bimodal Suite

`code/src/model_checker/theory_lib/bimodal/tests/` contains the in-package bimodal test suite,
which as of task 118 has zero references to `bimodal_logic` (`grep -rl bimodal_logic
code/src/model_checker/` returns nothing) and collects/runs with only `PYTHONPATH=code/src`. The
7 test files that exercised the external oracle directly (cross-oracle differential, soundness
regression, boundary regression, oracle provider/interface, JSON translation, fold/unfold) moved
here, to `oracle/bimodal_logic/tests/`, alongside one split-out test
(`test_frame_class_declaration.py`) extracted from the in-package
`test_frame_class_mapping.py`'s single oracle-dependent test method.
