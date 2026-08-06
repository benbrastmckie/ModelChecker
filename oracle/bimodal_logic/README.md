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

## Running the Test Suite

The suite has two entry points: a fast **gating** runner (deselects the exhaustive
complexity<=5 self-consistency scan) for routine use, and a separate, explicitly-invoked
**exhaustive** runner for the full sweep. See `code/docs/core/TESTING_GUIDE.md` section 8.8
("Oracle Suite: Gating vs. Exhaustive Split") for the full rationale; this section covers the
day-to-day commands.

### Gating (routine use)

Run the full `oracle/` suite with the two-pass gating runner rather than a single
`pytest oracle/ -n 6` invocation:

```bash
nix develop --command bash oracle/run-oracle-suite.sh
```

Both passes deselect the `slow` marker (the exhaustive scan and its temporal-only BH-comparison
sibling), so this runs in roughly 15-20 minutes rather than the ~77 minutes a full sweep costs.
`oracle/` has no reachable pytest ini file (see `oracle/conftest.py`'s module docstring), so the
deselect has to be spelled out on every invocation — there is no ambient default to inherit.

The suite is further split into two passes because a handful of tests have a Z3 solve budget with
under ~2x headroom over their typical solo wall-clock time, and CPU contention from running six
pytest workers in parallel can inflate solve times enough to trip that budget — reported as
"no countermodel" rather than as an error (see `code/docs/core/TESTING_GUIDE.md` section 8.6). The
script runs `pytest oracle/ -n 6 -m "not xdist_serial and not slow"` first, then a serial
`pytest oracle/ -m "xdist_serial and not slow"` pass with no `-n` at all. Both passes are wrapped
in `timeout --kill-after=60s BUDGET` (override via `ORACLE_PASS1_TIMEOUT` / `ORACLE_PASS2_TIMEOUT`);
a pass that exceeds its budget is reported as `TIMED OUT (exit 124)`, distinct from
`FAILED (exit N)`. Extra arguments (e.g. `-q`, `--collect-only`) are forwarded to both passes.

Marks are registered in `oracle/conftest.py`, which is also where `differential` and `slow` are
registered for `oracle/`-rooted invocations (they are already declared in `code/pyproject.toml`,
but that file sits outside pytest's ini-discovery path when `oracle/` is invoked from the repo
root).

When adding a new test whose Z3 solve budget has under ~2x headroom over its typical solo
wall-clock time, mark it `@pytest.mark.xdist_serial` (or, for a single case inside a shared
`parametrize` list, add its node-id fragment to `oracle/conftest.py`'s
`pytest_collection_modifyitems` hook) so it runs in the serial pass instead of risking a
contention-induced spurious failure under `-n 6`.

### Exhaustive (explicit, on demand)

Run the full complexity<=5 self-consistency sweep (274 formulas x 2 solves, ~60-90 minutes) with:

```bash
nix develop --command bash oracle/run-oracle-exhaustive-scan.sh
```

This is typically used to re-derive the known-conclusive baseline manifest
(`oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json`) after a change to the
formula enumerator or the solve budget — never as part of routine gating. For a bounded/ad-hoc run
instead (e.g. a quick smoke check), use the standalone CLI directly:

```bash
python oracle/scan_runner.py --max-complexity 3 --limit 5 --out-dir /tmp/my-scan
```

**Observing a long run.** Both entry points write into a per-run output directory: `progress.jsonl`
gets one flushed JSON record appended per formula (so `tail -f progress.jsonl` shows the run live),
and the same run also prints heartbeat/loud lines to stdout (pass `-s` to pytest, or rely on
`scan_runner.py`'s default stdout streaming) for every formula that disagrees, times out, or takes
more than 5 seconds, plus a periodic heartbeat.

**Detecting completion.** A `SCAN_COMPLETE` marker is written into the output directory strictly
after `report.json` is written and closed (atomically, via write-to-temp-then-rename). The
marker's existence — never whether the pytest/scan_runner.py process is still running — is the
only sanctioned signal that a run finished. `run-oracle-exhaustive-scan.sh`'s summary checks for
this marker explicitly and reports "scan did not reach completion" if it is absent, even if the
process itself exited.

## Relationship to the In-Package Bimodal Suite

`code/src/model_checker/theory_lib/bimodal/tests/` contains the in-package bimodal test suite,
which as of task 118 has zero references to `bimodal_logic` (`grep -rl bimodal_logic
code/src/model_checker/` returns nothing) and collects/runs with only `PYTHONPATH=code/src`. The
7 test files that exercised the external oracle directly (cross-oracle differential, soundness
regression, boundary regression, oracle provider/interface, JSON translation, fold/unfold) moved
here, to `oracle/bimodal_logic/tests/`, alongside one split-out test
(`test_frame_class_declaration.py`) extracted from the in-package
`test_frame_class_mapping.py`'s single oracle-dependent test method.
