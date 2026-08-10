# Implementation Summary: Restore Package Identity and Repair Test Infrastructure

- **Task**: 121 - restore_package_identity_and_repair_test_infrastru
- **Plan**: plans/01_restore-package-identity-test-infra.md
- **Status**: COMPLETED (all 4 phases)
- **Branch**: task-117-restore-model-checker

## Overview

Restored the `model-checker` package identity in `code/pyproject.toml` (replacing the transient
`bimodal-logic` oracle identity from task 104), reconciled `MANIFEST.in`/packaging config/version
single-sourcing, widened `testpaths` and repaired every live test-collection error, and added
`pytest-xdist` as a declared dev dependency with `-n auto` usage documented.

## Phase-by-Phase Results

### Phase 1: Restore

Rewrote `[project]` in `code/pyproject.toml`:
- `name = "model-checker"`, `version = "1.3.0"` (commented as provisional; release task confirms
  final number).
- `description`/`keywords`/`classifiers` restored to the framework identity (semantics, Z3, SMT,
  modal logic, model checking, hyperintensionality), dropping bimodal-oracle-specific wording.
- `dependencies = ["z3-solver>=4.8.0", "networkx>=2.0"]` — confirmed `networkx` is imported
  unconditionally at module scope in `iterate/graph.py`, so it stays a hard dependency (not moved
  to an extra).
- Added `[project.optional-dependencies]` `jupyter` and `all` extras
  (`ipywidgets`, `matplotlib`, `networkx`, `jupyter`, `ipython`).
- `[project.scripts]` now has exactly one entry, `model-checker = "model_checker.__main__:run"`;
  removed the `bimodal-logic` script and the entire
  `[project.entry-points."bimodal_harness.oracle_providers"]` table.

### Phase 2: Reconcile Packaging Config, MANIFEST.in, and Version Single-Sourcing

All checks passed with **no source edits required**:
- `grep -rn bimodal_logic code/src/` returns nothing — no stray oracle references remain under
  `code/src`.
- `[tool.setuptools.package-data]` globs (`README.md`, `*.md`, `*.ipynb`) already cover the
  restored jupyter notebooks and theory READMEs.
- Every `MANIFEST.in` path resolves to an existing file (verified with a per-line existence
  check against `code/`).
- `get_model_checker_version()` in `model_checker/utils/version.py` already queries
  `version('model-checker')`, matching the `[project] name` set in Phase 1 — version
  single-sourcing is correct as-is; `model_checker/__init__.py` needed no change.
- Verified via a `python -m build --sdist --no-isolation code/` build (isolated build fails only
  because this sandbox has no network access to fetch `setuptools`/`wheel`, unrelated to the
  packaging config itself): the resulting `model_checker-1.3.0.tar.gz` contains
  `model_checker/jupyter/` and all four theory READMEs, and contains no `bimodal_logic` content.

### Phase 3: Repair Test Collection

Set `[tool.pytest.ini_options] testpaths = ["tests", "src/model_checker"]` (all other pytest
options — `pythonpath`, `python_files`, `markers`, `filterwarnings` — left untouched).

Live `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker --collect-only -q` confirmed
the plan's hypothesized 3 errors exactly, then repair work surfaced additional errors on
subsequent collection passes (documented below):

1. **`code/tests/e2e/test_simple_output_verify.py` — DELETED.** Imported
   `model_checker.output.collectors.ModelDataCollector`, which does not exist. Grepped the whole
   `output/` package: no `collectors` submodule, no `ModelDataCollector` class, and no
   `data_collector` attribute on `OutputManager` anywhere. The batch data-extraction capability
   this test exercised is genuinely gone with no restored equivalent — deleted rather than
   repaired.

2. **`code/src/model_checker/builder/tests/integration/test_interactive.py` — DELETED.** Imported
   `SequentialSaveManager` from `model_checker.output`, which is not exported (or defined
   anywhere in the source tree — only mentioned in stale `output/README.md` prose).
   `ConsoleInputProvider` is likewise absent. The interactive/sequential-save user-prompt flow
   these tests exercised is genuinely gone — deleted rather than repaired.
   **Flagged for downstream attention (not fixed, out of this task's collection-only scope and
   outside `file_scope`):** `code/src/model_checker/builder/module.py`'s
   `_initialize_output_management()` still contains a function-local (deferred) import of these
   same missing names (`SequentialSaveManager`, `ConsoleInputProvider`, `create_output_config` is
   present but the other two are not) — this is a pre-existing *runtime* bug that will raise
   `ImportError` whenever a `BuildModule` reaches that code path (i.e. when `config.sequential` is
   true). It does not cause a collection error (the import is deferred inside a method, not at
   module scope), so it is out of this task's non-goals-bounded scope; recorded here for the
   downstream green-gate task.

3. **`code/src/model_checker/theory_lib/tests/unit/test_error_handling.py` — REPAIRED
   (partial delete).** The plan flagged one broken import (`WitnessSemanticError`); fixed to
   `WitnessError` (exists in `theory_lib/errors.py`). Re-collecting after that fix surfaced **four
   further genuinely-absent names** in the same import block that the original research grounding
   had not caught: `ImpositionSemanticError`, `ImpositionOperationError`, `ImpositionHelperError`,
   `LogosSubtheoryError`, `LogosProtocolError`. Confirmed via grep across `theory_lib/errors.py`
   and the imposition/logos packages (which only ever import the generic `SemanticError` base
   from `theory_lib.errors`; logos does not import from `theory_lib.errors` at all) that none of
   these five classes exist anywhere, and no generic base has a matching constructor signature
   for the specific ones (`ImpositionHelperError(function_name)`,
   `LogosSubtheoryError(msg, subtheory_name=...)`). Repair decisions:
   - `TestWitnessErrorHandling`: `WitnessSemanticError` → `WitnessError`, passing `theory="exclusion"`
     explicitly since (unlike the test's original assumption) none of `WitnessError`/
     `WitnessRegistryError`/`WitnessConstraintError` auto-populate `theory` in their constructors
     — this is a pre-existing content mismatch between test expectations and actual class
     behavior, left as-is per the collection-only, not-runtime-correctness, scope of this task.
   - `TestImpositionErrorHandling`: rewritten to exercise the real `SemanticError` base
     (`SemanticError("...", theory="imposition")`) instead of the fictional
     `ImpositionSemanticError`/`ImpositionOperationError`/`ImpositionHelperError` classes.
   - `TestLogosErrorHandling`: deleted outright — no `Logos*` classes or equivalent constructor
     shape exist to repair against.
   - `test_error_chaining_preserves_context`: `ImpositionSemanticError(...)` →
     `SemanticError(..., theory="imposition")`.

Re-verified the parent plan's originally-flagged files (`tests/integration/test_model_building_sync.py`,
`tests/integration/test_system_imports.py`, `tests/utils/helpers.py`) collect cleanly under the
widened `testpaths` with no changes needed.

**Result**: `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker --collect-only -q`
reports **2095 tests collected, 0 errors** (up from 2083 collected / 3 errors at the start of
Phase 3 — the increase reflects the widened `testpaths` picking up additional in-package test
trees, net of the two deleted files).

### Phase 4: Add pytest-xdist and Final Verification

- Added `[project.optional-dependencies] dev = ["pytest-xdist>=3.0.0"]`.
- Documented `-n auto` parallel-run usage in a new "Parallel Test Execution (`pytest-xdist`)"
  section of `code/tests/README.md`; also removed two now-dangling references to the deleted
  `test_simple_output_verify.py` from that same README's directory listing and key-files section.
- Final verification re-run: `code/tests/` alone collects 273 tests / 0 errors; the widened
  `code/tests/ code/src/model_checker` scope collects 2095 tests / 0 errors.
- `PYTHONPATH=code/src python -m model_checker --help` exits 0; confirmed
  `model_checker.theory_lib.AVAILABLE_THEORIES == ['bimodal', 'logos', 'exclusion', 'imposition']`.

## Deviations from Plan

- **Sandbox has no network access for isolated builds.** `python -m build --sdist code/` (default,
  isolated) fails with a pip-install error unrelated to this task's packaging changes (the sandbox
  cannot reach PyPI to bootstrap the build environment). Used `--no-isolation` instead (setuptools/
  wheel/build already present in the ambient environment) to verify sdist contents; this is an
  environment limitation, not a packaging defect — noted for whoever runs the release task in an
  environment with network access.
- **`pytest-xdist` could not be installed to execute `-n auto` live** in this network-isolated
  sandbox (`pip install pytest-xdist` fails: no network, and the sandbox blocks user-site installs
  into this virtualenv). Verified via the plan's own stated alternative: the dependency is
  correctly declared in `[project.optional-dependencies] dev`, matching the "declared" branch of
  the plan's verification criterion (`python -c "import xdist" (after install) **or** presence of
  pytest-xdist in the declared dev extra`).
- **Phase 3 test-collection repair uncovered more broken imports than the plan's research
  grounding identified.** The plan's live-collection-error list (3 files) was accurate as far as
  it went, but fixing the first named symbol in `test_error_handling.py`
  (`WitnessSemanticError` → `WitnessError`) surfaced four further genuinely-absent names in the
  same import statement on the next collection pass. These were resolved using the same
  repair-vs-delete decision rule the plan specified (prefer repair against a restored capability
  under a new name; delete when the symbol is genuinely absent) — documented per-file above and in
  the plan's Phase 3 checklist annotations.
- **`builder/module.py`'s pre-existing runtime `ImportError`** (deferred import of
  `SequentialSaveManager`/`ConsoleInputProvider`, which do not exist) was identified during the
  test_interactive.py delete decision but intentionally **not fixed** — it is a runtime failure,
  not a collection error, and `builder/module.py` is outside this task's `file_scope`
  (`code/pyproject.toml; code/MANIFEST.in; code/src/model_checker/__init__.py; code/tests`) and
  outside the plan's Non-Goals boundary ("Do not fix runtime test failures beyond what is needed
  for zero collection errors"). Flagged in the plan's Phase 3 annotation and here for the
  downstream green-gate task.
- No other deviations; all four phases followed the plan's task lists directly.

## Files Modified

- `code/pyproject.toml` — `[project]` identity/deps/extras/scripts rewrite (Phase 1); `testpaths`
  widened (Phase 3); `dev` extra with `pytest-xdist` added (Phase 4).
- `code/tests/README.md` — `-n auto` documentation added; two dangling references to a deleted
  test file removed (Phase 4).
- `code/src/model_checker/theory_lib/tests/unit/test_error_handling.py` — repaired imports and
  rewrote three affected test classes (Phase 3).
- `code/tests/e2e/test_simple_output_verify.py` — deleted (Phase 3).
- `code/src/model_checker/builder/tests/integration/test_interactive.py` — deleted (Phase 3).
- `code/src/model_checker/__init__.py` — inspected only, no change needed (Phase 2).
- `code/MANIFEST.in` — inspected only, no change needed (Phase 2).

## Verification Summary

| Check | Result |
|-------|--------|
| `[project] name`/`version` | `model-checker` / `1.3.0` |
| `grep -n bimodal` under `[project]`/scripts/entry-points | clean (only legitimate `testpaths` bimodal-theory reference remains) |
| `[project.scripts]` entry count | 1 (`model-checker`) |
| `MANIFEST.in` paths resolve | all resolve |
| `--no-isolation` sdist build | succeeds; contains jupyter/ + 4 theory READMEs; no bimodal_logic content |
| `pytest --collect-only` (`code/tests/` only) | 273 tests, 0 errors |
| `pytest --collect-only` (widened `testpaths`) | 2095 tests, 0 errors |
| `pytest-xdist` declared | yes, `dev` extra |
| `python -m model_checker --help` | exit 0 |

## Next Steps

- Downstream green-gate task should address the `builder/module.py`
  `_initialize_output_management()` runtime `ImportError` flagged above (missing
  `SequentialSaveManager`/`ConsoleInputProvider`).
- Downstream release task (parent 117) confirms the final published version number (currently
  `1.3.0` here as a provisional restoration value).
- An editable reinstall (`pip install -e code/`) may be needed in a real (networked) environment
  for `__version__` to reflect the restored `model-checker` distribution identity at runtime.
