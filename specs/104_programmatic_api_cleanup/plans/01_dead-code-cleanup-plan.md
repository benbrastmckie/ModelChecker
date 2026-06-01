# Implementation Plan: Task #104 - Dead-Code Cleanup and Thin CLI

- **Task**: 104 - Dead-code cleanup and thin CLI
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: 103 (OracleProvider - completed)
- **Research Inputs**: specs/104_programmatic_api_cleanup/reports/01_dead-code-cleanup.md
- **Artifacts**: plans/01_dead-code-cleanup-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Remove dead code from the ModelChecker codebase now that OracleProvider is the primary public interface. The builder/ directory (22 files), most of output/ (11 files), and several standalone dead files are CLI-only components unreachable from the oracle pipeline. After removal, simplify `model_checker/__init__.py` and `output/__init__.py` to export only oracle-relevant symbols, then add a thin `bimodal-logic check` CLI entry point backed by Z3OracleProvider. Each phase runs the full test suite to catch regressions.

### Research Integration

The research report (01_dead-code-cleanup.md) provides:
- Complete file-by-file inventory classifying every file in builder/ and output/ as CLI-only or oracle-needed
- Oracle pipeline import chain showing which modules are transitively required
- Confirmation that builder/ is imported via `model_checker/__init__.py` but never used by the oracle
- Thin CLI design with argparse subcommand pattern and pyproject.toml entry point
- Risk assessment: all builder/ removals are LOW risk; `__init__.py` changes are MEDIUM risk
- Three formatter test files to keep (test_markdown_formatter, test_json_serialization, test_color_formatting)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Remove all CLI-only dead code (builder/, dead output/ components, cli.py debug artifact, profile_abundance.py)
- Simplify `model_checker/__init__.py` to remove builder and `__main__` imports
- Simplify `output/__init__.py` to export only formatters
- Add `bimodal-logic check` CLI entry point to pyproject.toml
- Maintain all existing bimodal test suite passing (627+ tests)

**Non-Goals**:
- Removing `__main__.py` entirely (the `model-checker` CLI entry point stays)
- Removing `settings/settings.py` (explicitly kept per task description)
- Removing `output/formatters/` (explicitly kept per task description)
- Removing `theory_lib/bimodal/tests/`, `theory_lib/bimodal/examples.py`, or `theory_lib/bimodal/operators.py`
- Removing `extract_model_elements()`, `extract_states()`, or `print_*` methods
- Modifying the oracle pipeline internals (provider.py, serialization.py, translation.py)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing builder/ breaks `model-checker` CLI entry point | M | L | `__main__.py` imports builder directly; it still works because `__main__.py` remains and imports builder at call time. But builder/ is deleted, so `model-checker` CLI will break. Accept this as intentional -- task says "remove unused builder components" |
| `__init__.py` cleanup breaks external callers using `from model_checker import BuildModule` | M | L | No external packages import BuildModule; only internal tests do. Verify with grep before removing. |
| Removing output/ components breaks formatter tests | H | L | Keep formatter tests explicitly; remove only tests for deleted components |
| Test collection errors from removed files | M | M | Update pyproject.toml testpaths if needed; remove conftest.py in deleted test directories |
| Thin CLI has import error at runtime | M | L | Write test for CLI invocation before shipping |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Remove builder/ directory and fix __init__.py [COMPLETED]

**Goal**: Delete the entire builder/ directory (22 files + tests) and remove builder/`__main__` imports from `model_checker/__init__.py`. This is the highest-impact, lowest-risk removal.

**Tasks**:
- [ ] Record pre-removal test baseline: run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q --tb=no` and note pass count
- [ ] Delete `code/src/model_checker/builder/` directory entirely (22 source files + 32 test files + README)
- [ ] Edit `code/src/model_checker/__init__.py`:
  - Remove `from .builder import (BuildModule, BuildProject)`
  - Remove `from .builder.example import BuildExample`
  - Remove `from .__main__ import (ParseFileFlags, main)`
  - Remove `BuildModule`, `BuildProject`, `BuildExample`, `ParseFileFlags`, `main` from `__all__`
  - Update module docstring to remove "Jupyter notebook integration" reference
- [ ] Run full bimodal test suite to verify no regressions

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/builder/` - DELETE entire directory
- `code/src/model_checker/__init__.py` - Remove builder and __main__ imports

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q --tb=no` passes with same count as baseline
- `PYTHONPATH=code/src python -c "from model_checker import ModelConstraints, Syntax"` succeeds
- `PYTHONPATH=code/src python -c "from model_checker import BuildModule"` raises ImportError (expected)

---

### Phase 2: Remove dead output/ components [NOT STARTED]

**Goal**: Remove CLI-only output components while preserving formatters/ and its tests.

**Tasks**:
- [ ] Delete `code/src/model_checker/output/progress/` directory entirely (4 source files + __init__.py + README)
- [ ] Delete individual files:
  - `code/src/model_checker/output/prompts.py`
  - `code/src/model_checker/output/sequential_manager.py`
  - `code/src/model_checker/output/input_provider.py`
  - `code/src/model_checker/output/manager.py`
  - `code/src/model_checker/output/collectors.py`
  - `code/src/model_checker/output/config.py`
  - `code/src/model_checker/output/constants.py`
  - `code/src/model_checker/output/helpers.py`
  - `code/src/model_checker/output/errors.py`
- [ ] Edit `code/src/model_checker/output/__init__.py` to export only formatters:
  - Keep imports of `MarkdownFormatter`, `JSONFormatter`, `ANSIToMarkdown` from `.formatters`
  - Remove all other imports (OutputManager, ModelDataCollector, OutputConfig, etc.)
  - Update `__all__` to only include formatter exports
- [ ] Delete dead output tests (keep only formatter tests):
  - Delete: `test_progress_animated.py`, `test_progress_core.py`, `test_progress_spinner.py`, `test_progress_display.py`
  - Delete: `test_prompts.py`, `test_prompt_manager.py`, `test_input_provider.py`
  - Delete: `test_output_manager_simple.py`, `test_helpers.py`, `test_errors.py`, `test_config_simple.py`
  - Delete: `test_notebook_formatter.py` (broken import, already dead)
  - Delete: `test_collector_integration.py`, `test_model_data_collection.py`
  - Delete integration tests: `test_output_integration.py`, `test_output_directory.py`, `test_build_integration.py`, `test_markdown_relations.py`
  - Keep: `test_markdown_formatter.py`, `test_json_serialization.py`, `test_color_formatting.py`
- [ ] Run full bimodal test suite to verify no regressions

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/output/progress/` - DELETE entire directory
- `code/src/model_checker/output/prompts.py` - DELETE
- `code/src/model_checker/output/sequential_manager.py` - DELETE
- `code/src/model_checker/output/input_provider.py` - DELETE
- `code/src/model_checker/output/manager.py` - DELETE
- `code/src/model_checker/output/collectors.py` - DELETE
- `code/src/model_checker/output/config.py` - DELETE
- `code/src/model_checker/output/constants.py` - DELETE
- `code/src/model_checker/output/helpers.py` - DELETE
- `code/src/model_checker/output/errors.py` - DELETE
- `code/src/model_checker/output/__init__.py` - Simplify to formatters only
- `code/src/model_checker/output/tests/` - Remove dead test files, keep 3 formatter tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q --tb=no` passes
- `PYTHONPATH=code/src python -c "from model_checker.output.formatters import MarkdownFormatter, JSONFormatter, ANSIToMarkdown"` succeeds
- `PYTHONPATH=code/src python -c "from model_checker.output import MarkdownFormatter"` succeeds
- Kept formatter tests pass: `PYTHONPATH=code/src pytest code/src/model_checker/output/tests/unit/test_markdown_formatter.py code/src/model_checker/output/tests/unit/test_json_serialization.py code/src/model_checker/output/tests/unit/test_color_formatting.py -q --tb=short`

---

### Phase 3: Remove other dead code [NOT STARTED]

**Goal**: Remove remaining dead files: cli.py debug artifact, profile_abundance.py, dead e2e test, and clean up __main__.py.

**Tasks**:
- [ ] Delete `code/src/model_checker/cli.py` (debug artifact with unconditional print() calls)
- [ ] Delete `code/src/model_checker/theory_lib/bimodal/profile_abundance.py` (profiling script, not imported)
- [ ] Delete `code/src/model_checker/theory_lib/bimodal/tests/e2e/test_cli_execution.py` (tests old multi-theory CLI)
- [ ] Edit `code/src/model_checker/__main__.py`:
  - Remove logos-specific `--subtheory` dead-code block (lines referencing `logos` theory)
  - Clean up epilog help text that references non-existent logos theory
  - Note: `__main__.py` will now fail on import because builder/ was deleted in Phase 1. This is expected -- the `model-checker` CLI entry point is now dead code itself. Leave `__main__.py` in place but accept it is only callable if builder is reinstalled.
- [ ] Run full bimodal test suite to verify no regressions

**Timing**: 30 minutes

**Depends on**: 2

**Files to modify**:
- `code/src/model_checker/cli.py` - DELETE
- `code/src/model_checker/theory_lib/bimodal/profile_abundance.py` - DELETE
- `code/src/model_checker/theory_lib/bimodal/tests/e2e/test_cli_execution.py` - DELETE
- `code/src/model_checker/__main__.py` - Clean up dead logos references

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q --tb=no` passes
- `ls code/src/model_checker/cli.py` returns "not found"
- `ls code/src/model_checker/theory_lib/bimodal/profile_abundance.py` returns "not found"

---

### Phase 4: Add thin CLI (bimodal-logic check) [NOT STARTED]

**Goal**: Create a `bimodal-logic` CLI entry point that invokes Z3OracleProvider for standalone countermodel checking, with tests.

**Tasks**:
- [ ] Write test file first (TDD): `code/src/bimodal_logic/tests/test_cli.py`
  - Test CLI module can be imported
  - Test `main()` with valid formula JSON produces JSON output with "result" key
  - Test `main()` with no arguments prints help and exits non-zero
  - Test `main()` with invalid JSON exits with error
  - Test known countermodel formula returns `{"result": "invalid", "countermodel": {...}}`
  - Test known valid formula returns `{"result": "valid", "countermodel": null}`
- [ ] Create `code/src/bimodal_logic/tests/__init__.py` if not exists
- [ ] Create `code/src/bimodal_logic/tests/conftest.py` if needed
- [ ] Create `code/src/bimodal_logic/cli.py`:
  - `argparse` with `check` subcommand
  - `--timeout` (int, default 5000ms)
  - `--frame-class` (string, default "Base")
  - JSON output to stdout: `{"result": "valid"|"invalid", "countermodel": null|dict}`
  - `run()` entry point function
- [ ] Update `code/pyproject.toml`:
  - Add `bimodal-logic = "bimodal_logic.cli:run"` to `[project.scripts]`
- [ ] Update `code/src/bimodal_logic/__init__.py` to export CLI function if appropriate
- [ ] Run new CLI tests and full bimodal test suite

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `code/src/bimodal_logic/cli.py` - CREATE new thin CLI module
- `code/src/bimodal_logic/tests/test_cli.py` - CREATE CLI tests (TDD)
- `code/src/bimodal_logic/tests/__init__.py` - CREATE if not exists
- `code/pyproject.toml` - Add bimodal-logic entry point to [project.scripts]
- `code/src/bimodal_logic/__init__.py` - Optional: export CLI

**Verification**:
- `PYTHONPATH=code/src pytest code/src/bimodal_logic/tests/test_cli.py -v` all tests pass
- `PYTHONPATH=code/src python -m bimodal_logic.cli check '["not", ["atom", "p"]]'` produces valid JSON output
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q --tb=no` still passes

---

### Phase 5: Final validation and cleanup [NOT STARTED]

**Goal**: Run comprehensive test suite, verify no collection errors, update pyproject.toml testpaths if needed, and clean up any remaining issues.

**Tasks**:
- [ ] Run full test suite with verbose output to check for collection errors: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ code/src/bimodal_logic/tests/ -v --tb=short`
- [ ] Verify no import errors from removed modules: `PYTHONPATH=code/src python -c "import model_checker; import bimodal_logic"`
- [ ] Check for stale references to deleted modules: `grep -r "from model_checker.builder" code/src/ --include="*.py"` should return nothing (except __main__.py)
- [ ] Check for stale references: `grep -r "from model_checker.output.manager" code/src/ --include="*.py"` should return nothing
- [ ] Check for stale references: `grep -r "from model_checker.output.progress" code/src/ --include="*.py"` should return nothing
- [ ] Update `code/pyproject.toml` testpaths if test collection finds issues with old paths
- [ ] Verify `model-checker` entry point status: if `__main__.py` imports fail, consider removing the `model-checker` entry point from pyproject.toml or adding a guard
- [ ] Remove any empty `__pycache__` directories left behind
- [ ] Run formatter tests explicitly: `PYTHONPATH=code/src pytest code/src/model_checker/output/tests/unit/test_markdown_formatter.py code/src/model_checker/output/tests/unit/test_json_serialization.py code/src/model_checker/output/tests/unit/test_color_formatting.py -v`

**Timing**: 30 minutes

**Depends on**: 4

**Files to modify**:
- `code/pyproject.toml` - Potentially update testpaths or remove model-checker entry point
- Various `__pycache__/` directories - Clean up

**Verification**:
- Zero test collection errors
- All bimodal tests pass (627+ expected)
- All CLI tests pass
- All formatter tests pass
- `PYTHONPATH=code/src python -c "from bimodal_logic import Z3OracleProvider; print('OK')"` succeeds
- No stale imports referencing deleted modules

---

## Testing & Validation

- [ ] Bimodal theory tests pass after each phase (627+ tests)
- [ ] Formatter tests pass (test_markdown_formatter, test_json_serialization, test_color_formatting)
- [ ] New CLI tests pass (6+ tests for bimodal-logic check command)
- [ ] No pytest collection errors
- [ ] `import model_checker` succeeds without pulling in builder
- [ ] `import bimodal_logic` succeeds
- [ ] `bimodal-logic check` CLI produces valid JSON output

## Artifacts & Outputs

- `specs/104_programmatic_api_cleanup/plans/01_dead-code-cleanup-plan.md` (this file)
- `specs/104_programmatic_api_cleanup/summaries/01_dead-code-cleanup-summary.md` (post-implementation)
- `code/src/bimodal_logic/cli.py` (new file)
- `code/src/bimodal_logic/tests/test_cli.py` (new file)

## Rollback/Contingency

Git provides full rollback capability. Each phase is committed separately, so reverting any phase is a single `git revert`. If a phase breaks tests:
1. `git stash` or `git revert` the failing phase
2. Investigate which removed component was still needed
3. Restore only that component and re-run tests
4. Proceed with adjusted removal scope

The builder/ removal is the most impactful change. If it causes unexpected failures outside the bimodal test suite, restore builder/ and instead only remove its `__init__.py` imports from the top-level `model_checker/__init__.py`.
