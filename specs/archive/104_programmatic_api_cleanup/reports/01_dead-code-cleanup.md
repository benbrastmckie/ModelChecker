# Task 104: Dead Code Cleanup and Thin CLI Research Report

**Date**: 2026-06-01
**Task**: Identify dead code in `code/src/model_checker/` and design thin CLI for bimodal_logic package
**Status**: Research complete

---

## 1. Oracle Pipeline Import Chain

The oracle pipeline starts at `bimodal_logic.provider.Z3OracleProvider.find_countermodel()` and pulls in:

```
bimodal_logic.provider
  -> bimodal_logic.translation          (json_to_prefix, temporal_depth, prefix_to_infix, fold_formula)
  -> bimodal_logic.serialization        (serialize_countermodel)
  -> model_checker.utils.context        (isolated_z3_context)
  -> model_checker.ModelConstraints     (__init__.py -> models.constraints)
  -> model_checker.Syntax               (__init__.py -> syntactic)
  -> model_checker.theory_lib.bimodal   (BimodalSemantics, BimodalProposition, BimodalStructure, bimodal_operators)
      -> model_checker.theory_lib.bimodal.semantic     (semantic.py, semantic/*)
      -> model_checker.theory_lib.bimodal.operators    (operators.py)
  -> model_checker.solver               (is_true, registry, lifecycle, z3_adapter)
  -> model_checker.models.*             (constraints, semantic, proposition, structure)
  -> model_checker.syntactic.*          (Syntax, atoms, operators, ...)
  -> model_checker.utils.*              (bitvector, z3_helpers, formatting, context, ...)
  -> model_checker.z3_shim              (z3 wrapper)
  -> model_checker.settings.settings   (SettingsManager, DEFAULT_GENERAL_SETTINGS)
```

The `model_checker.__init__` is imported, which pulls in `builder` (BuildModule, BuildProject) and `__main__` (ParseFileFlags, main). This means the oracle pipeline transitively imports the entire CLI stack including builder, output manager, etc. — even though it never uses them. This is a coupling problem, but removing it would require changes to `model_checker/__init__.py`.

### Modules Directly Used by the Oracle Pipeline (excluding test infrastructure)

| Module | Used By | Keep |
|--------|---------|------|
| `bimodal_logic/provider.py` | Entry point | YES |
| `bimodal_logic/serialization.py` | provider.py | YES |
| `bimodal_logic/translation.py` | provider.py, __init__.py | YES |
| `bimodal_logic/__init__.py` | public facade | YES |
| `theory_lib/bimodal/semantic.py` | provider.py | YES |
| `theory_lib/bimodal/semantic/witness_registry.py` | semantic.py | YES |
| `theory_lib/bimodal/semantic/witness_constraints.py` | semantic.py | YES |
| `theory_lib/bimodal/operators.py` | provider.py | YES |
| `theory_lib/bimodal/__init__.py` | provider.py | YES |
| `theory_lib/bimodal/examples.py` | tests, __init__.py report | YES |
| `models/constraints.py` | provider.py indirectly | YES |
| `models/semantic.py` | semantic.py | YES |
| `models/proposition.py` | semantic.py | YES |
| `models/structure.py` | semantic.py | YES |
| `syntactic/*.py` | Syntax class | YES |
| `solver/*.py` | is_true, registry | YES |
| `utils/context.py` | provider.py | YES |
| `utils/bitvector.py` | semantic.py | YES |
| `utils/z3_helpers.py` | semantic.py | YES |
| `utils/formatting.py` | structure.py | YES |
| `utils/parsing.py` | syntactic | YES |
| `utils/api.py` | utils __init__ | YES |
| `utils/version.py` | __init__.py | YES |
| `utils/testing.py` | tests | YES |
| `settings/settings.py` | module.py (SettingsManager) | YES (needed by CLI chain) |
| `z3_shim.py` | semantic.py, runner.py | YES |
| `theory_lib/__init__.py` | meta | YES |
| `theory_lib/meta_data.py` | theory_lib | REVIEW |

---

## 2. File-by-File Inventory: `code/src/model_checker/builder/`

### Used only by the multi-theory CLI (candidates for removal or simplification)

| File | Purpose | Status | Recommendation |
|------|---------|--------|----------------|
| `builder/project.py` (BuildProject) | Scaffolds new theory projects from templates | CLI-only | **REMOVE** - pure project scaffolding for the multi-theory CLI; unreachable from oracle pipeline |
| `builder/comparison.py` (ModelComparison) | Compares theories at max N using ProcessPoolExecutor | CLI-only (`--maximize` flag) | **REMOVE** - only used when `module.general_settings["maximize"]` is True via `__main__.py` |
| `builder/module.py` (BuildModule) | Loads examples.py modules, manages output | CLI-only | **REMOVE** - the Oracle pipeline never calls BuildModule |
| `builder/runner.py` (ModelRunner) | Runs examples with progress bars, iterations | CLI-only | **REMOVE** - only called by BuildModule.runner |
| `builder/runner_utils.py` | Helper utilities for runner | CLI-only | **REMOVE** - only imported by runner.py |
| `builder/loader.py` | Loads Python modules dynamically | CLI-only | **REMOVE** - only used by BuildModule._load_module() |
| `builder/example.py` (BuildExample) | Wraps a single model-check call | CLI-only | **REMOVE** - used by runner.py and module.py, but not the oracle |
| `builder/importer.py` | Package import helpers | CLI-only | **REMOVE** - used by loader.py |
| `builder/filesystem.py` | File system protocol for DI | CLI-only | **REMOVE** - used by loader.py/strategies.py |
| `builder/strategies.py` | Import strategy implementations | CLI-only | **REMOVE** - used by loader.py |
| `builder/translation.py` (OperatorTranslation) | Translates operators across theories | CLI-only | **REMOVE** - used by module.py for multi-theory mode |
| `builder/serialize.py` | Serializes semantic theories for multiprocessing | CLI-only (comparison.py) | **REMOVE** - used by comparison.py and runner.py |
| `builder/detector.py` | Detects file/package types | CLI-only | **REMOVE** - used by loader.py |
| `builder/protocols.py` | Protocol definitions | CLI-only | **REMOVE** - used internally by builder |
| `builder/validation.py` | Settings validation helpers | CLI-only | **REMOVE** - used by runner_utils.py |
| `builder/z3_utils.py` | Z3 utility helpers in builder context | CLI-only | **REMOVE** - used by runner_utils.py |
| `builder/types.py` | Type aliases for builder | CLI-only | **REMOVE** - used by builder modules |
| `builder/errors.py` + `builder/error_types.py` | Builder error types | CLI-only | **REMOVE** - used by builder modules |
| `builder/__init__.py` | Exports BuildModule, BuildProject | CLI only (via __main__.py) | **REMOVE/SIMPLIFY** |

**Critical note**: `builder/` is imported by `model_checker/__init__.py`, which the oracle pipeline pulls in. However, the oracle pipeline only uses `ModelConstraints`, `Syntax`, `BimodalSemantics`, etc. — not BuildModule or BuildProject. The fix is to remove the builder imports from `model_checker/__init__.py`.

### Builder tests (all CLI-only)

All tests in `builder/tests/` test the CLI-only components. If `builder/` is removed, these tests are removed with it.

---

## 3. File-by-File Inventory: `code/src/model_checker/output/`

### Used only by the multi-theory CLI (candidates for removal or simplification)

| File | Purpose | Status | Recommendation |
|------|---------|--------|----------------|
| `output/progress/` (all 4 files) | Animated progress bars, spinner | CLI-only | **REMOVE** - OracleProvider returns dicts; no interactive UI needed |
| `output/prompts.py` | Interactive yes/no prompts | CLI-only | **REMOVE** - OracleProvider is non-interactive |
| `output/sequential_manager.py` | Sequential save prompting | CLI-only | **REMOVE** - depends on prompts.py; no interactive saves |
| `output/input_provider.py` | Console input abstraction | CLI-only | **REMOVE** - used only by sequential_manager.py |
| `output/manager.py` (OutputManager) | Orchestrates output saving | CLI-only | **REMOVE** - only used by BuildModule |
| `output/collectors.py` (ModelDataCollector) | Collects model data for output | CLI-only | **REMOVE** - only used by BuildModule._prepare_model_data |
| `output/config.py` (OutputConfig, create_output_config) | Output config from CLI flags | CLI-only | **REMOVE** - only used by BuildModule |
| `output/constants.py` | FORMAT_MARKDOWN, FORMAT_NOTEBOOK, etc. | CLI-only | **REMOVE** - only referenced by manager.py, errors.py |
| `output/helpers.py` | save_file, save_json, ensure_directory | CLI-only | **REMOVE** - only used by manager.py |
| `output/errors.py` | Output-specific error types | CLI-only | **REMOVE** - only used by manager.py |
| `output/__init__.py` | Exports all output components | CLI-only | **REMOVE/SIMPLIFY** |

**Keep**:
| File | Reason |
|------|--------|
| `output/formatters/` (base.py, markdown.py, json.py, __init__.py) | Task description explicitly says keep; used for structured output |

**Notes on notebook references**: The `output/constants.py` defines `FORMAT_NOTEBOOK` and `DEFAULT_NOTEBOOK_FILE`. The `output/errors.py` has a `NotebookGenerationError`. The test `output/tests/unit/test_notebook_formatter.py` imports `model_checker.output.formatters.notebook` — but there is no `formatters/notebook.py` file. This is already dead code (broken import in a test that doesn't exercise real code). The notebook formatter never existed in the current codebase.

---

## 4. `__main__.py` (the existing multi-theory CLI)

The current `__main__.py` entry point:
- `ParseFileFlags`: Builds argparse parser with `--maximize`, `--save`, `--sequential`, `--load_theory`, `--subtheory` flags
- `main()`: Calls `BuildProject.ask_generate()` (interactive project scaffolding), `module.comparison.run_comparison()`, `module.runner.run_examples()`

### Logos-specific branching remnants in `__main__.py`

Lines 303-313 contain logos-specific logic:
```python
if hasattr(module_flags, 'subtheory') and module_flags.subtheory:
    if semantic_theory_name != 'logos':
        print(f"Error: The --subtheory flag only applies to the logos theory, not '{semantic_theory_name}'")
        return
    builder = BuildProject(semantic_theory_name, subtheories=module_flags.subtheory)
```
The `--subtheory` flag is not even defined in `_create_parser()`, so this block is unreachable dead code. It was a logos-specific remnant.

Additionally, the example usage text in the argparse epilog includes `%(prog)s -l logos examples.py` which references the non-existent logos theory.

### `cli.py` (debugging artifact)

`code/src/model_checker/cli.py` contains `debug_imports()` which calls `print()` unconditionally and runs on import. This is a debugging artifact that should be removed entirely — it is not referenced by any other module or test.

---

## 5. `model_checker/__init__.py` Cleanup

The current `__init__.py` imports:
```python
from .builder import (BuildModule, BuildProject)
from .builder.example import BuildExample
from .__main__ import (ParseFileFlags, main)
```

These pull in the entire CLI stack (builder, output, progress bars, etc.) on every `import model_checker`. The oracle pipeline does `from model_checker import ModelConstraints, Syntax` which triggers this.

**Recommendation**: Remove the builder and `__main__` imports from `model_checker/__init__.py`. The oracle pipeline only needs:
- `ModelConstraints` (from `models.constraints`)
- `Syntax` (from `syntactic`)
- The utility functions (ForAll, Exists, bitvec_to_substates, etc.)

---

## 6. Thin CLI Design

### Objective
Add a `bimodal-logic` entry point to `pyproject.toml` that supports:
```
bimodal-logic check '<formula_json>'
```

### Location
New file: `code/src/bimodal_logic/cli.py`

### Design

```python
"""bimodal_logic.cli - Thin CLI for standalone countermodel checking."""
import argparse
import json
import sys

def main():
    parser = argparse.ArgumentParser(
        prog='bimodal-logic',
        description='Z3-based bimodal logic countermodel checker',
    )
    subparsers = parser.add_subparsers(dest='command')
    
    check_parser = subparsers.add_parser('check', help='Check formula for countermodel')
    check_parser.add_argument('formula_json', type=str, help='JSON formula string')
    check_parser.add_argument('--timeout', type=int, default=5000, help='Solver timeout in ms')
    check_parser.add_argument('--frame-class', default='Base', help='Frame class to check')

    args = parser.parse_args()
    
    if args.command == 'check':
        formula = json.loads(args.formula_json)
        from .provider import Z3OracleProvider
        provider = Z3OracleProvider()
        result = provider.find_countermodel(formula, frame_class=args.frame_class, timeout_ms=args.timeout)
        if result is None:
            print(json.dumps({"result": "valid", "countermodel": None}))
        else:
            print(json.dumps({"result": "invalid", "countermodel": result}))
    else:
        parser.print_help()
        sys.exit(1)

def run():
    main()
```

### pyproject.toml addition
```toml
[project.scripts]
bimodal-logic = "bimodal_logic.cli:run"
```

### Design Rationale
- Keeps existing `model-checker` entry point (`model_checker.__main__:run`) intact — no breakage
- New `bimodal-logic` entry point is in the `bimodal_logic` package (separate from `model_checker`)
- Uses `Z3OracleProvider` as the sole backend — consistent with the oracle pipeline
- Outputs JSON to stdout for machine-readable use
- `BimodalStructure.print_*` methods are NOT called by this thin CLI; the CLI only serializes the oracle dict result

---

## 7. Test Coverage Analysis

### Tests that reference removable components

**builder/tests/**: All 20+ test files test CLI-only components. If builder/ is removed, all these tests are removed with them. Risk: LOW (they test code being deleted).

**output/tests/**: Most test CLI-only components:
- `test_notebook_formatter.py` - imports non-existent `formatters/notebook.py`; already broken
- `test_progress_*.py` - test progress bars (removing with progress/)
- `test_prompts.py` - tests prompt_yes_no, prompt_choice (removing with prompts.py)
- `test_input_provider.py` - tests ConsoleInputProvider (removing)
- `test_prompt_manager.py` - tests SequentialSaveManager (removing)

**Keep from output/tests/**:
- `unit/test_markdown_formatter.py` - tests MarkdownFormatter (keeping formatters/)
- `unit/test_json_serialization.py` - tests JSONFormatter (keeping formatters/)
- `unit/test_color_formatting.py` - tests ANSIToMarkdown (keeping formatters/)

### Tests that do NOT reference removable components

All tests in `theory_lib/bimodal/tests/` are safe — they only import from:
- `model_checker.theory_lib.bimodal.*`
- `model_checker.syntactic.*`
- `model_checker.solver.*`
- `model_checker.models.*`
- `model_checker.utils.context`
- `bimodal_logic.*`

The e2e test `tests/e2e/test_cli_execution.py` calls `dev_cli.py` via subprocess and tests the full CLI. This test should be removed (it tests the old multi-theory CLI).

---

## 8. Risk Assessment

### Low-risk removals (clearly dead, no test references in keep list)

| Component | Risk | Notes |
|-----------|------|-------|
| `builder/comparison.py` | LOW | Only used by `--maximize` flag; bimodal has no multi-theory use case |
| `builder/project.py` | LOW | Interactive scaffolding; no programmatic use |
| `builder/runner.py` | LOW | Only called by BuildModule; tests removed with it |
| `output/progress/` | LOW | Pure UI widgets; oracle is headless |
| `output/prompts.py` | LOW | Interactive prompts; oracle is headless |
| `cli.py` (debug file) | LOW | Debug artifact with unconditional print() calls |

### Medium-risk changes (require care in scope)

| Component | Risk | Notes |
|-----------|------|-------|
| `model_checker/__init__.py` builder imports | MEDIUM | Removing `BuildModule`, `BuildProject`, `BuildExample`, `ParseFileFlags`, `main` from `__init__.__all__` could break external callers who use `from model_checker import BuildModule`. Mitigate by checking if any external package (other than tests) does this. |
| `__main__.py` logos branching | LOW-MED | Safe to remove `--subtheory` dead code block; must not break `model-checker` entry point |
| `output/manager.py` | LOW | Removing with builder/; output/formatters/ is kept |

### High-risk (do not remove in this task)

| Component | Risk | Notes |
|-----------|------|-------|
| `settings/settings.py` | HIGH | Task description explicitly says keep; used by BuildModule but also imported by module.py; keeping is correct |
| `output/formatters/` | HIGH | Explicitly required by task; keeping |
| `theory_lib/bimodal/tests/` | HIGH | Explicitly required; keeping |
| `theory_lib/bimodal/examples.py` | HIGH | Explicitly required; keeping |

---

## 9. `profile_abundance.py` (bimodal-only)

`code/src/model_checker/theory_lib/bimodal/profile_abundance.py` — this is a profiling/debugging script in the bimodal theory directory. It is not imported by any other module. It can be removed as dead code, though it's low-priority.

---

## 10. Summary: Recommended Removal Scope

### Remove entirely
- `code/src/model_checker/builder/` (except `__init__.py` if `model-checker` CLI is kept)
- `code/src/model_checker/output/progress/`
- `code/src/model_checker/output/prompts.py`
- `code/src/model_checker/output/sequential_manager.py`
- `code/src/model_checker/output/input_provider.py`
- `code/src/model_checker/output/manager.py`
- `code/src/model_checker/output/collectors.py`
- `code/src/model_checker/output/config.py`
- `code/src/model_checker/output/constants.py`
- `code/src/model_checker/output/helpers.py`
- `code/src/model_checker/output/errors.py`
- `code/src/model_checker/cli.py` (debug artifact)
- `code/src/model_checker/theory_lib/bimodal/profile_abundance.py`
- `code/src/model_checker/theory_lib/bimodal/tests/e2e/test_cli_execution.py`

### Modify
- `model_checker/__init__.py`: Remove builder and `__main__` imports; remove them from `__all__`
- `model_checker/__main__.py`: Remove logos-specific `--subtheory` dead-code block; clean up help text
- `output/__init__.py`: Simplify to export only formatters
- `bimodal_logic/__init__.py` + `bimodal_logic/cli.py`: Add thin CLI

### Add
- `code/src/bimodal_logic/cli.py`: New thin CLI module
- `code/pyproject.toml`: Add `bimodal-logic = "bimodal_logic.cli:run"` to `[project.scripts]`

### Keep unchanged
- All of `code/src/model_checker/theory_lib/bimodal/` (except `profile_abundance.py` and `tests/e2e/`)
- All of `code/src/model_checker/models/`
- All of `code/src/model_checker/syntactic/`
- All of `code/src/model_checker/solver/`
- All of `code/src/model_checker/utils/`
- All of `code/src/model_checker/settings/`
- `output/formatters/` (base.py, markdown.py, json.py, __init__.py)
- `code/src/bimodal_logic/` (provider.py, serialization.py, translation.py, __init__.py)

---

## 11. CLI Design Alternative: Print-Based Output

The task description mentions `print_*` methods on BimodalStructure are needed for the thin CLI. The thin CLI can optionally support a `--pretty` flag:

```
bimodal-logic check '<formula_json>'           # JSON output (default, machine-readable)
bimodal-logic check '<formula_json>' --pretty  # Calls structure.print_* methods
```

However, since the oracle pipeline (OracleProvider) already serializes the full countermodel to a dict via `serialization.py`, the thin CLI does not need to call `print_*` methods at all for its primary use case. The `print_*` methods remain needed by the existing `model-checker` CLI via BuildExample.print_model(). Keeping them is correct but they are not exercised by the thin CLI.
