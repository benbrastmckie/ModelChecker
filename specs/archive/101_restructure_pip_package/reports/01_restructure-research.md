# Task 101: Restructure as bimodal-logic pip package — Research Report

**Date**: 2026-06-01  
**Task**: 101  
**Status**: Research complete  

---

## 1. Current State of pyproject.toml

File location: `/home/benjamin/Projects/ModelChecker/code/pyproject.toml`

### Build system
```toml
[build-system]
requires = ["setuptools>=42", "wheel"]
build-backend = "setuptools.build_meta"
```

### Current project metadata
- **name**: `model-checker`
- **version**: `1.2.12`
- **description**: "A hyperintensional theorem prover for developing and exploring programmatic semantic theories."
- **classifiers**: Only `Python :: 3.8`, GPL-3.0+, OS Independent
- **keywords**: semantics, Z3, logic, counterfactuals, modality, model checker, theorem prover, hyperintensionality
- **requires-python**: `>=3.8`
- **dependencies**: `z3-solver>=4.8.0` (already stripped of networkx/jupyter/matplotlib/cvc5)

**Important discrepancy**: The egg-info at `code/src/model_checker.egg-info/requires.txt` still lists `networkx>=2.0` and full jupyter optional deps — this is stale from before task 100. The live `pyproject.toml` already shows only `z3-solver>=4.8.0` as core dependency, which is correct. The egg-info will be regenerated on `pip install -e .`.

### Current package directory mapping
```toml
[tool.setuptools]
package-dir = {"" = "src"}

[tool.setuptools.packages.find]
where = ["src"]
```
This discovers `model_checker` as the installable package from `code/src/model_checker/`.

### Current entry point
```toml
[project.scripts]
model-checker = "model_checker.__main__:run"
```

### Current pytest config
```toml
[tool.pytest.ini_options]
pythonpath = "src"
testpaths = ["src/model_checker/theory_lib"]
python_files = "test_*.py"
python_classes = "Test*"
addopts = "--durations=0 -v --import-mode=importlib"
```
`testpaths` already points at `src/model_checker/theory_lib` (task 100 already narrowed it). Task 101 should narrow further to `src/model_checker/theory_lib/bimodal/tests/`.

### Optional dependencies
```toml
[project.optional-dependencies]
all = ["z3-solver>=4.8.0"]
```
The `[jupyter]` and `all` groups still exist but only contain z3-solver — safe to simplify or remove the redundant `all` group.

---

## 2. Directory Structure Map (What Exists Now)

```
code/src/
├── model_checker/                          # Current installable package
│   ├── __init__.py                         # Exports: ModelConstraints, Syntax, ForAll, Exists, ...
│   ├── __main__.py                         # CLI entry point: ParseFileFlags, main(), run()
│   ├── cli.py                              # Thin wrapper calling __main__.main
│   ├── z3_shim.py                          # Lazy backend switcher (z3 default, cvc5 optional)
│   ├── builder/                            # BuildModule, BuildProject, BuildExample
│   │   ├── comparison.py, detector.py, errors.py, error_types.py
│   │   ├── example.py, filesystem.py, importer.py, loader.py
│   │   ├── module.py, project.py, protocols.py, runner.py, runner_utils.py
│   │   ├── serialize.py, strategies.py, translation.py, types.py
│   │   ├── validation.py, z3_utils.py
│   │   └── tests/  (unit/, integration/, e2e/, fixtures/, utils/)
│   ├── models/                             # ModelConstraints, SemanticDefaults, PropositionDefaults
│   │   ├── constraints.py, errors.py, proposition.py, semantic.py, structure.py, types.py
│   │   └── tests/  (unit/, integration/)
│   ├── output/                             # OutputManager, formatters (json, markdown, base)
│   │   ├── collectors.py, config.py, constants.py, errors.py, helpers.py
│   │   ├── input_provider.py, manager.py, prompts.py, sequential_manager.py
│   │   ├── formatters/  (base.py, json.py, markdown.py)
│   │   ├── progress/  (animated.py, core.py, display.py, spinner.py)
│   │   └── tests/  (unit/, integration/)
│   ├── settings/                           # SettingsManager, ValidationError
│   │   ├── errors.py, settings.py, types.py
│   │   └── tests/  (unit/, integration/)
│   ├── solver/                             # Z3/cvc5 abstraction layer
│   │   ├── backend.py, compat.py, cvc5_adapter.py, expressions.py
│   │   ├── lifecycle.py, protocols.py, registry.py, type_guards.py, types.py
│   │   ├── types_runtime.py, z3_adapter.py
│   │   └── tests/  (unit/)
│   ├── syntactic/                          # Formula parsing: Syntax, Sentence, Atoms, etc.
│   │   ├── assignments.py, atoms.py, collection.py, errors.py, formulas.py
│   │   ├── operators.py, sentence.py, syntax.py, terms.py, types.py
│   │   └── tests/  (unit/, integration/)
│   ├── theory_lib/                         # Theory registry (bimodal only after task 100)
│   │   ├── __init__.py                     # AVAILABLE_THEORIES = ['bimodal'], get_examples(), etc.
│   │   ├── errors.py, meta_data.py, types.py
│   │   ├── tests/  (test_meta_data.py, unit/test_error_handling.py)
│   │   └── bimodal/                        # THE theory — preserved as-is (ADR Decision 3 Rec 1)
│   │       ├── __init__.py                 # Public: BimodalSemantics, BimodalProposition, BimodalStructure, bimodal_operators
│   │       ├── examples.py                 # example_range, test_example_range, semantic_theories
│   │       ├── operators.py                # bimodal_operators collection
│   │       ├── profile_abundance.py        # Profiling utility
│   │       ├── semantic.py                 # BimodalSemantics, BimodalProposition, BimodalStructure
│   │       ├── semantic/                   # Sub-package for witness machinery
│   │       │   ├── __init__.py
│   │       │   ├── witness_constraints.py
│   │       │   └── witness_registry.py
│   │       └── tests/                      # Full test suite (172 tests, 1 pre-existing failure)
│   │           ├── unit/  (test_bimodal.py, test_foralltime.py, test_frame_constraints.py,
│   │           │           test_modal_witness_integration.py, test_until_since.py,
│   │           │           test_witness_constraints.py, test_witness_registry.py)
│   │           ├── integration/  (test_api_consistency.py, test_data_extraction.py,
│   │           │                  test_injection.py, test_strict_semantics.py,
│   │           │                  test_until_since_integration.py)
│   │           ├── e2e/  (test_cli_execution.py)
│   │           ├── fixtures/, utils/
│   │           └── README.md
│   └── utils/                              # ForAll, Exists, bitvec_to_substates, etc.
│       ├── api.py, bitvector.py, context.py, formatting.py, parsing.py
│       ├── testing.py, types.py, version.py, z3_helpers.py
│       └── tests/  (unit/)
└── model_checker.egg-info/                 # Stale — will be replaced by bimodal_logic.egg-info
```

**New directory to create** (task 101):
```
code/src/
└── bimodal_logic/                          # New thin package (pip import name)
    ├── __init__.py                         # Public: Z3OracleProvider placeholder
    ├── provider.py                         # Stub (filled by task 103)
    ├── translation.py                      # Stub (filled by task 102)
    └── serialization.py                    # Stub (filled by task 102)
```

---

## 3. Import Dependency Analysis

### Key insight: Two packages in one source tree

The restructure introduces a **dual-package layout** under `code/src/`:
1. `model_checker/` — existing infrastructure (builder, solver, models, syntactic, output, settings, theory_lib/bimodal)
2. `bimodal_logic/` — new thin facade package that imports from `model_checker`

Both packages are found by `[tool.setuptools.packages.find] where = ["src"]`. The `bimodal_logic` package will import from `model_checker` internally, just like any other consumer would.

### Import paths that must stay `model_checker.*`

All 58 absolute `from model_checker...` imports inside `theory_lib/bimodal/` use the `model_checker` namespace and must remain unchanged (ADR Decision 3 Rec 1). Key patterns:

- `from model_checker import z3_shim as z3` — used in semantic.py, operators.py, witness files
- `from model_checker.solver import is_true, is_false` — semantic.py
- `from model_checker.models.semantic import SemanticDefaults` — semantic.py
- `from model_checker.models.proposition import PropositionDefaults` — semantic.py
- `from model_checker.models.structure import ModelDefaults` — semantic.py
- `from model_checker.utils import ForAll, Exists, bitvec_to_worldstate, pretty_set_print` — semantic.py
- `from model_checker import syntactic` — semantic.py, operators.py
- `from model_checker.syntactic.atoms import get_atom_sort` — semantic.py
- `from model_checker.theory_lib.bimodal.semantic.witness_registry import WitnessRegistry` — semantic.py
- `from model_checker.theory_lib.bimodal.semantic.witness_constraints import WitnessConstraintGenerator` — semantic.py
- `from model_checker.utils import pretty_set_print` — operators.py
- `from model_checker.solver import is_true` — operators.py

The witness sub-package files use relative imports to `theory_lib/bimodal/errors.py`:
- `from ...errors import WitnessConstraintError` — witness_constraints.py
- `from ...errors import WitnessRegistryError, WitnessPredicateError` — witness_registry.py

### `bimodal_logic` import chain (new)

The thin package `bimodal_logic` will import from `model_checker.theory_lib.bimodal`:
```python
# bimodal_logic/__init__.py
from .provider import Z3OracleProvider  # placeholder stub

# bimodal_logic/provider.py (stub placeholder)
class Z3OracleProvider:
    pass
```

Tasks 102 and 103 will fill in translation.py, serialization.py, and the real Z3OracleProvider implementation.

---

## 4. Specific Changes Needed for the Restructure

### 4.1 pyproject.toml — Complete overhaul

**Changes needed:**

1. **Package name**: `model-checker` → `bimodal-logic`
2. **Version**: Reset to `0.1.0` (fresh package, new namespace)
3. **Description**: Update to bimodal-only oracle description
4. **Classifiers**: Update `Python :: 3.8` → `Python :: 3.10`, `Python :: 3.11`, `Python :: 3.12`
5. **Keywords**: Replace with bimodal-specific terms
6. **requires-python**: `>=3.8` → `>=3.10`
7. **dependencies**: Already correct (`z3-solver>=4.8.0` only); remove stale `[all]` optional group
8. **package-dir**: Add `bimodal_logic` discovery (packages.find will handle automatically since both `model_checker` and `bimodal_logic` live under `src/`)
9. **Entry point script**: Update or remove `model-checker` console script — it points at `model_checker.__main__:run` which still works but may not be the right public API for the new package. Keep for now or remove (task description doesn't mention removing it).
10. **New entry point group**: Add:
    ```toml
    [project.entry-points."bimodal_harness.oracle_providers"]
    z3_base = "bimodal_logic.provider:Z3OracleProvider"
    ```
11. **testpaths**: Narrow from `["src/model_checker/theory_lib"]` to `["src/model_checker/theory_lib/bimodal/tests"]`

### 4.2 New thin files under `code/src/bimodal_logic/`

Four files needed:

**`bimodal_logic/__init__.py`**:
```python
"""bimodal_logic — Z3-based bimodal logic oracle package."""
from .provider import Z3OracleProvider

__all__ = ["Z3OracleProvider"]
```

**`bimodal_logic/provider.py`** (stub for task 103):
```python
"""Z3OracleProvider — stub to be implemented in task 103."""

class Z3OracleProvider:
    """Placeholder. Full implementation in task 103."""
    pass
```

**`bimodal_logic/translation.py`** (stub for task 102):
```python
"""Formula JSON translation — stub to be implemented in task 102."""
```

**`bimodal_logic/serialization.py`** (stub for task 102):
```python
"""Result serialization — stub to be implemented in task 102."""
```

### 4.3 Pytest testpaths update

Change:
```toml
testpaths = ["src/model_checker/theory_lib"]
```
To:
```toml
testpaths = ["src/model_checker/theory_lib/bimodal/tests"]
```

This ensures only bimodal tests run by default. All other theory_lib tests (meta_data, error_handling) are less critical and can be added back separately if needed.

---

## 5. Risk Areas and Potential Issues

### Risk 1: Dual-package discovery (LOW risk)
`packages.find where=["src"]` will now discover both `model_checker` (and all subpackages) AND `bimodal_logic`. Setuptools handles this correctly. Both packages will be installed when `pip install bimodal-logic` or `pip install -e .` is run. This is intentional — `model_checker` provides the infrastructure, `bimodal_logic` provides the public facade.

**Mitigation**: Verify both packages appear in `pip show bimodal-logic` output after install.

### Risk 2: Entry point stub references non-existent class methods (LOW risk)
The entry point `bimodal_logic.provider:Z3OracleProvider` is a stub that exists but does nothing. This is valid — entry point loading is lazy (only triggered when a consumer calls `pkg_resources.iter_entry_points('bimodal_harness.oracle_providers')`). The stub class just needs to be importable.

**Mitigation**: `import bimodal_logic; from bimodal_logic.provider import Z3OracleProvider` must not raise `ImportError`.

### Risk 3: egg-info namespace collision (LOW risk)
The old `model_checker.egg-info` exists at `code/src/`. After renaming the package to `bimodal-logic`, a new `bimodal_logic.egg-info` will be generated. The old egg-info should be removed to avoid confusion. It does not affect runtime imports but clutters the source tree.

**Mitigation**: Delete `code/src/model_checker.egg-info/` before or during `pip install -e .` (pip will regenerate).

### Risk 4: `__main__.py` still checks for jupyter/matplotlib/networkx (NEGLIGIBLE risk)
`__main__.py` lines 257-269 check for `ipywidgets`, `matplotlib`, `networkx` at runtime if `--jupyter` flag is passed. These packages are no longer dependencies, but the check is guarded by the flag — no import actually happens unless the user explicitly passes `--jupyter`. Since the task description says to remove those deps from pyproject.toml (already done), the runtime check will simply warn the user that those packages are missing, which is correct behavior.

**Mitigation**: Optional — can clean up `__main__.py` to remove the jupyter-check block entirely, as it references the old API. Not strictly required for task 101.

### Risk 5: `cvc5_adapter.py` still imports cvc5 at runtime (LOW risk)
`solver/cvc5_adapter.py` does `from cvc5.pythonic import Solver` but only inside the class `__init__` method, so it only fails if someone actually instantiates the adapter. The `registry.py` selects adapters by backend name — Z3 is the default and cvc5 is only loaded if explicitly requested. Since cvc5 is not installed, any attempt to use it will raise `ImportError` with a helpful message. This is acceptable behavior.

**Mitigation**: No change needed for task 101. If desired, cvc5 references could be cleaned up in a future task.

### Risk 6: Python >=3.10 requirement (LOW risk)
Current code runs on Python 3.12 (confirmed). The task says `>=3.10` because "protocol uses modern type syntax." The codebase uses `from __future__ import annotations` or `typing.Protocol` in several places — needs verification that no 3.8-specific workarounds are needed. Since the system Python is 3.12, this constraint is safe.

**Mitigation**: Run tests after changing requires-python to confirm.

### Risk 7: Pre-existing test failure (KNOWN, NOT task 101 scope)
`BM_CM_1` test case fails in the current codebase (1 failure in 172 tests). This is a pre-existing issue from before task 101, not caused by restructure work. Do not attempt to fix during task 101.

### Risk 8: `model-checker` console script in new `bimodal-logic` package (MEDIUM risk)
The current `[project.scripts]` entry `model-checker = "model_checker.__main__:run"` will still be present after renaming. This means installing `bimodal-logic` installs a `model-checker` CLI command. This is semantically odd — the CLI is the old model-checker interface, not the new oracle API. The task description does not explicitly say to remove or update this. 

**Decision needed**: Remove the console script (cleaner for a library package) or keep it (preserves CLI for development/debugging). Recommended: keep it during task 101 since the oracle API is a programmatic interface, not a CLI tool, but this could be removed in task 104 (programmatic API cleanup).

---

## 6. Test Configuration Changes Needed

### Current pytest configuration
```toml
[tool.pytest.ini_options]
pythonpath = "src"
testpaths = ["src/model_checker/theory_lib"]
```

This already excludes most non-bimodal tests (task 100 narrowed it from `src/`). However, `src/model_checker/theory_lib` still includes:
- `bimodal/tests/` (172 tests, 1 pre-existing failure)
- `tests/test_meta_data.py` (theory lib meta data tests)
- `tests/unit/test_error_handling.py`

### Recommended change
```toml
testpaths = ["src/model_checker/theory_lib/bimodal/tests"]
```

This focuses pytest exclusively on the bimodal logic test suite, which is the correctness gate for this package. The meta_data and error_handling tests can be re-added as needed.

### Additional consideration: builder/models/output tests
The builder, models, output, settings, solver, syntactic, and utils modules all have their own test suites under `src/model_checker/{module}/tests/`. These are NOT currently in testpaths and will not run by default. This is acceptable for the bimodal oracle package — the builder infrastructure tests are secondary to the logic correctness tests.

---

## 7. Summary of All Changes Required

| File/Action | Change |
|---|---|
| `code/pyproject.toml` | name, version, description, classifiers, keywords, requires-python, remove `[all]` optional-deps, add `[project.entry-points."bimodal_harness.oracle_providers"]`, update testpaths |
| `code/src/bimodal_logic/__init__.py` | Create new file (imports Z3OracleProvider) |
| `code/src/bimodal_logic/provider.py` | Create new stub file (Z3OracleProvider placeholder class) |
| `code/src/bimodal_logic/translation.py` | Create new stub file (empty) |
| `code/src/bimodal_logic/serialization.py` | Create new stub file (empty) |
| `code/src/model_checker.egg-info/` | Delete (stale, will be regenerated) |
| All existing model_checker imports | NO CHANGES — preserved as-is per ADR Decision 3 Rec 1 |

### Verification steps
1. `pip install -e . --break-system-packages` (or in a venv) from `code/` directory
2. `python -c "import bimodal_logic; print(bimodal_logic.__all__)"` — should print `['Z3OracleProvider']`
3. `python -c "from bimodal_logic.provider import Z3OracleProvider; print(Z3OracleProvider)"` — should print the class
4. `python -c "import model_checker; print(model_checker.__version__)"` — existing package still importable
5. `PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/ -v` from `code/` — 171 pass, 1 pre-existing failure (BM_CM_1)
6. `pip show bimodal-logic` — shows both packages installed

---

## Appendix: pyproject.toml Proposed New Content

```toml
[build-system]
requires = ["setuptools>=42", "wheel"]
build-backend = "setuptools.build_meta"

[project]
name = "bimodal-logic"
version = "0.1.0"
description = "Z3-based bimodal logic oracle: temporal and modal reasoning for the bimodal_harness."
authors = [
    { name = "Benjamin Brast-McKie", email = "benbrastmckie@gmail.com" },
]
license = { text = "GPL-3.0-or-later" }
readme = "README.md"
classifiers = [
    "Programming Language :: Python :: 3.10",
    "Programming Language :: Python :: 3.11",
    "Programming Language :: Python :: 3.12",
    "License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)",
    "Operating System :: OS Independent",
    "Topic :: Scientific/Engineering :: Mathematics",
    "Topic :: Software Development :: Libraries :: Python Modules",
]
keywords = ["bimodal logic", "temporal logic", "modal logic", "Z3", "SMT", "model checking", "oracle", "theorem prover"]
dependencies = [
    "z3-solver>=4.8.0",
]
requires-python = ">=3.10"

[project.urls]
Homepage = "https://github.com/benbrastmckie/ModelChecker"
Issues = "https://github.com/benbrastmckie/ModelChecker/issues"

[project.scripts]
model-checker = "model_checker.__main__:run"

[project.entry-points."bimodal_harness.oracle_providers"]
z3_base = "bimodal_logic.provider:Z3OracleProvider"

[tool.setuptools]
package-dir = {"" = "src"}
include-package-data = true

[tool.setuptools.packages.find]
where = ["src"]

[tool.setuptools.package-data]
"*" = ["README.md", "*.md", "*.ipynb"]

[tool.pytest.ini_options]
pythonpath = "src"
testpaths = ["src/model_checker/theory_lib/bimodal/tests"]
python_files = "test_*.py"
python_classes = "Test*"
addopts = "--durations=0 -v --import-mode=importlib"
markers = [
    "countermodel: Tests that verify a countermodel exists",
    "theorem: Tests that verify a formula is a theorem",
    "performance: Tests that verify performance characteristics",
]
filterwarnings = [
    "ignore:pkg_resources is deprecated as an API:DeprecationWarning:z3.z3core",
    "ignore:pkg_resources is deprecated as an API:DeprecationWarning",
]
```
