# Research Report: Per-Example Solver Setting

**Task**: 71 - Add per-example solver setting
**Date**: 2026-03-30
**Session**: sess_1774928471_9iebt6

## Executive Summary

This report documents the research findings for implementing a per-example `solver` field in ModelChecker. The investigation reveals a clear implementation path: the settings infrastructure already supports a `solver` field in general settings, and the solver registry already has precedence logic for CLI > environment > settings > default. The main gap is that `create_solver()` is called **without passing settings** at the point where solvers are created, and example-level solver settings are not currently recognized in `DEFAULT_EXAMPLE_SETTINGS`.

## Current Architecture Analysis

### 1. Solver Registry (Priority Chain)

**Location**: `code/src/model_checker/solver/registry.py`

The current priority order is well-documented (lines 82-113):

```python
def get_active_backend(settings: Optional[Dict[str, Any]] = None) -> str:
    """Get the active solver backend name.

    Priority order:
    1. CLI flag (set via set_cli_backend)
    2. Environment variable MODEL_CHECKER_SOLVER
    3. Settings configuration (solver key)
    4. Default: "z3"
    """
```

**Key finding**: The `settings` parameter is already supported in `get_active_backend()`, but the places where `create_solver()` is called do not pass settings.

### 2. CLI Flag Processing

**Location**: `code/src/model_checker/__main__.py` (lines 290-302)

CLI flags `--z3` and `--cvc5` are processed early in `main()`:

```python
if hasattr(module_flags, 'z3') and module_flags.z3:
    from model_checker.solver import set_cli_backend
    set_cli_backend("z3")
elif hasattr(module_flags, 'cvc5') and module_flags.cvc5:
    from model_checker.solver import set_cli_backend, validate_backend
    try:
        validate_backend("cvc5")
        set_cli_backend("cvc5")
    except ImportError as e:
        print(f"Error: {e}")
```

**Key finding**: CLI flags set a global `_cli_override` that takes precedence over everything else. This behavior is correct and should be preserved.

### 3. Settings Architecture

#### General Settings (theory-level defaults)

**Location**: `code/src/model_checker/models/semantic.py` (lines 52-61)

```python
class SemanticDefaults:
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "sequential": False,
        "maximize": False,
        "solver": "z3",  # Solver backend: "z3" or "cvc5"
    }
```

**Key finding**: A `solver` field already exists in `DEFAULT_GENERAL_SETTINGS` but it is NOT in `DEFAULT_EXAMPLE_SETTINGS`.

#### Example Settings (per-example)

**Location**: `code/src/model_checker/theory_lib/logos/semantic.py` (lines 118-128)

```python
class LogosSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 16,
        'M': None,
        'contingent': True,
        'non_empty': True,
        'non_null': True,
        'disjoint': True,
        'max_time': 10,
        'iterate': False,
        'expectation': None,
    }
```

**Key finding**: No `solver` field exists in `DEFAULT_EXAMPLE_SETTINGS`. This is the first implementation point.

### 4. Settings Flow

**Location**: `code/src/model_checker/builder/example.py`

The `BuildExample` class processes settings in `_initialize_settings()` (lines 116-147):

```python
def _initialize_settings(self, build_module, theory_name):
    from model_checker.settings import SettingsManager

    self.settings_manager = SettingsManager(
        {"semantics": self.semantics},
        build_module.general_settings,
        theory_name=theory_name,
        is_comparison=is_comparison
    )

    self.settings = self.settings_manager.get_complete_settings(
        raw_general,
        self.example_settings,
        build_module.module_flags
    )
```

The `SettingsManager.get_complete_settings()` method merges:
1. Theory defaults
2. General settings (module-level)
3. Example settings (per-example)
4. CLI flags (highest priority)

**Key finding**: The merged `self.settings` dict would contain the final `solver` value, but it's never passed to solver creation.

### 5. Solver Creation Points

**Location**: `code/src/model_checker/models/structure.py`

Solvers are created in two places:

1. `_setup_solver()` (line 159): `solver = create_solver()`
2. `solve()` (line 234): `self.solver = create_solver()`

**Critical finding**: Neither call passes `settings` to `create_solver()`. This is the second implementation point.

### 6. Example Definition Structure

Examples are defined as `[premises, conclusions, settings]`:

```python
# From code/src/model_checker/theory_lib/logos/subtheories/modal/examples.py
MOD_CM_1_settings = {
    'N': 4,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 2,
    'iterate': 2,
    'expectation': True,
}
```

**Key finding**: Adding `'solver': 'cvc5'` here would be the user-facing interface.

## Implementation Points

### Point 1: Add `solver` to DEFAULT_EXAMPLE_SETTINGS

Add the `solver` field to example settings in each theory's `DEFAULT_EXAMPLE_SETTINGS`:

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/semantic.py`
- `code/src/model_checker/theory_lib/bimodal/semantic.py`
- `code/src/model_checker/models/semantic.py` (SemanticDefaults base class)

The field should default to `None` to indicate "use theory/general settings default".

### Point 2: Pass settings to create_solver()

Modify solver creation to pass the merged settings:

**Files to modify**:
- `code/src/model_checker/models/structure.py` - Two call sites

Change from:
```python
solver = create_solver()
```

To:
```python
solver = create_solver(self.settings)
```

### Point 3: Validate solver setting values

Add validation for the `solver` field:

**Files to modify**:
- `code/src/model_checker/settings/settings.py` - Add validation for 'z3'/'cvc5' values
- `code/src/model_checker/builder/validation.py` - Optional validation in example validation

### Point 4: Handle None value in registry

Modify `get_active_backend()` to treat `None` as "not specified":

**File**: `code/src/model_checker/solver/registry.py`

```python
if settings and "solver" in settings and settings["solver"] is not None:
    return settings["solver"]
```

## Precedence Chain (Proposed)

The final precedence chain (highest to lowest):

1. **CLI flags** (`--z3` / `--cvc5`) - Global override, set once at startup
2. **Per-example `solver` setting** - Individual example preference
3. **General settings `solver`** - Module-level preference
4. **Semantic theory defaults** - Theory's preferred solver
5. **Registry default** - "z3"

Note: Environment variable (`MODEL_CHECKER_SOLVER`) should be between CLI and per-example for testing/CI purposes.

## Test Strategy

### Existing Tests

The solver registry already has comprehensive tests in `code/src/model_checker/solver/tests/unit/test_registry.py`:

- `test_default_backend_is_z3()`
- `test_cli_override_takes_priority()`
- `test_settings_used_when_no_cli_override()`
- `test_environment_variable_override()`

### New Tests Needed

1. **Per-example setting test**: Verify example-level solver setting is respected
2. **Precedence test**: Verify CLI > example > general > default
3. **None handling test**: Verify `solver: None` falls through to next level
4. **Validation test**: Verify invalid solver values are rejected
5. **Integration test**: Run same example with different per-example solver settings

## Related Work

### Task 70 (completed)

Fixed cvc5 compatibility issues in `comparison.py`. Key learnings:

- Three-step reset pattern for switching solvers: clear CLI backend, reset registry, reset z3_shim
- `switch_solver()` function pattern for benchmark comparisons
- AtomSort must be reset when switching backends

### Tasks 58-65 (completed)

Migrated from direct z3 imports to solver abstraction layer. The infrastructure is mature and stable.

## Risk Assessment

### Low Risk

- Adding field to `DEFAULT_EXAMPLE_SETTINGS` - Well-established pattern
- Passing settings to `create_solver()` - Already supported, just not used
- Validation - Standard pattern in settings module

### Medium Risk

- Multiple solver creation points - Need to ensure all are updated
- Settings merge order - Must verify example settings override general settings correctly

### No Risk

- CLI override behavior - Already implemented and tested

## Recommendations

1. **Phase 1**: Add `solver` field to `DEFAULT_EXAMPLE_SETTINGS` in all theories
2. **Phase 2**: Modify `ModelDefaults` to pass settings to `create_solver()`
3. **Phase 3**: Add validation for solver field values
4. **Phase 4**: Add comprehensive tests for precedence chain
5. **Phase 5**: Update documentation in `settings/README.md` and `solver/README.md`

The implementation is straightforward due to the excellent existing infrastructure. The main work is connecting the already-existing `solver` field in settings to the already-existing settings parameter in `create_solver()`.

## Files Summary

### Must Modify

| File | Change |
|------|--------|
| `code/src/model_checker/theory_lib/logos/semantic.py` | Add `solver` to `DEFAULT_EXAMPLE_SETTINGS` |
| `code/src/model_checker/theory_lib/bimodal/semantic.py` | Add `solver` to `DEFAULT_EXAMPLE_SETTINGS` |
| `code/src/model_checker/models/structure.py` | Pass settings to `create_solver()` |
| `code/src/model_checker/solver/registry.py` | Handle `None` solver value |

### Should Add

| File | Change |
|------|--------|
| `code/src/model_checker/solver/tests/unit/test_registry.py` | Add per-example precedence tests |

### May Update

| File | Change |
|------|--------|
| `code/src/model_checker/settings/README.md` | Document per-example solver setting |
| `code/src/model_checker/solver/README.md` | Document precedence chain |

## Conclusion

The per-example solver setting feature has a clear implementation path with minimal risk. The existing infrastructure supports all the necessary functionality; the implementation requires connecting existing pieces rather than creating new architecture. The recommended approach is a phased implementation starting with the settings definition and ending with documentation updates.
