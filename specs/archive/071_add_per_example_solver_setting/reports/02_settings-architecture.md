# Deep Research Report: Settings Architecture for Per-Example Solver Setting

**Task**: 71 - Add per-example solver setting
**Date**: 2026-03-30
**Session**: sess_1774928887_jlpe
**Focus**: Settings architecture, merge patterns, and design considerations

## Executive Summary

This deep-dive research examines how settings flow through the ModelChecker system, from theory defaults through user configurations to CLI flags. The investigation reveals a well-designed layered architecture where each layer has clear responsibilities and precedence rules. The key finding is that the `solver` setting can be added to example settings by following the existing pattern, with minimal changes required to connect the settings to solver creation.

## Settings Architecture Overview

### Three-Class Settings System

The settings system uses three distinct classes that work together:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          SETTINGS CLASS HIERARCHY                           │
└─────────────────────────────────────────────────────────────────────────────┘

┌──────────────────────────┐
│    SemanticDefaults      │  Base class (models/semantic.py)
│                          │
│ DEFAULT_GENERAL_SETTINGS │  Framework-wide settings including:
│ • print_impossible       │  - Debug/output options
│ • print_constraints      │  - Display preferences
│ • print_z3               │  - Solver selection: "solver": "z3"
│ • save_output            │
│ • sequential             │
│ • maximize               │
│ • solver: "z3"           │  <-- General default exists!
└──────────────┬───────────┘
               │ Inherits
               ▼
┌──────────────────────────┐
│  Theory Semantics Class  │  e.g., LogosSemantics, BimodalSemantics
│  (theory_lib/*/semantic) │
│                          │
│ DEFAULT_EXAMPLE_SETTINGS │  Theory-specific per-example defaults:
│ • N: bit width           │  - Model parameters
│ • M: time points         │  - Constraint flags
│ • contingent             │  - Solver limits
│ • max_time               │
│ • iterate                │  ** NO "solver" field currently **
│                          │
│ ADDITIONAL_GENERAL_      │  Optional theory-specific general settings
│   SETTINGS (optional)    │  e.g., BimodalSemantics adds align_vertically
└──────────────┬───────────┘
               │ Used by
               ▼
┌──────────────────────────┐
│    SettingsManager       │  Orchestrates merging (settings/settings.py)
│                          │
│ • validate_general_      │  Merges and validates all settings sources
│   settings()             │
│ • validate_example_      │
│   settings()             │
│ • apply_flag_overrides() │
│ • get_complete_settings()│
└──────────────────────────┘
```

### Settings Sources and Precedence

Settings come from five sources with clear precedence (highest to lowest):

| Priority | Source | Code Location | Purpose |
|----------|--------|---------------|---------|
| 1 (Highest) | CLI Flags | `__main__.py` argparse | User command-line overrides |
| 2 | Example Settings | User's example file | Per-example customization |
| 3 | General Settings | User's module file | Module-level preferences |
| 4 | Theory Defaults | `Theory.DEFAULT_*_SETTINGS` | Sensible defaults per theory |
| 5 (Lowest) | System Defaults | `SemanticDefaults.DEFAULT_GENERAL_SETTINGS` | Framework baseline |

## Detailed Settings Flow Analysis

### Stage 1: Module Loading (BuildModule)

**File**: `code/src/model_checker/builder/module.py`

```python
class BuildModule:
    def _initialize_settings(self) -> None:
        """Initialize and validate general settings."""
        from model_checker.settings import SettingsManager, DEFAULT_GENERAL_SETTINGS

        if self.raw_general_settings is not None:
            first_theory = next(iter(self.semantic_theories.values()))
            # Create temporary manager for validation
            temp_manager = SettingsManager(first_theory, DEFAULT_GENERAL_SETTINGS)
            # Validate and merge general settings
            self.general_settings = temp_manager.validate_general_settings(
                self.raw_general_settings
            )
            # Apply CLI flag overrides to general settings
            self.general_settings = temp_manager.apply_flag_overrides(
                self.general_settings,
                self.module_flags
            )
        else:
            self.general_settings = DEFAULT_GENERAL_SETTINGS.copy()
```

**Key Insight**: General settings are processed at module load time, before any examples run. This is where module-level `solver` preference would be captured.

### Stage 2: Example Initialization (BuildExample)

**File**: `code/src/model_checker/builder/example.py`

```python
class BuildExample:
    def _initialize_settings(self, build_module, theory_name):
        from model_checker.settings import SettingsManager

        # Create settings manager for this theory
        self.settings_manager = SettingsManager(
            {"semantics": self.semantics},
            build_module.general_settings,
            theory_name=theory_name,
            is_comparison=is_comparison
        )

        # Get complete settings with all validations
        raw_general = getattr(build_module, 'raw_general_settings',
                             build_module.general_settings)
        self.settings = self.settings_manager.get_complete_settings(
            raw_general,                    # User's general settings
            self.example_settings,          # User's example settings (from example_case[2])
            build_module.module_flags       # CLI flags
        )
```

**Key Insight**: The `self.settings` dict contains the final merged settings for this example. This is where per-example `solver` setting would end up.

### Stage 3: Settings Merging (SettingsManager)

**File**: `code/src/model_checker/settings/settings.py`

```python
class SettingsManager:
    def __init__(self, semantic_theory, global_defaults=None, theory_name=None,
                 is_comparison=False, strict_mode=False):
        # Get semantics class
        semantics_class = semantic_theory.get("semantics")

        # Start with base class general settings
        from model_checker.models.semantic import SemanticDefaults
        self.DEFAULT_GENERAL_SETTINGS = SemanticDefaults.DEFAULT_GENERAL_SETTINGS.copy()

        # Augment with theory-specific additional general settings
        if hasattr(semantics_class, 'ADDITIONAL_GENERAL_SETTINGS'):
            self.DEFAULT_GENERAL_SETTINGS.update(
                semantics_class.ADDITIONAL_GENERAL_SETTINGS
            )

        # Get DEFAULT_EXAMPLE_SETTINGS from theory
        self.DEFAULT_EXAMPLE_SETTINGS = semantic_theory["semantics"].DEFAULT_EXAMPLE_SETTINGS

    def get_complete_settings(self, user_general_settings, user_example_settings,
                              module_flags) -> SettingsDict:
        # 1. Start with validated general settings (defaults + user general)
        general_settings = self.validate_general_settings(user_general_settings)

        # 2. Validate and merge example settings (defaults + user example)
        example_settings = self.validate_example_settings(user_example_settings)

        # 3. Combine: general + example (example takes precedence)
        combined_settings = general_settings.copy()
        combined_settings.update(example_settings)

        # 4. Apply CLI flag overrides (highest priority)
        final_settings = self.apply_flag_overrides(combined_settings, module_flags)

        return final_settings
```

**Critical Pattern**: The merge order is:
1. Theory general defaults
2. + User general settings (overrides defaults)
3. Theory example defaults
4. + User example settings (overrides example defaults)
5. General merged INTO example (example has precedence)
6. + CLI flags (highest priority)

### Stage 4: Solver Creation (ModelDefaults)

**File**: `code/src/model_checker/models/structure.py`

```python
class ModelDefaults:
    def __init__(self, model_constraints, settings):
        self.settings = settings  # <-- The merged settings are available!
        # ... other initialization ...

        # Solve Z3 constraints
        solver_results = self.solve(self.model_constraints, self.max_time)

    def solve(self, model_constraints, max_time):
        # Create a new solver via abstraction layer
        self.solver = create_solver()  # <-- Settings NOT passed!
        # ...
```

**Gap Identified**: `self.settings` is available but `create_solver()` is called without passing it.

### Stage 5: Solver Backend Selection (Registry)

**File**: `code/src/model_checker/solver/registry.py`

```python
def get_active_backend(settings: Optional[Dict[str, Any]] = None) -> str:
    """Get the active solver backend name.

    Priority order:
    1. CLI flag (set via set_cli_backend)
    2. Environment variable MODEL_CHECKER_SOLVER
    3. Settings configuration (solver key)
    4. Default: "z3"
    """
    # 1. CLI flag has highest priority
    if _cli_override:
        return _cli_override

    # 2. Environment variable
    env_solver = os.environ.get("MODEL_CHECKER_SOLVER")
    if env_solver and env_solver in ("z3", "cvc5"):
        return env_solver

    # 3. Settings configuration
    if settings and "solver" in settings:
        return settings["solver"]  # <-- Already supports settings!

    # 4. Default to z3
    return "z3"

def create_solver(settings: Optional[Dict[str, Any]] = None) -> TrackedSolverProtocol:
    backend = get_active_backend(settings)  # <-- Accepts settings parameter
    validate_backend(backend)
    # ... create and return solver
```

**Key Finding**: The registry already supports settings-based solver selection! The infrastructure exists; it's just not being used.

## Example Settings Field Analysis

### Current DEFAULT_EXAMPLE_SETTINGS (LogosSemantics)

```python
DEFAULT_EXAMPLE_SETTINGS = {
    'N': 16,              # Bit-width for states
    'M': None,            # Time steps (optional)
    'contingent': True,   # Constraint flag
    'non_empty': True,    # Constraint flag
    'non_null': True,     # Constraint flag
    'disjoint': True,     # Constraint flag
    'max_time': 10,       # Solver timeout (seconds)
    'iterate': False,     # Model iteration
    'expectation': None,  # Expected result
    # NO 'solver' field
}
```

### Proposed Addition

```python
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
    'solver': None,  # NEW: None means "use theory/general/default"
}
```

### Why `None` as Default?

Using `None` (not `"z3"`) as the default allows the settings merge chain to work correctly:

1. If example sets `solver: None` -> falls through to general settings
2. If general sets `solver: "cvc5"` -> that's used
3. If general is `None` -> falls through to `SemanticDefaults.DEFAULT_GENERAL_SETTINGS["solver"]`
4. If that's `"z3"` -> that's the final default

This preserves the layered override behavior users expect.

## CLI Flag Integration

### Current CLI Processing

**File**: `code/src/model_checker/__main__.py`

```python
def main():
    # ...
    parser = ParseFileFlags()
    module_flags, package_name = parser.parse()

    # Handle solver backend selection (early, before module loading)
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
            return

    # Then load module and run...
    module = BuildModule(module_flags)
```

**Key Insight**: CLI flags set a module-level `_cli_override` in the registry that takes absolute precedence. This happens *before* any settings are even loaded.

### Why CLI Overrides Everything

The registry uses a global `_cli_override` variable:

```python
# Module-level state
_cli_override: Optional[str] = None

def set_cli_backend(backend: str) -> None:
    global _cli_override
    _cli_override = backend

def get_active_backend(settings=None) -> str:
    # CLI flag has highest priority - checked FIRST
    if _cli_override:
        return _cli_override
    # ... then check settings
```

This design ensures that `--z3` or `--cvc5` always wins, regardless of any settings. This is correct behavior: CLI should override everything else.

## Validation Patterns

### Current Example Settings Validation

```python
def validate_example_settings(self, user_example_settings):
    if user_example_settings is None:
        return self.DEFAULT_EXAMPLE_SETTINGS.copy()

    merged_settings = self.DEFAULT_EXAMPLE_SETTINGS.copy()

    # Warn about unknown settings
    for key in user_example_settings:
        if key not in self.DEFAULT_EXAMPLE_SETTINGS:
            self._warn_unknown_setting(key, 'example')

    # Merge valid settings
    valid_keys = set(user_example_settings.keys()).intersection(
        self.DEFAULT_EXAMPLE_SETTINGS.keys()
    )
    for key in valid_keys:
        merged_settings[key] = user_example_settings[key]

    return merged_settings
```

**Implication**: Adding `solver` to `DEFAULT_EXAMPLE_SETTINGS` automatically enables it as a valid user setting. No separate validation code needed for the field itself.

### Proposed Value Validation

However, we should add validation for the *value* of the solver field:

```python
# In validate_example_settings or as a separate validator
def _validate_solver_setting(self, settings):
    if 'solver' in settings and settings['solver'] is not None:
        if settings['solver'] not in ('z3', 'cvc5'):
            raise ValidationError(
                f"Invalid solver value '{settings['solver']}'. "
                f"Must be 'z3', 'cvc5', or None."
            )
```

## Theory Comparison Mode

### How Comparison Handles Solver Switching

**File**: `code/src/model_checker/theory_lib/logos/comparison.py`

```python
def switch_solver(backend: str) -> None:
    """Switch to specified solver backend with full cache invalidation."""
    from model_checker.syntactic.atoms import reset_atom_sort

    # Clear CLI backend first
    clear_cli_backend()
    # Reset registry caches
    reset_registry()
    # Reset z3_shim cached module
    z3_shim._reset_backend()
    # Reset AtomSort so it's recreated for the new backend
    reset_atom_sort()
    # Set new backend
    set_cli_backend(backend)
```

**Key Learning**: Switching solvers mid-session requires clearing multiple caches. For per-example settings, this is NOT necessary because:
1. Each example already creates a fresh solver instance
2. The solver backend is determined at `create_solver()` time
3. Settings are already per-example

However, if two examples in the same module use different solvers, they need isolation. The current architecture already handles this because `create_solver()` is called fresh for each example in `ModelDefaults.solve()`.

## Design Recommendations

### 1. Add `solver` to DEFAULT_EXAMPLE_SETTINGS

Add to both theory classes with `None` default:

```python
# LogosSemantics
DEFAULT_EXAMPLE_SETTINGS = {
    # ... existing fields ...
    'solver': None,  # NEW: None = use general/default, 'z3' or 'cvc5' = override
}

# BimodalSemantics
DEFAULT_EXAMPLE_SETTINGS = {
    # ... existing fields ...
    'solver': None,
}
```

### 2. Pass Settings to create_solver()

In `ModelDefaults.solve()`:

```python
def solve(self, model_constraints, max_time):
    # Pass settings to enable per-example solver selection
    self.solver = create_solver(self.settings)  # CHANGED
```

And in `_setup_solver()`:

```python
def _setup_solver(self, model_constraints):
    solver = create_solver(self.settings)  # CHANGED
```

### 3. Handle None in Registry

```python
def get_active_backend(settings=None) -> str:
    if _cli_override:
        return _cli_override

    env_solver = os.environ.get("MODEL_CHECKER_SOLVER")
    if env_solver and env_solver in ("z3", "cvc5"):
        return env_solver

    # Handle None explicitly
    if settings and "solver" in settings and settings["solver"] is not None:
        return settings["solver"]

    return "z3"
```

### 4. Add Validation (Optional but Recommended)

In SettingsManager:

```python
def _validate_solver_value(self, value):
    if value is not None and value not in ('z3', 'cvc5'):
        raise ValidationError(
            f"Invalid solver '{value}'. Valid values: 'z3', 'cvc5', None"
        )
```

## Precedence Chain Summary

After implementation, the complete precedence chain will be:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                     SOLVER SELECTION PRECEDENCE (Highest to Lowest)         │
└─────────────────────────────────────────────────────────────────────────────┘

Priority 1: CLI Flags (--z3 / --cvc5)
    │       Set once at startup via set_cli_backend()
    │       Stored in _cli_override global
    │       ALWAYS checked first in get_active_backend()
    │
    ▼
Priority 2: Environment Variable (MODEL_CHECKER_SOLVER)
    │       Useful for CI/testing environments
    │       Checked before any settings
    │
    ▼
Priority 3: Per-Example Settings (example's 'solver' field)
    │       NEW: From example_case[2] dict
    │       Allows: {'solver': 'cvc5', ...}
    │
    ▼
Priority 4: General Settings (module's 'solver' field)
    │       From module's general_settings dict
    │       Falls through if example solver is None
    │
    ▼
Priority 5: Theory Defaults (SemanticDefaults.DEFAULT_GENERAL_SETTINGS)
    │       Currently: "solver": "z3"
    │
    ▼
Priority 6: Registry Default
            Hardcoded "z3" in get_active_backend()
```

## User Interface After Implementation

### Example File Usage

```python
# In examples.py

# Example using z3 (explicit)
EX1_settings = {
    'N': 4,
    'max_time': 5,
    'solver': 'z3',  # Use z3 for this example
}

# Example using cvc5 (explicit)
EX2_settings = {
    'N': 4,
    'max_time': 5,
    'solver': 'cvc5',  # Use cvc5 for this example
}

# Example using module default (implicit)
EX3_settings = {
    'N': 4,
    'max_time': 5,
    # No 'solver' key = use general_settings default
}

# Module-level preference
general_settings = {
    'solver': 'cvc5',  # Default solver for this module
}

example_range = {
    'example1': [premises1, conclusions1, EX1_settings],  # Uses z3
    'example2': [premises2, conclusions2, EX2_settings],  # Uses cvc5
    'example3': [premises3, conclusions3, EX3_settings],  # Uses cvc5 (from general)
}
```

### CLI Override

```bash
# Force all examples to use z3, regardless of settings
model-checker examples.py --z3

# Force all examples to use cvc5
model-checker examples.py --cvc5
```

## Risk Assessment

### Minimal Risk Items

1. **Adding field to DEFAULT_EXAMPLE_SETTINGS**: Standard pattern, well-tested
2. **Passing settings to create_solver()**: Parameter already exists, just unused
3. **Handling None in registry**: Simple null check

### Requires Careful Testing

1. **Example isolation**: Verify different solvers in same module work correctly
2. **Merge order**: Verify example settings override general settings
3. **CLI override**: Verify CLI still takes absolute precedence

## Conclusion

The settings architecture is well-designed for this addition:

1. The layered settings system naturally supports per-example overrides
2. The solver registry already accepts settings but isn't being used
3. Adding the `solver` field follows established patterns
4. No architectural changes needed, only connecting existing pieces

The implementation should be straightforward, focusing on:
1. Adding `'solver': None` to `DEFAULT_EXAMPLE_SETTINGS` in both theories
2. Passing `self.settings` to `create_solver()` in two places
3. Adding null handling in `get_active_backend()`
4. Adding value validation for robustness
5. Comprehensive tests for the precedence chain

## Files Summary

| File | Change | Risk |
|------|--------|------|
| `models/semantic.py` | No change needed (already has `solver` in general) | N/A |
| `theory_lib/logos/semantic.py` | Add `'solver': None` to `DEFAULT_EXAMPLE_SETTINGS` | Low |
| `theory_lib/bimodal/semantic.py` | Add `'solver': None` to `DEFAULT_EXAMPLE_SETTINGS` | Low |
| `models/structure.py` | Pass `self.settings` to `create_solver()` (2 places) | Low |
| `solver/registry.py` | Add null check in `get_active_backend()` | Low |
| `settings/settings.py` | Add solver value validation (optional) | Low |
