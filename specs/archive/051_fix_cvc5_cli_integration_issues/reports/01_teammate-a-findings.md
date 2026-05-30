# Teammate A Findings: cvc5 CLI Integration Issues

## Key Findings

### 1. Root Cause of "Flag 'cvc5' doesn't correspond to any known setting" Warning

**File**: `code/src/model_checker/settings/settings.py`, line 233

The warning is produced in `_apply_overrides()` at line 253:

```python
elif key not in standard_args:
    print(f"Warning: Flag '{key}' doesn't correspond to any known setting")
```

The `standard_args` set (line 233-234) is:
```python
standard_args = {'load_theory', 'upgrade', 'version', 'save',
                'interactive', 'output_mode', 'sequential_files'}
```

When the user passes `--z3` or `--cvc5`, argparse adds `z3=True` and `cvc5=False` (or vice versa) as attributes on `module_flags`. The `_apply_overrides()` loop iterates over all `vars(module_flags)` and hits `z3` and `cvc5`. Neither `z3` nor `cvc5` appears in `merged_settings` or `DEFAULT_EXAMPLE_SETTINGS`, and neither is in `standard_args`, so the warning fires.

**Fix**: Add `'z3'` and `'cvc5'` to the `standard_args` set.

### 2. Hardcoded "Z3 Run Time" Label in structure.py

**File**: `code/src/model_checker/models/structure.py`, line 840

```python
def _print_runtime_footer(self, output: TextIO) -> None:
    """Print Z3 runtime and separator footer."""
    print(f"\nZ3 Run Time: {self.z3_model_runtime} seconds", file=output)
    print(f"\n{'='*40}", file=output)
```

This is the user-facing output label that should be backend-aware.

**Second hardcoded reference** at line 505 (inside `print_save_input()` - generates test file content):
```python
inputs_template = Template(
'''Z3 run time: ${z3_model_runtime} seconds
```

This one generates code/template content rather than direct UI output, so it's a lower-priority fix.

### 3. How `get_active_backend()` Works

**File**: `code/src/model_checker/solver/registry.py`, lines 82-113

`get_active_backend(settings=None)` returns the active backend name by checking in priority order:
1. `_cli_override` (set via `set_cli_backend()` from `__main__.py` at lines 291-302)
2. Environment variable `MODEL_CHECKER_SOLVER`
3. `settings["solver"]` key if provided
4. Default: `"z3"`

It returns a plain string `"z3"` or `"cvc5"`. This is importable from `model_checker.solver`.

### 4. CLI Flag Processing Flow

**File**: `code/src/model_checker/__main__.py`, lines 148-160 and 288-302

The `--z3` / `--cvc5` flags are parsed by argparse as `store_true` in a mutually exclusive group. After `parser.parse()` (line 288), the main function checks:

```python
if hasattr(module_flags, 'z3') and module_flags.z3:
    from model_checker.solver import set_cli_backend
    set_cli_backend("z3")
elif hasattr(module_flags, 'cvc5') and module_flags.cvc5:
    from model_checker.solver import set_cli_backend, validate_backend
    try:
        validate_backend("cvc5")
        set_cli_backend("cvc5")
    ...
```

So by the time `_apply_overrides()` is called (later in the flow), `_cli_override` is already set correctly - the `z3`/`cvc5` attributes on `module_flags` have already been consumed and processed into the registry.

### 5. Other Hardcoded Z3 References in User-Facing Strings

In `structure.py`:
- Line 840: `"\nZ3 Run Time: {self.z3_model_runtime} seconds"` - **primary fix target**
- Line 505: `'Z3 run time: ${z3_model_runtime} seconds` - in generated test file template (secondary)

In `iterate/iterator.py`, line 56:
- `"Check that the Z3 solver successfully generated a model"` - error message, acceptable since it's a diagnostic for the solver layer

These internal error strings (in `errors.py`, `builder/error_types.py`) reference "Z3 solver" in technical error descriptions, not in routine user output. These are acceptable to leave as-is since they describe the internal solver component.

## Recommended Approach

### Fix 1: Add z3/cvc5 to standard_args (settings.py:233)

Change:
```python
standard_args = {'load_theory', 'upgrade', 'version', 'save',
                'interactive', 'output_mode', 'sequential_files'}
```

To:
```python
standard_args = {'load_theory', 'upgrade', 'version', 'save',
                'interactive', 'output_mode', 'sequential_files',
                'z3', 'cvc5'}
```

**Rationale**: `z3` and `cvc5` are CLI-only flags consumed by `__main__.py` before settings processing begins. They are structural flags (like `upgrade`, `version`) that modify execution mode, not semantic settings.

### Fix 2: Backend-Aware Label in _print_runtime_footer (structure.py:838-841)

Import `get_active_backend` at the top of structure.py or inline at call site, then:

```python
def _print_runtime_footer(self, output: TextIO) -> None:
    """Print solver runtime and separator footer."""
    from model_checker.solver import get_active_backend
    backend = get_active_backend()
    backend_label = backend.upper()
    print(f"\n{backend_label} Run Time: {self.z3_model_runtime} seconds", file=output)
    print(f"\n{'='*40}", file=output)
```

**Alternative**: Use a neutral label like `"Solver Run Time"` to avoid any backend-specific name in the string:

```python
print(f"\nSolver Run Time: {self.z3_model_runtime} seconds", file=output)
```

The neutral label is simpler (no import needed) and future-proof. If explicit backend labeling is desired, the `get_active_backend()` approach is available.

### Fix 3: Attribute Rename (Optional/Low Priority)

The attribute `self.z3_model_runtime` on `ModelDefaults` is named after the Z3 backend. If the team wants full consistency, rename it to `self.solver_runtime`. However, this is a broader refactor touching many files and is not strictly necessary for the bug fixes.

## Evidence/Examples

### Warning Trigger Path

```
CLI: model-checker --cvc5 examples.py
  -> argparse sets module_flags.cvc5 = True, module_flags.z3 = False
  -> __main__.py:294: set_cli_backend("cvc5") called
  -> settings._apply_overrides() iterates vars(module_flags)
  -> hits key='cvc5', value=True
  -> 'cvc5' not in merged_settings -> not in DEFAULT_EXAMPLE_SETTINGS -> not in standard_args
  -> prints "Warning: Flag 'cvc5' doesn't correspond to any known setting"
```

### get_active_backend() Call Pattern

Already used in `z3_shim.py` and `solver/expressions.py` via inline import:
```python
from model_checker.solver import get_active_backend
backend = get_active_backend()
```

This pattern is established and safe to use in structure.py.

## Confidence Level

- **Fix 1 (standard_args)**: HIGH - the warning path is clear and the fix is minimal/isolated
- **Fix 2 (backend label)**: HIGH - `get_active_backend()` is already used by other modules; neutral label is even simpler
- **Fix 3 (attribute rename)**: MEDIUM - correctness is clear, but scope is wider (many callers of `z3_model_runtime`)
