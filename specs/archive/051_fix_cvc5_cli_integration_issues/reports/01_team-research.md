# Research Report: Task #51

**Task**: Fix cvc5 CLI integration issues
**Date**: 2026-03-30
**Mode**: Team Research (2 teammates)

## Summary

Both teammates independently confirmed the root cause and recommended the same fix approach. The warning "Flag 'cvc5' doesn't correspond to any known setting" occurs because `z3` and `cvc5` are not in the `standard_args` set in settings.py. The "Z3 Run Time" label is hardcoded in structure.py:840. Comprehensive audit revealed additional Z3 references and an additional missing flag (`subtheory`).

## Key Findings

### 1. Root Cause: Missing `standard_args` Entries

**File**: `code/src/model_checker/settings/settings.py`, line 233

```python
standard_args = {'load_theory', 'upgrade', 'version', 'save',
                'interactive', 'output_mode', 'sequential_files'}
```

The `z3` and `cvc5` CLI flags are parsed by argparse but not included in `standard_args`. When `_apply_overrides()` iterates over `vars(module_flags)`, it finds `cvc5=True` (or `z3=True`), and since these aren't in `merged_settings`, `DEFAULT_EXAMPLE_SETTINGS`, or `standard_args`, it prints the warning.

**Additional Bug**: The `subtheory` flag is also missing from `standard_args` (discovered by Teammate B).

### 2. Hardcoded "Z3 Run Time" Label

**Primary Location**: `code/src/model_checker/models/structure.py`, line 840

```python
def _print_runtime_footer(self, output: TextIO) -> None:
    """Print Z3 runtime and separator footer."""
    print(f"\nZ3 Run Time: {self.z3_model_runtime} seconds", file=output)
```

**Secondary Location**: `structure.py`, line 505 (in template string for generated test files)

```python
inputs_template = Template(
'''Z3 run time: ${z3_model_runtime} seconds
```

### 3. Comprehensive Z3 Reference Audit

| File | Location | Content | Priority |
|------|----------|---------|----------|
| `models/structure.py` | line 840 | `"Z3 Run Time: ..."` | **HIGH** - main user output |
| `models/structure.py` | line 505 | Template: `Z3 run time:` | MEDIUM - generated files |
| `builder/example.py` | line 269 | `"Z3 error while finding next model"` | LOW - error message |
| `iterate/models.py` | line 161 | `"Z3 error building model"` | LOW - logger error |
| `iterate/iterator.py` | line 56 | `"Check that the Z3 solver..."` | LOW - suggestion |

Internal attribute names (`z3_model_runtime`, `z3_model_status`, etc.) should NOT be renamed - they are implementation details, not user-facing.

### 4. Backend Detection Mechanism

**File**: `code/src/model_checker/solver/registry.py`

`get_active_backend()` is already used in `z3_shim.py` and `solver/expressions.py`. It returns `"z3"` or `"cvc5"` based on CLI override, environment variable, or settings.

### 5. Test Impact

**No tests will break** from changing "Z3 Run Time" to "Solver Run Time":
- No tests assert the literal string "Z3 Run Time"
- Tests use the `z3_model_runtime` attribute (unchanged)
- `_print_runtime_footer` is not directly tested for output content

## Synthesis

### Conflicts Resolved

None - both teammates agreed on the approach and findings.

### Gaps Identified

1. **Additional `subtheory` flag** should be added to `standard_args` (found by Teammate B)
2. **Lower-priority Z3 references** in error messages (builder/example.py, iterate/models.py) could be made backend-aware in a future task

### Recommendations

#### Fix 1: Add z3/cvc5/subtheory to standard_args

**File**: `code/src/model_checker/settings/settings.py`, line 233

Change:
```python
standard_args = {'load_theory', 'upgrade', 'version', 'save',
                'interactive', 'output_mode', 'sequential_files'}
```

To:
```python
standard_args = {'load_theory', 'upgrade', 'version', 'save',
                'interactive', 'output_mode', 'sequential_files',
                'z3', 'cvc5', 'subtheory'}
```

#### Fix 2: Backend-Aware or Neutral Label

**File**: `code/src/model_checker/models/structure.py`, line 840

**Option A - Neutral Label (Simpler)**:
```python
print(f"\nSolver Run Time: {self.z3_model_runtime} seconds", file=output)
```

**Option B - Backend-Aware Label**:
```python
from model_checker.solver import get_active_backend
backend = get_active_backend().upper()
print(f"\n{backend} Run Time: {self.z3_model_runtime} seconds", file=output)
```

**Recommendation**: Option A (neutral label) is simpler, requires no import, and is future-proof for additional backends.

#### Fix 3: Update Docstring

The docstring at line 838 says "Print Z3 runtime" - update to "Print solver runtime".

#### Fix 4 (Optional): Template String

Update the template at line 505 to use "Solver run time" for generated test files.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary Implementation | completed | high |
| B | Audit & Alternatives | completed | high |

## Implementation Notes

1. **Test verification**: Run existing tests after fix to confirm no regressions
2. **Scope**: Focus on the two high-priority fixes (standard_args + runtime label)
3. **Future work**: Lower-priority Z3 references in error messages could be addressed separately

## References

- `code/src/model_checker/settings/settings.py` - Settings processing
- `code/src/model_checker/models/structure.py` - Model output formatting
- `code/src/model_checker/solver/registry.py` - Backend detection
- `code/src/model_checker/__main__.py` - CLI flag handling
