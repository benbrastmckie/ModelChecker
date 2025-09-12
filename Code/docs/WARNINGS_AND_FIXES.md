# Common Warnings and Fixes

## Z3 pkg_resources DeprecationWarning

### The Warning
```
DeprecationWarning: pkg_resources is deprecated as an API
  import pkg_resources
```

### Cause
The Z3 SMT solver library (z3-solver) internally uses the deprecated `pkg_resources` module from setuptools. This is a third-party library issue that needs to be fixed upstream in the Z3 project.

### Impact
- **Cosmetic only** - Does not affect functionality
- Appears during test runs and when importing Z3
- Can clutter test output making it harder to see real issues

### Solution Implemented
Added warning filters to `pyproject.toml` to suppress this specific deprecation warning:

```toml
[tool.pytest.ini_options]
filterwarnings = [
    # Ignore deprecation warning from z3's use of pkg_resources
    "ignore:pkg_resources is deprecated as an API:DeprecationWarning:z3.z3core",
    "ignore:pkg_resources is deprecated as an API:DeprecationWarning",
]
```

### Alternative Solutions

1. **Update Z3 when fixed**: Monitor Z3 releases for a fix to this issue
   - Track: https://github.com/Z3Prover/z3/issues
   - The Z3 team needs to migrate from `pkg_resources` to `importlib.resources`

2. **Runtime suppression** (not recommended):
   ```python
   import warnings
   warnings.filterwarnings("ignore", message="pkg_resources is deprecated")
   ```

3. **Environment variable** (for CI/CD):
   ```bash
   PYTHONWARNINGS="ignore::DeprecationWarning:z3.z3core" pytest
   ```

### When to Remove This Fix
Once Z3 releases a version that no longer uses `pkg_resources`, you can:
1. Update the z3-solver dependency version in `pyproject.toml`
2. Remove the filterwarnings configuration
3. Verify no warnings appear in test output

### Related Issues
- This warning does not indicate any problem with ModelChecker code
- It's a common issue affecting many projects using Z3
- The functionality of Z3 and ModelChecker is not affected

---

**Last Updated**: September 2025  
**Status**: Warning suppressed via pytest configuration