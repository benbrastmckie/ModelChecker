# Manual Testing Protocol

[← Testing Standards](TESTING_STANDARDS.md) | [Back to Maintenance](README.md)

## Overview

This document defines the manual testing protocol for ModelChecker. While automated tests provide fast feedback during development, manual testing is **required** to catch integration issues that mocked unit tests miss.

## Why Manual Testing is Essential

### The Problem
Unit tests with mocks can pass while the actual system fails at runtime. For example:
- Method signature mismatches (like `discover_theory_module` taking 1 vs 3 arguments)
- Import resolution issues in theory libraries
- Full pipeline integration problems
- Interactive mode behavior

### The Solution
A two-pronged testing approach:
1. **Automated tests** - Fast, focused unit testing with mocks
2. **Manual tests** - Full integration testing without mocks

## Manual Test Protocol

### Before Each Pull Request

Run ALL manual tests below. Any failure blocks the PR.

### 1. Theory Library Examples

Test each main theory and all subtheories:

```bash
# Main theories
./Code/dev_cli.py src/model_checker/theory_lib/logos/examples.py
./Code/dev_cli.py src/model_checker/theory_lib/exclusion/examples.py
./Code/dev_cli.py src/model_checker/theory_lib/imposition/examples.py
./Code/dev_cli.py src/model_checker/theory_lib/bimodal/examples.py

# Logos subtheories (CRITICAL - these revealed the discover_theory_module bug)
./Code/dev_cli.py src/model_checker/theory_lib/logos/subtheories/modal/examples.py
./Code/dev_cli.py src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py
./Code/dev_cli.py src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py
./Code/dev_cli.py src/model_checker/theory_lib/logos/subtheories/relevance/examples.py
./Code/dev_cli.py src/model_checker/theory_lib/logos/subtheories/extensional/examples.py
```

**Expected**: All examples run without Python errors. Model output displayed.

### 2. Generated Project Testing

```bash
# Step 1: Generate a project
./Code/model-checker
# Choose theory (e.g., logos)
# Enter project name (e.g., test_manual)
# Answer 'n' to run examples

# Step 2: Test the generated project
./Code/dev_cli.py project_test_manual/examples.py
```

**Expected**: Examples run successfully (note: relative imports mean BuildModule can't load these directly).

### 3. Iteration Testing

Test model iteration with each theory:

```bash
# Start iteration mode
./Code/dev_cli.py -i src/model_checker/theory_lib/logos/examples.py

# When prompted "Enter a number to iterate or hit return to continue:"
# Enter: 5
# This tests the iteration logic including discover_theory_module calls
```

**Expected**: 
- Prompts appear correctly
- Entering a number produces additional models
- No Python errors during iteration

### 4. Interactive Save Mode

```bash
# Test interactive save functionality
./Code/dev_cli.py -s src/model_checker/theory_lib/logos/examples.py

# When prompted for save mode:
# Choose 'i' for interactive
# Then 'y' to save models when prompted
```

**Expected**:
- Save prompts work correctly
- Output files created in generated directory
- No errors during save operations

### 5. Comparison Mode

```bash
# Test theory comparison
./Code/dev_cli.py -c src/model_checker/theory_lib/logos/examples.py
```

**Expected**:
- Comparison runs for all semantic theories
- Results displayed in tabular format
- No errors during comparison

### 6. Edge Cases

```bash
# Empty module
echo "semantic_theories = {}; example_range = {}" > /tmp/empty.py
./Code/dev_cli.py /tmp/empty.py

# Module with syntax error
echo "this is not valid python" > /tmp/bad.py
./Code/dev_cli.py /tmp/bad.py

# Non-existent file
./Code/dev_cli.py /tmp/does_not_exist.py
```

**Expected**: Appropriate error messages, no uncaught exceptions.

## Common Issues and Solutions

### Issue: "ModuleLoader.discover_theory_module() takes 1 positional argument but 3 were given"
**Cause**: Method name conflict between two different methods  
**Solution**: Fixed by renaming to `discover_theory_module_for_iteration()`

### Issue: "No module named 'project_NAME'"
**Cause**: Generated projects use relative imports  
**Solution**: This is by design - use proper Python module context

### Issue: Theory library examples fail with import errors
**Cause**: Relative imports require package context  
**Solution**: ModuleLoader now handles theory library imports specially

## Adding New Manual Tests

When adding new features:
1. Add corresponding manual test to this document
2. Run the manual test before committing
3. Consider if an integration test could catch the issue

## Manual Test Checklist

Copy this checklist for each PR:

```markdown
- [ ] All theory library examples run without errors
- [ ] Generated project creation and execution works
- [ ] Iteration mode functions correctly
- [ ] Interactive save mode works
- [ ] Comparison mode executes successfully
- [ ] Edge cases handled appropriately
- [ ] No Python tracebacks in any test
```

## Automation Opportunities

Consider creating integration tests for frequently-tested scenarios:

```python
# test_full_pipeline.py
def test_all_theory_examples():
    """Run all theory examples through actual dev_cli.py."""
    for theory in ['logos', 'exclusion', 'imposition', 'bimodal']:
        result = subprocess.run([
            sys.executable, 'dev_cli.py', 
            f'src/model_checker/theory_lib/{theory}/examples.py'
        ], capture_output=True, text=True)
        assert result.returncode == 0, f"{theory} failed: {result.stderr}"
```

However, manual testing remains essential for:
- Interactive features
- User experience validation
- Unexpected integration issues

---

[← Testing Standards](TESTING_STANDARDS.md) | [Back to Maintenance](README.md)