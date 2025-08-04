# Workflow: Using the ModelChecker Package Effectively

[← Back to Methodology](README.md) | [Architecture →](ARCHITECTURE.md) | [Iterator →](ITERATOR.md)

## Table of Contents

1. [Introduction](#introduction)
2. [Basic Workflows](#basic-workflows)
   - [Running Single Examples](#running-single-examples)
   - [Batch Testing with examples.py](#batch-testing-with-examplespy)
   - [Using dev_cli.py for Development](#using-dev_clipy-for-development)
   - [Command-line Options and Flags](#command-line-options-and-flags)
3. [Theory Development Workflow](#theory-development-workflow)
   - [Creating New Theories from Templates](#creating-new-theories-from-templates)
   - [Testing with Unit Tests](#testing-with-unit-tests)
   - [Running Example Validation](#running-example-validation)
   - [Using Iterate to Explore Semantic Space](#using-iterate-to-explore-semantic-space)
4. [Debugging Workflows](#debugging-workflows)
   - [Using Debug Settings](#using-debug-settings)
   - [Command-line Debug Flags](#command-line-debug-flags)
   - [Interpreting Z3 Unsat Cores](#interpreting-z3-unsat-cores)
   - [Common Error Patterns and Fixes](#common-error-patterns-and-fixes)
5. [Performance Optimization](#performance-optimization)
   - [Setting Appropriate N Values](#setting-appropriate-n-values)
   - [Timeout Configuration](#timeout-configuration)
   - [Iteration Settings Tuning](#iteration-settings-tuning)
   - [Memory Management Strategies](#memory-management-strategies)
6. [Integration Patterns](#integration-patterns)
   - [CLI Integration](#cli-integration)
   - [Test Framework Integration](#test-framework-integration)
   - [CI/CD Testing Patterns](#cicd-testing-patterns)
   - [Documentation Generation](#documentation-generation)
7. [Common Recipes](#common-recipes)
8. [Troubleshooting](#troubleshooting)
9. [References](#references)

## Introduction

This guide provides practical workflows for using the ModelChecker framework effectively, from basic usage to advanced development patterns. Whether you're running examples, developing new theories, or debugging complex logical formulas, these workflows will help you work efficiently with the framework.

The ModelChecker follows a pipeline architecture where formulas flow through syntax parsing, semantic constraint generation, and Z3 model finding. Understanding these workflows helps you leverage the full power of the framework for your logical investigations.

## Basic Workflows

### Running Single Examples

The simplest workflow is running a single example file to test logical formulas:

```bash
# Using the installed package
model-checker examples/my_example.py

# Using the development CLI (from Code/ directory)
./dev_cli.py examples/my_example.py

# With specific settings
model-checker examples/my_example.py --N=5 --verbose
```

**Example file structure**:
```python
from model_checker.theory_lib.logos import get_theory

theory = get_theory()

# Define your example
MY_EXAMPLE_premises = ["A \\wedge B"]
MY_EXAMPLE_conclusions = ["A"]
MY_EXAMPLE_settings = {
    'N': 3,
    'contingent': False,
    'max_time': 10
}
MY_EXAMPLE_example = [
    MY_EXAMPLE_premises,
    MY_EXAMPLE_conclusions,
    MY_EXAMPLE_settings
]

# Required exports
example_range = {
    "MY_EXAMPLE": MY_EXAMPLE_example
}

semantic_theories = {
    "logos": theory
}
```

### Batch Testing with examples.py

Theory modules include comprehensive example files for batch testing:

```bash
# Run all examples for a theory
model-checker theory_lib/logos/examples.py

# Run specific examples by modifying example_range
# In examples.py:
example_range = {
    "EXT_TH_1": EXT_TH_1_example,  # Include this
    # "MODAL_TH_1": MODAL_TH_1_example,  # Comment out to skip
}
```

**Batch testing workflow**:
1. Navigate to theory directory
2. Review available examples in examples.py
3. Modify example_range to select specific tests
4. Run with appropriate flags for your needs

### Using dev_cli.py for Development

The development CLI provides direct access to local source code without installation:

```bash
# Basic usage (same as model-checker)
./dev_cli.py examples/test.py

# With isomorphism debugging
./dev_cli.py --iso-debug examples/iterate_test.py

# Generate new theory project
./dev_cli.py -l logos my_new_theory

# Run with all debug output
./dev_cli.py -p -z examples/debug_test.py
```

**Development workflow advantages**:
- No installation required
- Immediate code changes reflection
- Additional debug flags
- Direct source debugging

### Command-line Options and Flags

Common flags and their uses:

```bash
# Verbosity and output control
--verbose, -v          # Show detailed progress
--quiet, -q           # Suppress non-essential output

# Constraint and Z3 output
--print-constraints, -p    # Show generated constraints
--print-z3, -z            # Show Z3 model details
--print-impossible        # Show impossible states

# Performance settings
--N=<int>                # Set maximum atomic propositions
--max-time=<seconds>     # Set solver timeout
--iterate=<int>          # Find multiple models

# Theory selection
--theory=<name>          # Select specific theory
--compare               # Compare multiple theories

# Development flags
--save-output           # Save output to file
--iso-debug            # Debug isomorphism checking
```

## Theory Development Workflow

### Creating New Theories from Templates

Start a new theory implementation:

```bash
# Generate from existing theory template
model-checker -l logos my_counterfactual_theory
# or using dev CLI
./dev_cli.py -l logos my_counterfactual_theory

# Generated structure
project_my_counterfactual_theory/
├── __init__.py
├── semantic.py         # Core semantics implementation
├── operators.py        # Operator definitions
├── examples.py         # Example formulas
├── tests/             # Unit tests
├── docs/              # Documentation
└── notebooks/         # Interactive tutorials
```

**Development steps**:
1. Modify semantic.py to implement your semantics
2. Define operators in operators.py
3. Create test examples in examples.py
4. Write unit tests in tests/
5. Document your theory in docs/

### Testing with Unit Tests

Run comprehensive tests during development:

```bash
# Run all tests for your theory
./run_tests.py my_counterfactual_theory

# Run only unit tests
./run_tests.py --unit my_counterfactual_theory

# Run only example tests
./run_tests.py --examples my_counterfactual_theory

# Run with verbose output
./run_tests.py --verbose my_counterfactual_theory

# Run specific test with pytest
pytest project_my_counterfactual_theory/tests/test_semantic.py -v
```

**Test-driven development workflow**:
1. Write failing test for new feature
2. Implement minimal code to pass
3. Refactor while keeping tests green
4. Add integration examples
5. Run full test suite before committing

### Running Example Validation

Validate your theory against standard examples:

```bash
# Run your theory's examples
model-checker project_my_counterfactual_theory/examples.py

# Compare with reference theory
model-checker project_my_counterfactual_theory/examples.py --compare

# Run with specific settings override
model-checker project_my_counterfactual_theory/examples.py --N=5 --contingent
```

**Validation workflow**:
1. Start with simple tautologies
2. Add invalid formulas expecting countermodels
3. Test edge cases (empty premises, contradictions)
4. Verify expected vs actual results
5. Compare with established theories

### Using Iterate to Explore Semantic Space

Explore multiple models for your formulas:

```python
# In your examples.py
EXPLORE_settings = {
    'N': 4,
    'iterate': 5,  # Find up to 5 distinct models
    'max_time': 30,
    'expectation': True  # Expect countermodels
}
```

```bash
# Run with iteration
model-checker examples/explore.py

# Output shows:
# MODEL 1/5
# [First model details]
# 
# MODEL 2/5
# === DIFFERENCES FROM PREVIOUS MODEL ===
# [Structural differences]
```

**Iteration workflow**:
1. Start with small iterate values (2-3)
2. Analyze differences between models
3. Adjust constraints if models are too similar
4. Use for understanding semantic variations
5. Document interesting model patterns

## Debugging Workflows

### Using Debug Settings

Enable detailed output for troubleshooting:

```python
# In your examples.py
DEBUG_settings = {
    'N': 3,
    'print_constraints': True,  # Show all Z3 constraints
    'print_z3': True,          # Show Z3 model details
    'print_impossible': True,   # Show impossible states
    'max_time': 60,            # Longer timeout for debugging
}
```

**Debug information interpretation**:
- Constraints show the logical requirements
- Z3 output reveals satisfying assignments
- Impossible states indicate semantic restrictions

### Command-line Debug Flags

Override settings from command line:

```bash
# Full debug output
./dev_cli.py -p -z examples/debug.py

# Specific debug aspects
model-checker examples/test.py --print-constraints
model-checker examples/test.py --print-z3
model-checker examples/test.py --print-impossible

# Save debug output
model-checker examples/test.py -p -z --save-output
```

### Interpreting Z3 Unsat Cores

When no model is found, understand why:

```bash
# Enable unsat core extraction
model-checker examples/unsat.py --unsat-core

# Common unsat patterns:
# 1. Contradictory premises: "A" and "\\neg A"
# 2. Impossible constraints: contingent=False with tautology
# 3. Over-constrained semantics: too many restrictions
```

**Unsat debugging workflow**:
1. Simplify example to minimal failing case
2. Enable constraint printing
3. Check for obvious contradictions
4. Relax constraints incrementally
5. Compare with working examples

### Common Error Patterns and Fixes

**Pattern 1: Formula Parsing Errors**
```python
# Error: Unmatched parentheses
BAD: "A \\wedge (B \\vee C"  # Missing closing parenthesis
GOOD: "A \\wedge (B \\vee C)"

# Error: Unknown operator
BAD: "A & B"  # Use LaTeX notation
GOOD: "A \\wedge B"
```

**Pattern 2: Setting Conflicts**
```python
# Error: Incompatible settings
BAD: {'contingent': False, 'non_contingent': True}
GOOD: {'contingent': False}  # Use one setting

# Error: N too small
BAD: {'N': 2}  # With 3 atoms A, B, C
GOOD: {'N': 3}  # Or reduce atoms
```

**Pattern 3: Theory Mismatches**
```python
# Error: Operator not in theory
# Using \\boxright in modal-only theory
# Solution: Load counterfactual subtheory
theory = get_theory(subtheories=['modal', 'counterfactual'])
```

## Performance Optimization

### Setting Appropriate N Values

The N parameter controls state space size (2^N states):

```python
# Performance impact:
# N=3: 8 states (fast)
# N=4: 16 states (moderate)
# N=5: 32 states (slower)
# N=6: 64 states (may timeout)

# Optimization strategies:
# 1. Start with minimal N
N_minimal = len(atomic_propositions)

# 2. Increase only if needed
if "unsat" in result:
    settings['N'] = N_minimal + 1

# 3. Use theory-specific minimums
# Modal logic often needs N+1 for accessibility
```

### Timeout Configuration

Balance thoroughness with responsiveness:

```python
# Quick exploration
QUICK_settings = {
    'max_time': 1,  # 1 second timeout
    'N': 3,
}

# Thorough analysis
THOROUGH_settings = {
    'max_time': 60,  # 1 minute timeout
    'N': 5,
}

# Iteration with timeouts
ITERATE_settings = {
    'max_time': 10,              # Per model timeout
    'iterate': 5,
    'iteration_timeout': 2,      # Isomorphism check timeout
    'iteration_solver_timeout': 5 # Z3 timeout per iteration
}
```

### Iteration Settings Tuning

Optimize iteration for your use case:

```python
# Fast iteration (find different valuations)
FAST_ITERATE = {
    'iterate': 3,
    'max_invalid_attempts': 2,
    'iteration_attempts': 3,
    'escape_attempts': 1
}

# Thorough iteration (find structurally different)
THOROUGH_ITERATE = {
    'iterate': 10,
    'max_invalid_attempts': 5,
    'iteration_attempts': 5,
    'escape_attempts': 3
}

# Debug iteration issues
DEBUG_ITERATE = {
    'iterate': 2,
    'verbose': True,
    'print_constraints': True
}
```

### Memory Management Strategies

Handle large state spaces efficiently:

```python
# 1. Use incremental solving
for n in range(3, 6):
    settings['N'] = n
    result = run_example(settings)
    if result.satisfiable:
        break

# 2. Limit iteration scope
settings['iterate'] = min(5, 2**(settings['N']-1))

# 3. Clean up between runs
import gc
gc.collect()

# 4. Monitor memory usage
import psutil
process = psutil.Process()
print(f"Memory: {process.memory_info().rss / 1024 / 1024:.1f} MB")
```

## Integration Patterns

### CLI Integration

Integrate ModelChecker into shell scripts:

```bash
#!/bin/bash
# run_analysis.sh

# Run multiple theories
for theory in logos exclusion imposition; do
    echo "Testing $theory..."
    model-checker -l $theory test_formula <<EOF
FORMULA_premises = ["A \\boxright B"]
FORMULA_conclusions = ["\\neg B \\boxright \\neg A"]
FORMULA_settings = {'N': 4}
FORMULA_example = [FORMULA_premises, FORMULA_conclusions, FORMULA_settings]

example_range = {"FORMULA": FORMULA_example}
semantic_theories = {theory: get_theory()}
EOF
done

# Collect results
model-checker examples/*.py --save-output > results.txt
```

### Test Framework Integration

Integrate with pytest or unittest:

```python
# test_logical_principles.py
import pytest
from model_checker import BuildExample
from model_checker.theory_lib.logos import get_theory

class TestLogicalPrinciples:
    @pytest.fixture
    def theory(self):
        return get_theory()
    
    def test_modus_ponens(self, theory):
        example = BuildExample(
            premises=["A", "A \\rightarrow B"],
            conclusions=["B"],
            settings={'N': 3}
        )
        result = example.check(theory)
        assert not result.countermodel_found
    
    def test_invalid_inference(self, theory):
        example = BuildExample(
            premises=["A \\vee B"],
            conclusions=["A"],
            settings={'N': 3, 'expectation': True}
        )
        result = example.check(theory)
        assert result.countermodel_found
```

### CI/CD Testing Patterns

GitHub Actions workflow:

```yaml
# .github/workflows/test.yml
name: ModelChecker Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v2
    
    - name: Set up Python
      uses: actions/setup-python@v2
      with:
        python-version: '3.10'
    
    - name: Install dependencies
      run: |
        pip install -e Code/
        pip install pytest
    
    - name: Run theory tests
      run: |
        cd Code
        ./run_tests.py --examples
    
    - name: Run unit tests
      run: |
        cd Code
        ./run_tests.py --unit
    
    - name: Validate examples
      run: |
        model-checker theory_lib/*/examples.py --quiet
```

### Documentation Generation

Generate documentation from examples:

```python
# generate_docs.py
import os
from pathlib import Path

def document_examples(theory_path):
    """Extract and document examples from theory."""
    examples_file = Path(theory_path) / "examples.py"
    
    # Parse examples
    examples = parse_example_file(examples_file)
    
    # Generate markdown
    doc = f"# {theory_path.name} Examples\n\n"
    for name, example in examples.items():
        doc += f"## {name}\n"
        doc += f"**Premises**: {example[0]}\n"
        doc += f"**Conclusions**: {example[1]}\n"
        doc += f"**Valid**: {not example[2].get('expectation', False)}\n\n"
    
    # Save documentation
    (Path(theory_path) / "docs" / "EXAMPLES.md").write_text(doc)

# Generate for all theories
for theory in Path("theory_lib").iterdir():
    if theory.is_dir() and (theory / "examples.py").exists():
        document_examples(theory)
```

## Common Recipes

### Recipe: Test Logical Equivalence

```python
# Test if two formulas are equivalent
def test_equivalence(formula1, formula2, theory):
    # Test formula1 → formula2
    forward = BuildExample(
        premises=[formula1],
        conclusions=[formula2],
        settings={'N': 4}
    )
    
    # Test formula2 → formula1
    backward = BuildExample(
        premises=[formula2],
        conclusions=[formula1],
        settings={'N': 4}
    )
    
    return (not forward.has_countermodel() and 
            not backward.has_countermodel())

# Usage
equiv = test_equivalence(
    "A \\wedge B",
    "B \\wedge A",
    get_theory()
)
```

### Recipe: Find Minimal Countermodel

```python
# Find smallest N that yields countermodel
def find_minimal_countermodel(premises, conclusions, theory):
    for n in range(1, 8):
        example = BuildExample(
            premises=premises,
            conclusions=conclusions,
            settings={'N': n, 'max_time': 5}
        )
        result = example.check(theory)
        if result.countermodel_found:
            return n, result
    return None, None

# Usage
n, model = find_minimal_countermodel(
    ["A \\boxright B"],
    ["A \\rightarrow B"],
    get_theory()
)
```

### Recipe: Theory Comparison Report

```python
# Compare multiple theories on same examples
def compare_theories(examples_file, theories):
    from model_checker.builder import BuildModule
    
    results = {}
    for theory_name, theory in theories.items():
        module = BuildModule(examples_file)
        module.semantic_theories = {theory_name: theory}
        
        results[theory_name] = {}
        for example_name in module.example_range:
            result = module.run_example(example_name)
            results[theory_name][example_name] = result
    
    return generate_comparison_table(results)
```

## Troubleshooting

### Issue: "No module named 'model_checker'"

**Solution**: Install the package or use dev_cli.py
```bash
# Install from PyPI
pip install model-checker

# Or use development CLI
cd ModelChecker/Code
./dev_cli.py examples/test.py
```

### Issue: "Z3 timeout" errors

**Solutions**:
1. Increase timeout: `--max-time=30`
2. Reduce N: `--N=3`
3. Simplify formula
4. Check for infinite loops in semantics

### Issue: "Unexpected keyword argument" errors

**Solution**: Check theory compatibility
```python
# List available settings
print(theory.get_available_settings())

# Use only compatible settings
valid_settings = {k: v for k, v in settings.items() 
                  if k in theory.get_available_settings()}
```

### Issue: Iteration finds only isomorphic models

**Solutions**:
1. Increase escape_attempts
2. Add more diverse constraints
3. Check theory's iterate implementation
4. Enable --iso-debug flag

## References

### Command Line Reference
- `model-checker --help` - Full command documentation
- `./dev_cli.py --help` - Development CLI options
- `./run_tests.py --help` - Test runner options

### Configuration Files
- `examples.py` - Standard example format
- `settings.py` - Settings validation
- `.model_checker_config` - User configuration

### Related Documentation
- [Architecture](ARCHITECTURE.md) - System design
- [Iterator System](ITERATOR.md) - Model iteration details
- [Builder Pattern](BUILDER_PATTERN.md) - Pipeline orchestration
- [Development Guide](../../Code/docs/DEVELOPMENT.md) - Contributing

---

[← Back to Methodology](README.md) | [Architecture →](ARCHITECTURE.md) | [Iterator →](ITERATOR.md)