# Workflow Overview: The Complete ModelChecker Process

[← Previous: Project Setup](PROJECT.md) | [Next: Writing Examples →](EXAMPLES.md)

## Overview: How ModelChecker Works

**ModelChecker** tests if logical inferences are valid by searching for counterexamples:
1. You provide premises and conclusions
2. ModelChecker searches for a model where premises are true but conclusions false
3. If no such model exists, the inference is valid
4. If found, you get the countermodel details

## Quick Workflow Examples

### 1. Test a Simple Inference

```bash
# Does "A and (A implies B)" entail "B"?
model-checker examples.py  # Contains this test
# Result: VALID (no countermodel found)
```

### 2. Find a Counterexample

```bash
# Does "A or B" entail "A"?
model-checker invalid_test.py
# Result: INVALID - Shows model where B is true, A is false
```

### 3. Explore Multiple Models

```bash
# Find different ways premises can be true
model-checker examples.py --iterate=3
# Shows up to 3 different models
```

## Core Workflows

### Running Examples

After creating your project ([see PROJECT.md](PROJECT.md)), test logical formulas:

```bash
# Run examples in your project
cd project_my_theory
model-checker examples.py

# Run with options
model-checker examples.py --N=4        # More atomic propositions  
model-checker examples.py --verbose    # Show details
model-checker examples.py --iterate=3  # Find multiple models
```

**What happens**: ModelChecker reads your formula, generates logical constraints, and uses Z3 to find models. Details in [EXAMPLES.md](EXAMPLES.md).

### Understanding Results

```python
# VALID inference (no countermodel)
Premises: ["A", "A → B"]
Conclusions: ["B"]
Result: No countermodel found (VALID)

# INVALID inference (countermodel exists)
Premises: ["A ∨ B"]
Conclusions: ["A"]
Result: Countermodel found:
  World 0: B is true, A is false
```

See [OUTPUT.md](OUTPUT.md) for saving and formatting results.

### Common Command-Line Options

Essential flags for daily use:

```bash
# Control output
--verbose              # Show detailed progress
--quiet                # Minimal output only

# Debug issues  
--print-constraints    # Show logical constraints
--print-z3            # Show Z3 solver details

# Adjust parameters
--N=5                 # Set max atomic propositions
--iterate=3           # Find multiple models
--max-time=30         # Set timeout (seconds)

# Save results
--save json           # Save as JSON
--save markdown       # Save as Markdown
```

Complete reference in [SETTINGS.md](SETTINGS.md).

## Development Workflow

### Modify Your Theory

After creating a project, develop your custom logic:

```python
# Edit semantic.py - Define your logic rules
class MySemantics(Semantics):
    def _generate_constraints(self):
        # Add your logical constraints
        
# Edit operators.py - Add new operators
class MyOperator(Operator):
    name = "⊕"  # Your symbol
    
# Edit examples.py - Test your logic
MY_TEST_premises = ["A ⊕ B"]
MY_TEST_conclusions = ["B ⊕ A"]
```

### Test Your Changes

```bash
# Run your modified examples
model-checker examples.py

# Create new test files
model-checker test_symmetry.py
model-checker test_transitivity.py
```

Detailed development guide in [Settings](SETTINGS.md) and [Architecture](../architecture/README.md).

## Debugging When Things Go Wrong

### Common Issues and Solutions

```bash
# No model found? Check your constraints:
model-checker examples.py --print-constraints

# Timeout? Reduce complexity:
model-checker examples.py --N=3 --max-time=5

# Wrong result? Enable debug output:
model-checker examples.py --verbose --print-z3
```

### Understanding Error Messages

```python
# Formula parsing error
Error: Unknown operator '&'
Fix: Use LaTeX notation '\\wedge'

# Constraint conflict  
Error: Unsat core [...]
Fix: Check for contradictory settings

# Timeout
Error: Z3 timeout after 30s
Fix: Simplify formula or increase --max-time
```

Full debugging guide in [CONSTRAINTS.md](CONSTRAINTS.md).

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

### Saving Your Results

```bash
# Save in different formats
model-checker examples.py --save json      # For processing
model-checker examples.py --save markdown  # For documentation
model-checker examples.py --save notebook  # For Jupyter

# Results saved to output/ directory
```

See [OUTPUT.md](OUTPUT.md) for output formats and options.

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

## Next Steps

### Learn the Details

Now that you understand the workflow, explore:

1. **[EXAMPLES.md](EXAMPLES.md)** - Write logical formulas correctly
2. **[SETTINGS.md](SETTINGS.md)** - Configure ModelChecker behavior  
3. **[CONSTRAINTS.md](CONSTRAINTS.md)** - Test semantic properties
4. **[OUTPUT.md](OUTPUT.md)** - Save and format results

### Advanced Topics

- **[TOOLS.md](TOOLS.md)** - Advanced tools and theory comparison
- **[Architecture Docs](../architecture/README.md)** - How ModelChecker works internally

## Quick Reference

### Essential Commands

```bash
# Create project
model-checker                    # Interactive creation
model-checker -l exclusion       # Copy specific theory

# Run examples
model-checker examples.py        # Run tests
model-checker examples.py --N=4  # More states

# Debug
model-checker examples.py --verbose            # Show details
model-checker examples.py --print-constraints  # Show logic

# Save results  
model-checker examples.py --save json     # JSON format
model-checker examples.py --save markdown # Markdown format
```

### Common Patterns

```python
# Test if inference is valid
TEST_premises = ["A", "A → B"]
TEST_conclusions = ["B"]
# Expect: Valid (no countermodel)

# Find counterexample
INVALID_premises = ["A ∨ B"] 
INVALID_conclusions = ["A"]
# Expect: Invalid (shows countermodel)

# Test logical equivalence
EQUIV1_premises = ["A ∧ B"]
EQUIV1_conclusions = ["B ∧ A"]
# Should be valid both directions
```

### Formula Syntax

```
∧  AND         (\\wedge)
∨  OR          (\\vee)
¬  NOT         (\\neg)
→  IMPLIES     (\\rightarrow)
↔  IFF         (\\leftrightarrow)
□  NECESSARY   (\\Box)
◇  POSSIBLE    (\\Diamond)
```

Full syntax guide in [EXAMPLES.md](EXAMPLES.md).

## Summary

You've learned the ModelChecker workflow:
1. **Create** a project with your theory
2. **Run** examples to test inferences
3. **Debug** with verbose output when needed
4. **Save** results in various formats

Continue to [EXAMPLES.md](EXAMPLES.md) for writing formulas, or return to [PROJECT.md](PROJECT.md) to review project creation.

---

[← Previous: Project Setup](PROJECT.md) | [Back to Usage](README.md) | [Next: Writing Examples →](EXAMPLES.md)
