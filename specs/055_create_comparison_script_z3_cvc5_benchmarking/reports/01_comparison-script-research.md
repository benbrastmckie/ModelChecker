# Task 55: Research Report - Z3 vs CVC5 Comparison Script

## Executive Summary

This report documents the infrastructure for creating a `comparison.py` script that benchmarks z3 vs cvc5 solvers using the logos theory examples. The existing codebase provides comprehensive support for this task through:

1. A well-organized example registry (`all_subtheory_examples`)
2. A proven solver-switching mechanism in `test_solver_comparison.py`
3. Clear APIs for running examples and extracting timing data

## 1. Examples Infrastructure

### 1.1 Main Entry Point

Location: `code/src/model_checker/theory_lib/logos/examples.py`

The examples module aggregates examples from all logos subtheories into unified dictionaries:

```python
# For testing frameworks that need full access to all examples
all_subtheory_examples = {
    'extensional': extensional_all_examples,
    'modal': modal_all_examples,
    'constitutive': constitutive_all_examples,
    'counterfactual': counterfactual_all_examples,
    'relevance': relevance_all_examples,
    'first_order': first_order_all_examples,
}
```

### 1.2 Example Structure

Each example is a list with three elements:

```python
example = [
    premises,      # List of LaTeX strings, e.g., ['\\Box A']
    conclusions,   # List of LaTeX strings, e.g., ['\\Diamond A']
    settings,      # Dict with N, contingent, max_time, expectation, etc.
]
```

Key settings fields:
- `N`: Number of world states (2-4 typically)
- `max_time`: Timeout in seconds
- `expectation`: `True` = expect countermodel (SAT), `False` = expect theorem (UNSAT)
- `contingent`, `non_null`, `non_empty`, `disjoint`: Constraint flags

### 1.3 Subtheory Example Counts

Based on the `unit_tests` dictionaries in each subtheory:

| Subtheory | Example Count | Prefix |
|-----------|---------------|--------|
| extensional | ~15 | EXT_ |
| modal | ~25 | MOD_ |
| constitutive | ~12 | CL_/CON_ |
| counterfactual | ~10 | CF_ |
| relevance | ~8 | REL_ |
| first_order | ~12 | FO_ |

## 2. Solver Switching Mechanism

### 2.1 Core Components

From `code/src/model_checker/solver/registry.py`:

```python
from model_checker.solver import detect_cvc5, detect_z3
from model_checker.solver.registry import set_cli_backend, clear_cli_backend, reset_registry
from model_checker import z3_shim
```

### 2.2 Switch Function

From `test_solver_comparison.py`:

```python
def switch_solver(backend: str) -> None:
    """Switch to specified solver backend with full cache invalidation."""
    # Clear CLI backend first
    clear_cli_backend()
    # Reset registry caches
    reset_registry()
    # Reset z3_shim cached module
    z3_shim._reset_backend()
    # Set new backend
    set_cli_backend(backend)
```

**Critical**: All three reset steps are required for clean solver switching.

### 2.3 Theory Loading

```python
from model_checker.theory_lib.logos import get_theory

# Subtheory dependencies
subtheory_deps = {
    'extensional': ['extensional'],
    'modal': ['extensional', 'modal', 'first_order'],
    'constitutive': ['extensional', 'modal', 'constitutive'],
    'counterfactual': ['extensional', 'modal', 'counterfactual'],
    'relevance': ['extensional', 'modal', 'constitutive', 'relevance'],
    'first_order': ['extensional', 'constitutive', 'first_order'],
}

theory = get_theory(subtheory_deps[subtheory])
```

## 3. Running Examples Programmatically

### 3.1 BuildExample API

From `code/src/model_checker/builder/example.py`:

```python
from model_checker.builder.example import BuildExample
from types import SimpleNamespace
from unittest.mock import Mock

def create_test_module(theory):
    """Create a mock build module for testing."""
    mock_module = Mock()
    mock_module.semantic_theories = {"logos": theory}

    general_settings = {
        'N': 2,
        'contingent': False,
        'disjoint': False,
        'non_empty': True,
        'non_null': True,
        'print_constraints': False,
        'save_output': False,
        'print_impossible': False,
        'print_z3': False,
        'max_time': 5
    }
    mock_module.general_settings = general_settings
    mock_module.raw_general_settings = general_settings
    mock_module.module_flags = SimpleNamespace(
        contingent=False, disjoint=False, non_empty=False,
        non_null=False, print_constraints=False, save_output=False,
        print_impossible=False, print_z3=False, maximize=False
    )
    return mock_module

# Run example
mock_module = create_test_module(theory)
example = BuildExample(mock_module, theory, example_case)
```

### 3.2 Extracting Results

```python
# Check if countermodel found (SAT)
result = bool(example.model_structure.z3_model_status)

# Get solver runtime
runtime = example.model_structure.z3_model_runtime

# Result interpretation:
# - z3_model_status = True/truthy -> SAT (countermodel found)
# - z3_model_status = False/None -> UNSAT (no countermodel, theorem)
```

### 3.3 Timing Pattern

From `test_solver_comparison.py`:

```python
import time

start_time = time.perf_counter()
try:
    mock_module = create_test_module(theory)
    example = BuildExample(mock_module, theory, example_case)
    result = bool(example.model_structure.z3_model_status)
    error = None
except Exception as e:
    error = str(e)
    result = None
elapsed = time.perf_counter() - start_time
```

## 4. Proposed JSON Output Schema

```json
{
  "metadata": {
    "timestamp": "2026-03-30T12:00:00Z",
    "z3_version": "4.12.2",
    "cvc5_version": "1.0.8",
    "platform": "linux",
    "total_examples": 82,
    "total_runtime_seconds": 45.23
  },
  "summary": {
    "z3": {
      "total_examples": 82,
      "passed": 80,
      "failed": 2,
      "errors": 0,
      "total_time_seconds": 22.5,
      "avg_time_seconds": 0.274
    },
    "cvc5": {
      "total_examples": 82,
      "passed": 78,
      "failed": 2,
      "errors": 2,
      "total_time_seconds": 22.7,
      "avg_time_seconds": 0.277
    }
  },
  "by_subtheory": {
    "extensional": {
      "z3": {"passed": 15, "failed": 0, "time": 2.1},
      "cvc5": {"passed": 15, "failed": 0, "time": 2.3}
    }
  },
  "results": [
    {
      "subtheory": "modal",
      "example_name": "MOD_TH_1",
      "expectation": false,
      "z3": {
        "result": false,
        "passed": true,
        "time_seconds": 0.045,
        "error": null
      },
      "cvc5": {
        "result": false,
        "passed": true,
        "time_seconds": 0.052,
        "error": null
      }
    }
  ],
  "disagreements": [
    {
      "example_name": "MOD_COMP_1",
      "subtheory": "modal",
      "z3_result": false,
      "cvc5_result": true,
      "expectation": false
    }
  ]
}
```

## 5. Implementation Approach

### 5.1 Recommended Script Structure

```python
#!/usr/bin/env python3
"""comparison.py - Benchmark z3 vs cvc5 on logos theory examples."""

import json
import time
from datetime import datetime
from dataclasses import dataclass, asdict
from typing import Dict, List, Optional, Any

from model_checker.solver import detect_cvc5, detect_z3
from model_checker.solver.registry import set_cli_backend, clear_cli_backend, reset_registry
from model_checker import z3_shim
from model_checker.theory_lib.logos import get_theory
from model_checker.theory_lib.logos.examples import all_subtheory_examples
from model_checker.builder.example import BuildExample

# ... switch_solver, create_test_module, get_required_subtheories ...

def main():
    # 1. Check solver availability
    if not detect_cvc5():
        print("Error: cvc5 not installed")
        return 1

    # 2. Collect all examples
    examples = flatten_examples()  # -> List[(subtheory, name, example)]

    # 3. Run each example with both solvers
    results = []
    for subtheory, name, example_case in examples:
        result = {"subtheory": subtheory, "example_name": name}

        for solver in ['z3', 'cvc5']:
            switch_solver(solver)
            theory = get_theory(get_required_subtheories(subtheory))
            passed, elapsed, error = run_example_with_timing(example_case, theory)
            result[solver] = {"passed": passed, "time": elapsed, "error": error}

        results.append(result)

    # 4. Write output.json
    output = build_output_structure(results)
    with open("output.json", "w") as f:
        json.dump(output, f, indent=2)

if __name__ == "__main__":
    main()
```

### 5.2 Key Design Decisions

1. **Sequential execution**: Run each example against both solvers before moving to the next (allows side-by-side comparison and early disagreement detection)

2. **Full cache invalidation**: Use the three-step reset before each solver switch

3. **Error isolation**: Catch exceptions per-example to continue benchmarking even if some examples fail

4. **Dual timing**: Use both `time.perf_counter()` (wall clock) and `z3_model_runtime` (solver-reported)

5. **Disagreement tracking**: Flag examples where solvers disagree on SAT/UNSAT

### 5.3 Script Location

Recommended: `code/src/model_checker/theory_lib/logos/comparison.py`

This keeps it alongside the existing test infrastructure and examples.

## 6. Import Path Reference

```python
# Solver infrastructure
from model_checker.solver import detect_cvc5, detect_z3, get_active_backend
from model_checker.solver.registry import (
    set_cli_backend,
    clear_cli_backend,
    reset_registry
)
from model_checker import z3_shim

# Theory and examples
from model_checker.theory_lib.logos import get_theory
from model_checker.theory_lib.logos.examples import all_subtheory_examples

# Building examples
from model_checker.builder.example import BuildExample
```

## 7. Testing Notes

### 7.1 Verify Solver Availability

```python
from model_checker.solver import detect_z3, detect_cvc5

assert detect_z3(), "z3 required"
assert detect_cvc5(), "cvc5 required for comparison"
```

### 7.2 Known Differences

The `MOD_COMP_*` examples (modal compositionality tests from Task 42) may show differences between solvers due to different handling of quantifier instantiation strategies.

### 7.3 Timeout Handling

Examples with `max_time` setting will timeout at that threshold. The script should track timeouts separately from errors.

## 8. File Paths Summary

| File | Purpose |
|------|---------|
| `code/src/model_checker/theory_lib/logos/examples.py` | Example registry |
| `code/src/model_checker/theory_lib/logos/tests/integration/test_solver_comparison.py` | Reference implementation |
| `code/src/model_checker/solver/registry.py` | Solver switching API |
| `code/src/model_checker/z3_shim.py` | Backend module caching |
| `code/src/model_checker/builder/example.py` | BuildExample class |
| `code/src/model_checker/theory_lib/logos/__init__.py` | get_theory() function |
