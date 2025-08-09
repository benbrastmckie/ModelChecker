# Utility Functions: Essential Tools for Model Checking

[← Back to Model Checker](../README.md) | [Models →](../models/README.md) | [Syntactic →](../syntactic.py)

## Directory Structure

```
utils/
├── README.md               # This file - comprehensive utility documentation
├── __init__.py            # Package initialization and exports
├── api.py                 # Theory and example access functions
├── bitvector.py           # Bit vector operations and conversions
├── context.py             # Z3 context management
├── formatting.py          # Output formatting and display utilities
├── parsing.py             # Expression parsing functions
├── testing.py             # Test runner utilities
├── version.py             # Version management and compatibility
├── z3_helpers.py          # Z3 constraint helpers
└── tests/                 # Comprehensive test suite
    ├── __init__.py
    ├── test_bitvector.py
    ├── test_context.py
    ├── test_parsing.py
    └── test_z3_helpers.py
```

## Overview

The **utils** package provides essential utility functions for the ModelChecker framework. These utilities handle common operations across the codebase including expression parsing, bit vector manipulation, Z3 solver management, and output formatting.

### Core Capabilities

1. **Expression Parsing**: Convert infix logical expressions to prefix notation
2. **Bit Vector Operations**: Manipulate Z3 bit vectors for state representation
3. **Z3 Context Management**: Ensure solver isolation between examples
4. **Output Formatting**: Pretty-print sets and generate error messages
5. **Version Management**: Track compatibility and generate licenses
6. **API Functions**: Access theories and examples programmatically
7. **Test Utilities**: Run model checking tests with detailed analysis

### Integration Context

The utils package serves as the foundation for many ModelChecker operations:
- **Syntactic module** uses parsing functions for formula processing
- **Semantic theories** use bit vector operations for state manipulation
- **Builder module** uses Z3 context management for solver isolation
- **Theory implementations** use formatting utilities for output
- **Test suites** use testing utilities for validation

## Module Reference

### parsing.py - Expression Parsing

Converts infix logical expressions to prefix notation for internal processing.

```python
from model_checker.utils import parse_expression, op_left_right

# Parse a simple expression
tokens = ['(', 'A', '\\wedge', 'B', ')']
prefix, complexity = parse_expression(tokens)
# Result: ['\\wedge', ['A'], ['B']], 1

# Extract operator and operands
operator, left, right = op_left_right(['\\wedge', 'A', 'B'])
# Result: '\\wedge', ['A'], ['B']
```

**Key Functions**:
- `parse_expression(tokens)`: Parse token list to prefix notation
- `op_left_right(tokens)`: Extract binary operator and operands

### bitvector.py - Bit Vector Operations

Provides conversions between integers, bit vectors, and state representations.

```python
from model_checker.utils import (
    binary_bitvector, bitvec_to_substates, bitvec_to_worldstate
)

# Create a bit vector from integer
bv = binary_bitvector(5, N=3)  # 101 in binary

# Convert to state representation
states = bitvec_to_substates(bv, N=3)
# Result: 'a.c' (states a and c are true)

# Convert to world state format
world = bitvec_to_worldstate(bv, N=3)
# Result: {'a': True, 'b': False, 'c': True}
```

**Key Functions**:
- `binary_bitvector(bit, N)`: Create N-bit vector from integer
- `int_to_binary(integer, number)`: Convert to binary string
- `index_to_substate(index)`: Map index to state letter
- `bitvec_to_substates(bit_vec, N)`: Format as dot-separated states
- `bitvec_to_worldstate(bit_vec, N)`: Convert to dictionary format

### context.py - Z3 Context Management

Ensures proper isolation between different Z3 solver instances.

```python
from model_checker.utils import Z3ContextManager

# Reset Z3 context between examples
Z3ContextManager.reset_context()

# This prevents constraint leakage between model checking runs
```

**Key Class**:
- `Z3ContextManager`: Provides centralized Z3 context management
  - `reset_context()`: Force fresh Z3 context

### formatting.py - Output Formatting

Utilities for pretty-printing and error message generation.

```python
from model_checker.utils import pretty_set_print, not_implemented_string

# Pretty print a set
result = pretty_set_print({'a', 'b', 'c'})
# Result: '{a, b, c}'

# Generate standard error message
msg = not_implemented_string('PropositionDefaults')
# Result: 'User should implement subclass(es) of PropositionDefaults...'
```

**Key Functions**:
- `pretty_set_print(set_with_strings)`: Format sets for display
- `not_implemented_string(cl_name)`: Generate NotImplementedError messages
- `flatten(structured_list)`: Recursively flatten nested lists

### version.py - Version Management

Functions for version tracking and license generation.

```python
from model_checker.utils import (
    get_model_checker_version, check_theory_compatibility
)

# Get current version
version = get_model_checker_version()
# Result: '1.0.0' or '0.0.0-dev'

# Check theory compatibility
is_compatible = check_theory_compatibility('logos')
# Result: True/False
```

**Key Functions**:
- `get_model_checker_version()`: Get package version
- `get_theory_version(theory_name)`: Get specific theory version
- `check_theory_compatibility(theory_name)`: Verify compatibility
- `get_license_template(...)`: Generate license text with inheritance

### api.py - Theory and Example Access

Programmatic access to theories and examples.

```python
from model_checker.utils import get_theory, get_example

# Load a theory
theory = get_theory('logos')
# Returns dict with semantics, proposition, model, operators

# Get specific example
example = get_example('MODAL_CM_1', example_range)
# Returns [premises, conclusions, settings]
```

**Key Functions**:
- `get_theory(name, semantic_theories=None)`: Load semantic theory
- `get_example(name, example_range)`: Retrieve specific example

### z3_helpers.py - Z3 Constraint Helpers

Quantifier functions for Z3 constraint generation.

```python
from model_checker.utils import ForAll, Exists
import z3

# Universal quantification
x = z3.BitVec('x', 4)
constraint = ForAll(x, x > 0, x < 10)

# Existential quantification
y = z3.BitVec('y', 4)
constraint = Exists(y, y == 5)
```

**Key Functions**:
- `ForAll(bvs, formula)`: Create universal quantification
- `Exists(bvs, formula)`: Create existential quantification

### testing.py - Test Runner Utilities

Functions for running model checking tests with analysis.

```python
from model_checker.utils import run_test, TestResultData

# Run basic test
result = run_test(
    example_case=[premises, conclusions, settings],
    semantic_class=LogosSemantics,
    proposition_class=LogosProposition,
    operator_collection=operator_collection,
    syntax_class=Syntax,
    model_constraints=ModelConstraints,
    model_structure=ModelDefaults
)

# Enhanced test with detailed analysis
test_data = run_enhanced_test(...)
print(f"Model found: {test_data.model_found}")
print(f"Solving time: {test_data.solving_time}")
```

**Key Functions**:
- `run_test(...)`: Run basic model checking test
- `run_enhanced_test(...)`: Run test with detailed data collection
- `run_strategy_test(...)`: Test specific exclusion strategies

**Key Classes**:
- `TestResultData`: Container for detailed test results

## Usage Patterns

### Basic Import Pattern

```python
# Import specific utilities
from model_checker.utils import (
    parse_expression, 
    bitvec_to_substates,
    pretty_set_print
)

# Or import everything
from model_checker.utils import *
```

### Common Workflows

#### Processing Logical Formulas

```python
# Tokenize and parse formula
formula = "(A \\wedge B) \\rightarrow C"
tokens = formula.replace('(', ' ( ').replace(')', ' ) ').split()
prefix_expr, complexity = parse_expression(tokens)
```

#### Working with States

```python
# Convert state index to representation
for i in range(2**N):
    bv = binary_bitvector(i, N)
    state_str = bitvec_to_substates(bv, N)
    print(f"State {i}: {state_str}")
```

#### Running Tests Programmatically

```python
# Load theory and run test
theory = get_theory('logos')
result = run_test(
    example_case,
    theory['semantics'],
    theory['proposition'],
    theory['operators'],
    Syntax,
    ModelConstraints,
    theory['model']
)
```

## Technical Implementation

### Design Decisions

1. **Modular Structure**: Utilities are organized by functionality rather than as a monolithic module
2. **No External Dependencies**: Core utilities rely only on Python stdlib and Z3
3. **Stateless Functions**: Most utilities are pure functions without side effects
4. **Consistent Interfaces**: Similar operations use similar parameter patterns

### Performance Considerations

- **Parsing**: Uses recursive descent for simplicity over speed
- **Bit Vectors**: Direct Z3 operations for efficiency
- **Context Reset**: Full Z3 reload ensures complete isolation
- **Pretty Printing**: Sorts elements for consistent output

### Error Handling

- **Parse Errors**: Raise ValueError with descriptive messages
- **Theory Not Found**: Raise ValueError or KeyError as appropriate
- **Type Errors**: Let Z3 raise its own type errors for clarity

## Extension Points

### Adding New Utilities

1. Create new module in utils/ directory
2. Implement functions following existing patterns
3. Add comprehensive tests in tests/
4. Update __init__.py exports
5. Document in this README

### Custom Formatting

Extend formatting.py for theory-specific output:

```python
def format_theory_specific(data):
    """Format theory-specific data structures."""
    # Custom formatting logic
    return formatted_string
```

### Theory Integration

When adding new theories, ensure they use utils appropriately:
- Use parsing functions for formula processing
- Use bitvector operations for state manipulation
- Use Z3 helpers for constraint generation
- Use formatting utilities for consistent output

## Testing

The utils package includes comprehensive tests:

```bash
# Run all utils tests
pytest src/model_checker/utils/tests/ -v

# Run specific module tests
pytest src/model_checker/utils/tests/test_parsing.py -v

# Run with coverage
pytest src/model_checker/utils/tests/ --cov=model_checker.utils
```

### Test Organization

- Each module has corresponding test file
- Tests cover normal cases, edge cases, and error conditions
- Mocking used where appropriate (e.g., for theory imports)
- Property-based testing for mathematical functions

## Migration History

This utils package is the result of refactoring the original monolithic utils.py (1000+ lines) into a modular structure. The migration was completed on 2025-08-09 as part of the v1.0 preparation:

1. **Phase 1**: Identified all functions and their dependencies
2. **Phase 2**: Created modular structure with focused modules
3. **Phase 3**: Migrated all imports across the codebase (34 files)
4. **Phase 4**: Renamed utils_new to utils after successful migration

All original functionality has been preserved with improved organization and maintainability.

## References

- **Z3 Documentation**: [Z3 Python API](https://z3prover.github.io/api/html/namespacez3py.html)
- **ModelChecker Architecture**: [Architecture Documentation](../../docs/ARCHITECTURE.md)
- **Theory Implementations**: [Theory Library](../theory_lib/README.md)

---

[← Back to Model Checker](../README.md) | [Models →](../models/README.md) | [Syntactic →](../syntactic.py)