# Research Report: Task #6

**Task**: Create model-checker researcher skill
**Date**: 2026-01-11
**Focus**: Model-checker usage patterns for skill creation

## Summary

Research completed on ModelChecker usage patterns to inform the creation of a comprehensive skill for researchers. The framework provides a modular semantic theory system using Z3 SMT solver with 4 theories (logos, exclusion, imposition, bimodal) and 25+ operators. Key workflows include: defining operators, adjusting frame constraints, creating examples, running tests, and reporting findings.

## Findings

### 1. Architecture Overview

The ModelChecker follows a **three-layer architecture**:

1. **User Interface Layer**: `BuildExample`, `BuildModule`, Jupyter widgets
2. **Coordination Layer**: Model construction, constraint generation, result processing
3. **Theory Implementation Layer**: Semantic classes, operators, and constraint definitions

**Core Components**:
- `theory_lib/` - Contains all semantic theories (logos, exclusion, imposition, bimodal)
- `builder/` - Model construction and example execution
- `iterate/` - Model iteration and constraint generation
- `settings/` - Centralized configuration management
- `syntactic/` - Formula parsing and operator registry

### 2. Theory Structure Pattern

Each theory follows a standardized structure:
```
theory_lib/{theory}/
├── __init__.py          # Public API (get_theory, get_examples)
├── semantic.py          # Core semantic framework extending SemanticDefaults
├── operators.py         # Operator registry and loading
├── examples.py          # Test cases with countermodels and theorems
├── iterate.py           # Theory-specific iteration support
└── tests/
    ├── unit/           # Unit tests for semantic methods
    └── integration/    # Integration tests for examples
```

### 3. Operator Definition Pattern

Operators extend `syntactic.Operator` or `syntactic.DefinedOperator` and implement:

```python
class MyOperator(syntactic.Operator):
    name = "\\myop"      # LaTeX-style name
    arity = 2            # Number of arguments

    def true_at(self, *args, eval_point):
        """Truth conditions at evaluation point."""

    def false_at(self, *args, eval_point):
        """Falsity conditions at evaluation point."""

    def extended_verify(self, state, *args, eval_point):
        """Hyperintensional verification conditions."""

    def extended_falsify(self, state, *args, eval_point):
        """Hyperintensional falsification conditions."""

    def find_verifiers_and_falsifiers(self, *args, eval_point):
        """Compute proposition (verifier/falsifier sets)."""

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Output formatting."""
```

**Key methods inherited from semantics**:
- `self.semantics.true_at(sentence, eval_point)` - Evaluate truth recursively
- `self.semantics.false_at(sentence, eval_point)` - Evaluate falsity recursively
- `self.semantics.fusion(x, y)` - State fusion (bitwise OR)
- `self.semantics.is_part_of(x, y)` - Parthood relation
- `self.semantics.possible(state)` - Possibility predicate
- `self.semantics.is_world(state)` - World predicate

### 4. Frame Constraints Pattern

Frame constraints are defined in `SemanticDefaults` subclasses:

```python
class MySemantics(SemanticDefaults):
    def __init__(self, combined_settings=None, **kwargs):
        super().__init__(combined_settings)

        # Define Z3 primitives
        self.verify = z3.Function("verify", z3.BitVecSort(self.N),
                                   syntactic.AtomSort, z3.BoolSort())
        self.falsify = z3.Function("falsify", z3.BitVecSort(self.N),
                                    syntactic.AtomSort, z3.BoolSort())
        self.possible = z3.Function("possible", z3.BitVecSort(self.N),
                                     z3.BoolSort())

        # Main evaluation point
        self.main_world = z3.BitVec("w", self.N)
        self.main_point = {"world": self.main_world}

        # Frame constraints
        x, y = z3.BitVecs("frame_x frame_y", self.N)
        possibility_downward_closure = ForAll([x, y], z3.Implies(
            z3.And(self.possible(y), self.is_part_of(x, y)),
            self.possible(x)
        ))

        self.frame_constraints = [
            possibility_downward_closure,
            self.is_world(self.main_world),
        ]

        # Validity conditions
        self.premise_behavior = lambda p: self.true_at(p, self.main_point)
        self.conclusion_behavior = lambda c: self.false_at(c, self.main_point)
```

### 5. Example Definition Pattern

Examples follow a structured format in `examples.py`:

```python
# Example naming: {SUBTHEORY}_{TYPE}_{NUMBER}
# Types: CM (countermodel), TH (theorem)

EXT_TH_1_premises = ['A', '(A \\rightarrow B)']
EXT_TH_1_conclusions = ['B']
EXT_TH_1_settings = {
    'N': 3,                    # State space size (2^N states)
    'contingent': False,       # Force contingent propositions
    'non_null': True,         # Exclude null state verifiers
    'non_empty': True,        # Require non-empty verifier sets
    'disjoint': False,        # Allow verifier/falsifier overlap
    'max_time': 1,            # Solver timeout (seconds)
    'iterate': 1,             # Number of models to find
    'expectation': False,     # False=theorem (no countermodel expected)
}
EXT_TH_1_example = [
    EXT_TH_1_premises,
    EXT_TH_1_conclusions,
    EXT_TH_1_settings,
]

# Organize into collections
countermodel_examples = {"EXT_CM_1": ..., "EXT_CM_2": ...}
theorem_examples = {"EXT_TH_1": ..., "EXT_TH_2": ...}
unit_tests = {**countermodel_examples, **theorem_examples}
example_range = {"EXT_TH_1": EXT_TH_1_example}  # Active examples
```

### 6. Testing Workflow

**Commands**:
```bash
# Run all tests
PYTHONPATH=Code/src pytest Code/tests/ -v

# Run specific theory tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/logos/tests/ -v
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/exclusion/tests/unit/ -v

# Development CLI
cd Code && ./dev_cli.py examples/my_example.py

# Run model checker directly
model-checker examples.py              # Basic
model-checker examples.py --maximize   # Compare theories
model-checker examples.py --save       # Export results
```

**TDD Workflow** (mandatory):
1. RED: Write failing test first
2. GREEN: Write minimal code to pass
3. REFACTOR: Improve while tests pass

### 7. Settings System

Settings cascade with theory-specific defaults:

```python
DEFAULT_EXAMPLE_SETTINGS = {
    'N': 16,                 # State space size
    'contingent': True,      # Require contingent propositions
    'non_empty': True,       # Non-empty verifier/falsifier sets
    'non_null': True,        # No null state verifiers
    'disjoint': True,        # Disjoint verifier/falsifier sets
    'max_time': 10,          # Solver timeout
    'iterate': False,        # Multi-model iteration
    'expectation': None,     # Expected result (True=countermodel, False=theorem)
}

DEFAULT_GENERAL_SETTINGS = {
    "print_impossible": False,
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
    "sequential": False,
    "maximize": False
}
```

### 8. Subtheory System (Logos)

Logos uses a modular subtheory system with dependency management:

```python
class LogosOperatorRegistry:
    dependencies = {
        'modal': ['extensional', 'counterfactual'],
        'counterfactual': ['extensional'],
        'constitutive': [],
        'relevance': ['constitutive'],
        'extensional': []
    }

    def load_subtheories(self, names):
        """Load subtheories with automatic dependency resolution."""
```

**Available Subtheories**:
- `extensional`: Negation, conjunction, disjunction, conditional, biconditional, top, bottom
- `modal`: Necessity, possibility, counterfactual necessity/possibility
- `constitutive`: Ground, essence, identity operators
- `counterfactual`: Would/might counterfactual conditionals
- `relevance`: Content-sensitive relevance operators

### 9. Key Z3 Patterns

```python
# BitVector states
x = z3.BitVec("x", self.N)
state = z3.BitVecVal(5, self.N)  # Concrete state

# Quantifiers (from model_checker.utils)
from model_checker.utils import ForAll, Exists
constraint = ForAll(x, z3.Implies(self.possible(x), condition(x)))
constraint = Exists(x, z3.And(self.possible(x), self.verify(x, atom)))

# Functions
self.verify = z3.Function("verify", z3.BitVecSort(N), AtomSort, z3.BoolSort())

# Constraint checking
solver = z3.Solver()
solver.add(constraints)
if solver.check() == z3.sat:
    model = solver.model()
    value = model.evaluate(expression)
```

## Recommendations

### Skill Structure

The skill should support these workflows:

1. **Define New Operator** (`/mc-operator`)
   - Generate operator class skeleton
   - Implement semantic methods
   - Add to registry
   - Create test examples

2. **Adjust Frame Constraints** (`/mc-frame`)
   - Modify semantic class
   - Add/remove constraints
   - Test constraint effects

3. **Create Examples** (`/mc-example`)
   - Define premises/conclusions
   - Configure settings
   - Set expectations
   - Run and validate

4. **Run Tests** (`/mc-test`)
   - Execute theory tests
   - Generate coverage reports
   - Validate examples

5. **Report Findings** (`/mc-report`)
   - Document logical results
   - Compare theories
   - Export model data

### Skill Features

1. **Formula Syntax Help**: LaTeX operator reference
2. **Settings Guide**: What each setting does
3. **Example Templates**: Standard patterns for countermodels/theorems
4. **Theory Comparison**: Run same formula across theories
5. **Result Interpretation**: Explain countermodel structure

### Implementation Considerations

1. **Context Loading**: Skill needs access to theory structure
2. **File Generation**: Templates for operators, examples, tests
3. **Test Integration**: Automated test execution
4. **Error Handling**: Clear messages for common issues
5. **Documentation Links**: Cross-references to theory docs

## References

- Code/src/model_checker/README.md - API documentation
- Code/docs/core/ARCHITECTURE.md - Architecture guide
- Code/docs/core/TESTING_GUIDE.md - Testing standards
- theory_lib/logos/semantic.py - Semantic implementation
- theory_lib/logos/operators.py - Operator registry
- theory_lib/logos/subtheories/*/operators.py - Operator definitions
- theory_lib/logos/subtheories/*/examples.py - Example patterns

## Next Steps

1. Create skill prompt structure with workflow commands
2. Define templates for operator/example generation
3. Implement test execution integration
4. Add theory comparison workflow
5. Create result reporting format
