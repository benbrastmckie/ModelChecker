# Exclusion Theory Technical Reference

## Overview

This document provides complete technical reference for the exclusion theory implementation, including API documentation, implementation patterns, and usage examples. The exclusion theory implements Bernard and Champollion's unilateral semantics using the breakthrough **witness predicate architecture**.

## Core Classes and API

### WitnessSemantics

Main semantic framework that orchestrates the witness predicate system.

```python
class WitnessSemantics(SemanticDefaults):
    """Main semantics class coordinating witness predicates and model building."""
```

#### Key Methods

**`build_model() -> WitnessAwareModel`**
- Two-phase model construction with witness registration
- Phase 1: Register all witness predicates by traversing formula trees
- Phase 2: Generate Z3 constraints referencing registered predicates
- Returns extended model with witness query capabilities

**`_register_witness_predicates_recursive(formulas: List[Formula])`**
- First pass: traverse all formulas to register witnesses
- Creates Z3 Function objects for each exclusion subformula
- Ensures consistency across all constraint generation

**`_generate_all_witness_constraints(eval_point: int) -> List[z3.BoolRef]`**
- Second pass: generate three-condition semantic constraints
- References predicates registered in first pass
- Implements Bernard-Champollion formal semantics

#### Core Semantic Relations

**`excludes(state1: z3.BitVecRef, state2: z3.BitVecRef) -> z3.BoolRef`**
```python
def excludes(self, bit_e1, bit_e2):
    """Unilateral exclusion relation (asymmetric in general)."""
    return z3.Or(
        z3.And(bit_e1 == 0, bit_e2 != 0),  # Empty excludes non-empty
        z3.And(
            bit_e1 != 0, bit_e2 != 0,
            z3.And(bit_e1 & bit_e2) == 0   # Non-empty states with no overlap
        )
    )
```

**`conflicts(state1: z3.BitVecRef, state2: z3.BitVecRef) -> z3.BoolRef`**
```python
def conflicts(self, bit_e1, bit_e2):
    """Check if two states have parts that exclude each other."""
    f1, f2 = z3.BitVecs("f1 f2", self.N)
    return Exists([f1, f2], z3.And(
        self.is_part_of(f1, bit_e1),
        self.is_part_of(f2, bit_e2),
        self.excludes(f1, f2)
    ))
```

**`fusion(state1: z3.BitVecRef, state2: z3.BitVecRef) -> z3.BitVecRef`**
```python
def fusion(self, bit_e1, bit_e2):
    """Compute fusion of two states (bitwise OR)."""
    return bit_e1 | bit_e2
```

### WitnessAwareModel

Extended Z3 model that treats witness functions as queryable predicates.

```python
class WitnessAwareModel:
    """Extended model with witness predicate access."""
    
    def __init__(self, z3_model, semantics, witness_predicates):
        self.z3_model = z3_model
        self.semantics = semantics
        self.witness_predicates = witness_predicates
```

#### Key Methods

**`get_h_witness(formula_str: str, state: int) -> Optional[int]`**
```python
def get_h_witness(self, formula_str: str, state: int) -> Optional[int]:
    """Get h witness function value for formula at state."""
    h_pred = self.witness_predicates.get(f"{formula_str}_h")
    if h_pred is None:
        return None
        
    state_bv = z3.BitVecVal(state, self.semantics.N)
    result = self.eval(h_pred(state_bv))
    if z3.is_bv_value(result):
        return result.as_long()
    return None
```

**`get_y_witness(formula_str: str, state: int) -> Optional[int]`**
```python
def get_y_witness(self, formula_str: str, state: int) -> Optional[int]:
    """Get y witness function value for formula at state."""
    y_pred = self.witness_predicates.get(f"{formula_str}_y") 
    if y_pred is None:
        return None
        
    state_bv = z3.BitVecVal(state, self.semantics.N)
    result = self.eval(y_pred(state_bv))
    if z3.is_bv_value(result):
        return result.as_long()
    return None
```

**`has_witness_for(formula_str: str) -> bool`**
```python
def has_witness_for(self, formula_str: str) -> bool:
    """Check if witness predicates exist for formula."""
    return (f"{formula_str}_h" in self.witness_predicates and 
            f"{formula_str}_y" in self.witness_predicates)
```

### WitnessRegistry

Centralized registry ensuring consistency of witness predicates across phases.

```python
class WitnessRegistry:
    """Registry for witness predicate management."""
    
    def __init__(self, N: int):
        self.N = N
        self.predicates = {}
```

#### Key Methods

**`register_witness_predicates(formula_str: str) -> Tuple[z3.FuncDeclRef, z3.FuncDeclRef]`**
```python
def register_witness_predicates(self, formula_str: str):
    """Create and register h and y predicates for formula."""
    h_name = f"{formula_str}_h"
    y_name = f"{formula_str}_y"
    
    # Create Z3 functions as first-class model citizens
    h_pred = z3.Function(h_name, z3.BitVecSort(self.N), z3.BitVecSort(self.N))
    y_pred = z3.Function(y_name, z3.BitVecSort(self.N), z3.BitVecSort(self.N))
    
    self.predicates[h_name] = h_pred
    self.predicates[y_name] = y_pred
    
    return h_pred, y_pred
```

### UniNegationOperator

Core exclusion operator that queries witness predicates during verifier computation.

```python
class UniNegationOperator(Operator):
    """Unilateral negation with witness predicates."""
    
    def __init__(self):
        super().__init__("\\func_unineg", 1)
```

#### Key Methods

**`compute_verifiers(argument, model, eval_point) -> List[int]`**
```python
def compute_verifiers(self, argument, model, eval_point):
    """Compute verifiers by querying witness predicates."""
    arg_verifiers = argument.compute_verifiers(model, eval_point)
    formula_str = f"\\func_unineg({self.semantics._formula_to_string(argument)})"
    
    verifiers = []
    for state in range(2**self.semantics.N):
        if self._verifies_uninegation_with_predicates(
            state, formula_str, arg_verifiers, model
        ):
            verifiers.append(state)
    return verifiers
```

**`_verifies_uninegation_with_predicates(state, formula_str, arg_verifiers, model) -> bool`**
```python
def _verifies_uninegation_with_predicates(self, state: int, formula_str: str,
                                      arg_verifiers: List[int],
                                      model: WitnessAwareModel) -> bool:
    """Verify three-condition semantics using witness predicates."""
    # Check all three conditions for each verifier
    for v in arg_verifiers:
        h_v = model.get_h_witness(formula_str, v)
        y_v = model.get_y_witness(formula_str, v)
        
        if h_v is None or y_v is None:
            return False
            
        # Condition 1: y_v ⊑ v and h_v excludes y_v
        if not self._eval_is_part_of(y_v, v, model):
            return False
        if not self._eval_excludes(h_v, y_v, model):
            return False
        
        # Condition 2: h_v ⊑ state
        if not self._eval_is_part_of(h_v, state, model):
            return False
    
    # Condition 3: minimality
    return self._check_minimality(state, formula_str, arg_verifiers, model)
```

## Implementation Patterns

### Two-Pass Model Building Pattern

The core architectural pattern that enables witness predicate access:

```python
def build_model(self):
    # PASS 1: Register all witness predicates
    self._register_witness_predicates_recursive(self.premises)
    self._register_witness_predicates_recursive(self.conclusions)
    
    # PASS 2: Generate constraints (can safely reference any predicate)
    solver = z3.Solver()
    standard_constraints = self._generate_standard_constraints()
    witness_constraints = self._generate_all_witness_constraints()
    
    solver.add(standard_constraints)
    solver.add(witness_constraints)
    
    # Solve and wrap result
    if solver.check() == z3.sat:
        z3_model = solver.model()
        return WitnessAwareModel(z3_model, self, self.witness_registry.predicates)
    else:
        return None
```

### Registry Pattern for Consistency

Ensures witness functions remain consistent across all phases:

```python
class WitnessRegistry:
    def __init__(self, N: int):
        self.N = N
        self.predicates = {}  # Single source of truth
        
    def get_or_create_predicates(self, formula_str: str):
        """Get existing predicates or create new ones."""
        h_name = f"{formula_str}_h"
        y_name = f"{formula_str}_y"
        
        if h_name not in self.predicates:
            self.register_witness_predicates(formula_str)
            
        return self.predicates[h_name], self.predicates[y_name]
```

### Three-Condition Constraint Generation

Implementation of Bernard-Champollion semantics:

```python
def generate_witness_constraints(self, formula_str, formula_ast, h_pred, y_pred, eval_point):
    """Generate constraints implementing three-condition semantics."""
    constraints = []
    
    for state in range(2**self.N):
        state_bv = z3.BitVecVal(state, self.N)
        
        # For each potential verifier of the negation
        verifier_condition = z3.Bool(f"verifies_{formula_str}_{state}")
        
        # Condition constraints for this state
        condition_constraints = []
        
        # Get argument verifiers
        arg_verifiers = self._get_argument_verifiers(formula_ast, eval_point)
        
        for v in arg_verifiers:
            v_bv = z3.BitVecVal(v, self.N)
            
            # Condition 1: ∀x ∈ Ver(φ): y(x) ⊑ x ∧ h(x) excludes y(x)
            cond1 = z3.And(
                self.is_part_of(y_pred(v_bv), v_bv),
                self.excludes(h_pred(v_bv), y_pred(v_bv))
            )
            
            # Condition 2: ∀x ∈ Ver(φ): h(x) ⊑ s
            cond2 = self.is_part_of(h_pred(v_bv), state_bv)
            
            condition_constraints.append(z3.And(cond1, cond2))
        
        # Condition 3: s is minimal (implemented via additional constraints)
        minimality = self._minimality_constraint(state_bv, formula_str, h_pred, y_pred)
        
        # Final constraint: state verifies negation iff all conditions hold
        if condition_constraints:
            all_conditions = z3.And(*condition_constraints, minimality)
            constraints.append(verifier_condition == all_conditions)
        
    return constraints
```

## Usage Examples

### Basic Theory Setup

```python
from model_checker.theory_lib.exclusion import (
    WitnessSemantics,
    WitnessProposition,
    WitnessStructure,
    witness_operators
)

# Define exclusion theory
exclusion_theory = {
    "semantics": WitnessSemantics,
    "proposition": WitnessProposition,
    "model": WitnessStructure,
    "operators": witness_operators,
    "dictionary": {}
}
```

### Running Examples

```python
from model_checker import BuildExample

# Test double negation elimination (should find countermodel)
model = BuildExample("double_neg_test", exclusion_theory,
    premises=['\\func_unineg \\func_unineg A'],  # ¬¬A
    conclusions=['A'],                           # A
    settings={'N': 3}
)

result = model.check_formula()
print(f"¬¬A ⊨ A: {result}")  # False - countermodel found

# Access the model structure
if result is False:  # Countermodel found
    model_structure = model.get_model()
    if hasattr(model_structure, 'get_h_witness'):
        # Inspect witness functions
        h_val = model_structure.get_h_witness("\\func_unineg(\\func_unineg(A))", 1)
        y_val = model_structure.get_y_witness("\\func_unineg(\\func_unineg(A))", 1)
        print(f"Witness functions at state 1: h={h_val}, y={y_val}")
```

### Command Line Usage

```bash
# Run all exclusion theory examples
./dev_cli.py src/model_checker/theory_lib/exclusion/examples.py

# Run with detailed constraint output
./dev_cli.py -p src/model_checker/theory_lib/exclusion/examples.py

# Run with Z3 solver output
./dev_cli.py -z src/model_checker/theory_lib/exclusion/examples.py

# Run with both constraint and solver output
./dev_cli.py -p -z src/model_checker/theory_lib/exclusion/examples.py
```

### Custom Example Definition

```python
# Countermodel example - expects to find countermodel
custom_countermodel = [
    ['\\func_unineg A'],      # Premises: ¬A
    ['A'],                    # Conclusions: A
    {                         # Settings
        'N': 3,
        'contingent': True,
        'non_empty': True,
        'max_time': 10,
        'iterate': 1,
        'expectation': True   # Expect countermodel (True)
    }
]

# Theorem example - expects no countermodel (valid inference)
custom_theorem = [
    ['A'],                    # Premises: A
    ['A'],                    # Conclusions: A
    {                         # Settings
        'N': 2,
        'max_time': 5,
        'expectation': False  # Expect validity (False = no countermodel)
    }
]
```

## Available Operators

| Operator | Symbol | Syntax | Arity | Description |
|----------|---------|---------|-------|-------------|
| **Unilateral Negation** | ¬ | `\\func_unineg` | 1 | Exclusion-based negation |
| **Conjunction** | ∧ | `\\uniwedge` | 2 | Standard conjunction |
| **Disjunction** | ∨ | `\\univee` | 2 | Standard disjunction |
| **Identity** | ≡ | `\\uniequiv` | 2 | Verifier set equality |

### Operator Implementation Pattern

```python
class UniNegationOperator(Operator):
    def __init__(self):
        super().__init__("\\func_unineg", 1)
    
    def compute_verifiers(self, argument, model, eval_point):
        """Query witness predicates to determine verifiers."""
        # Get argument verifiers
        arg_verifiers = argument.compute_verifiers(model, eval_point)
        
        # Build formula string for witness lookup
        formula_str = f"\\func_unineg({self.semantics._formula_to_string(argument)})"
        
        # Check each state using witness predicates
        verifiers = []
        for state in range(2**self.semantics.N):
            if self._verifies_uninegation_with_predicates(
                state, formula_str, arg_verifiers, model
            ):
                verifiers.append(state)
        return verifiers
```

## Settings and Configuration

### Model Settings

Standard settings for exclusion theory models:

```python
settings = {
    'N': 3,                    # State space size (2^N states)
    'possible': True,          # Require some possible states
    'contingent': True,        # Allow contingent propositions
    'non_empty': True,         # Propositions must have verifiers
    'non_null': True,          # Propositions must have falsifiers
    'disjoint': False,         # Allow overlapping verifier sets
    'fusion_closure': True,    # Require fusion closure
    'max_time': 10,            # Solver timeout (seconds)
    'iterate': 1               # Number of models to find
}
```

### Performance Tuning

For different use cases:

```python
# Fast testing (small models)
fast_settings = {'N': 2, 'max_time': 5}

# Balanced (most examples)
balanced_settings = {'N': 3, 'max_time': 10}

# Complex formulas (larger state space)
complex_settings = {'N': 4, 'max_time': 30, 'iterate': 2}
```

## Test Suite Structure

The exclusion theory includes 38 comprehensive test cases:

### Countermodel Examples (22 total)
- **Frame Constraints** (EX_CM_1-3): Empty models, gaps, gluts
- **False Premise Problems** (EX_CM_4-9): Negation failures resolved by witness predicates
- **DeMorgan's Laws** (EX_CM_10-13): All four forms find countermodels
- **Identity Relations** (EX_CM_14-20): Double negation, DeMorgan identities
- **Basic Tests** (EX_CM_21-22): Simple invalidity and distribution failures

### Theorem Examples (16 total)
- **Reflexivity** (EX_TH_1): A ⊨ A
- **Logical Rules** (EX_TH_2): Disjunctive syllogism
- **Distribution Laws** (EX_TH_3-6): Conjunction/disjunction distribution
- **Absorption Laws** (EX_TH_7-10): Both directions for conjunction and disjunction
- **Associativity Laws** (EX_TH_11-14): For conjunction and disjunction
- **Complex Theorems** (EX_TH_15-16): Distribution identity and complex formulas

### Example Collection Access

```python
from model_checker.theory_lib.exclusion.examples import (
    exclusion_cm_examples,    # All countermodel examples
    exclusion_th_examples,    # All theorem examples
    unit_tests,               # Combined collection
    example_range            # Curated subset for execution
)

# Access specific examples
double_negation = unit_tests["EX_CM_6"]  # Double negation elimination
reflexivity = unit_tests["EX_TH_1"]      # Basic reflexivity

# Get example categories
examples = get_examples()
countermodels = examples['countermodels']
theorems = examples['theorems'] 
all_examples = examples['all']
```

## Performance Characteristics

### Computational Complexity
- **Constraint Generation**: O(2^N × |formulas|)
- **Witness Query**: O(1) per lookup (direct model evaluation)
- **Memory Overhead**: O(|formulas| × 2^N) for witness storage
- **Solving Time**: ~1-5 seconds for typical N=3 examples

### Benchmarks
- **Test Suite**: All 38 examples pass with 100% success rate
- **Execution Time**: Complete test suite runs in ~30-60 seconds
- **Memory Usage**: ~300KB for full theory with witness predicates
- **Scalability**: Practical up to N=4, theoretical up to N=5

### Optimization Guidelines

```python
# Optimize for speed
speed_settings = {
    'N': 2,              # Smaller state space
    'max_time': 5,       # Shorter timeout
    'iterate': 1         # Single model only
}

# Optimize for expressiveness
expressive_settings = {
    'N': 4,              # Larger state space
    'max_time': 60,      # Longer timeout
    'contingent': True,  # Allow complex propositions
    'non_empty': True    # Ensure meaningful models
}
```

## Integration with ModelChecker Framework

### Framework Compatibility

The exclusion theory fully integrates with ModelChecker patterns:

```python
class WitnessSemantics(SemanticDefaults):
    """Proper inheritance from framework base class."""
    
    def _premise_behavior_method(self, premise):
        """Framework-compatible premise handling."""
        return self.true_at(premise, self.main_point)
    
    def _conclusion_behavior_method(self, conclusion):
        """Framework-compatible conclusion handling."""
        return z3.Not(self.true_at(conclusion, self.main_point))
```

### Standard Methods

All operators implement the standard operator interface:

```python
class UniNegationOperator(Operator):
    def __init__(self):
        super().__init__("\\func_unineg", 1)  # Name and arity
    
    def compute_verifiers(self, argument, model, eval_point):
        """Standard verifier computation method."""
        # Implementation with witness predicate queries
        pass
```

### Integration Testing

```python
# Test with other theories
from model_checker.theory_lib.logos import logos_theory

# Compare results across theories
test_formula = ['\\func_unineg \\func_unineg A'], ['A']

exclusion_result = BuildExample("ex", exclusion_theory, *test_formula).check_formula()
logos_result = BuildExample("logos", logos_theory, *test_formula).check_formula()

print(f"Exclusion theory: {exclusion_result}")  # False (countermodel)
print(f"Logos theory: {logos_result}")         # True (valid)
```

## Debugging and Development

### Debug Output

Use development CLI flags for detailed analysis:

```bash
# Show generated constraints
./dev_cli.py -p examples.py

# Show Z3 solver interaction
./dev_cli.py -z examples.py

# Show both constraints and solver
./dev_cli.py -p -z examples.py
```

### Witness Function Inspection

```python
# Inspect witness functions in countermodels
if model_structure.has_witness_for("\\func_unineg(A)"):
    for state in range(8):  # For N=3
        h = model_structure.get_h_witness("\\func_unineg(A)", state)
        y = model_structure.get_y_witness("\\func_unineg(A)", state)
        if h is not None and y is not None:
            print(f"State {state}: h={h}, y={y}")
```

### Common Issues

**Issue**: "Solver timeout"
```python
# Solution: Increase timeout or reduce model size
settings = {'N': 2, 'max_time': 60}
```

**Issue**: "No witness predicates found"
```python
# Solution: Check formula string consistency
formula_str = f"\\func_unineg({self.semantics._formula_to_string(argument)})"
```

**Issue**: "Inconsistent witness values"
```python
# Solution: Verify registry pattern usage
h_pred, y_pred = self.witness_registry.get_or_create_predicates(formula_str)
```

## Advanced Features

### Model Iteration

Find multiple distinct models using the iterator:

```python
settings = {
    'N': 3,
    'iterate': 3  # Find up to 3 distinct countermodels
}

model = BuildExample("iteration_test", exclusion_theory, 
    ['\\func_unineg A'], ['A'], settings)
    
models = model.find_models()  # Returns list of distinct models
for i, model_structure in enumerate(models):
    print(f"Model {i+1}: {model_structure}")
```

### Custom Semantic Relations

Extend the semantic framework with custom relations:

```python
class CustomWitnessSemantics(WitnessSemantics):
    def custom_relation(self, state1, state2):
        """Define custom semantic relations."""
        # Custom implementation
        return z3.And(
            self.excludes(state1, state2),
            self.is_part_of(state1, self.fusion(state1, state2))
        )
```

### Theory Comparison

Compare exclusion theory with other semantic approaches:

```python
def compare_theories(premises, conclusions):
    """Compare inference across different theories."""
    theories = {
        'exclusion': exclusion_theory,
        'logos': logos_theory,
        'default': default_theory
    }
    
    results = {}
    for name, theory in theories.items():
        model = BuildExample(f"{name}_test", theory, premises, conclusions)
        results[name] = model.check_formula()
    
    return results

# Compare double negation across theories
comparison = compare_theories(['\\func_unineg \\func_unineg A'], ['A'])
print(comparison)  # Shows different results across theories
```

This technical reference provides comprehensive documentation for implementing, using, and extending the exclusion theory within the ModelChecker framework. The witness predicate architecture enables complete computational support for unilateral semantics while maintaining clean integration with existing framework patterns.