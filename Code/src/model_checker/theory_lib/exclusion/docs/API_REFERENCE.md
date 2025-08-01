# API Reference: Technical Documentation for Exclusion Theory

[← Back to Documentation](README.md) | [Architecture →](ARCHITECTURE.md) | [Exclusion Theory →](../README.md)

## Directory Structure

```
docs/
├── API_REFERENCE.md   # This file - complete technical reference
├── ARCHITECTURE.md    # Architectural patterns and design decisions
├── DATA.md            # Test data analysis and performance metrics
├── ITERATE.md         # Model iteration and countermodel generation
├── README.md          # Documentation hub
├── SETTINGS.md        # Configuration and parameter guide
└── USER_GUIDE.md      # User-focused tutorial
```

## Overview

The **API Reference** provides comprehensive technical documentation for the exclusion theory implementation, covering all classes, methods, and usage patterns. This reference focuses on the witness predicate architecture that enables Bernard and Champollion's unilateral semantics through persistent Z3 functions as first-class model citizens.

Within the exclusion theory implementation, this API represents the successful resolution of the False Premise Problem through architectural innovation. The witness predicate approach transforms existentially quantified functions from ephemeral solver variables into queryable model predicates, enabling correct computation of negation verifiers across the two-phase model checking architecture.

This reference serves developers implementing or extending the exclusion theory, providing detailed specifications for all components, implementation patterns, and integration points with the ModelChecker framework.

## Core Insight

The witness predicate architecture transforms existentially quantified functions into persistent model predicates:

```python
# Core insight: witness functions as persistent predicates
from model_checker.theory_lib.exclusion import (
    WitnessSemantics,      # Two-phase model building
    WitnessAwareModel,     # Query witness predicates
    witness_operators,     # 4 operators with witness support
    exclusion_theory       # Complete theory definition
)

# Theory configuration for use with ModelChecker framework
theory = exclusion_theory

# Access witness functions in countermodels (conceptual example)
# For formula: ¬A with premise A false
if model_structure.has_witness_for("\\neg(A)"):
    h_val = model_structure.get_h_witness("\\neg(A)", state=1)
    y_val = model_structure.get_y_witness("\\neg(A)", state=1)
    print(f"Witness functions at state 1: h={h_val}, y={y_val}")

# See examples.py for complete implementation
```

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
        super().__init__("\\neg", 1)
```

#### Key Methods

**`compute_verifiers(argument, model, eval_point) -> List[int]`**
```python
def compute_verifiers(self, argument, model, eval_point):
    """Compute verifiers by querying witness predicates."""
    arg_verifiers = argument.compute_verifiers(model, eval_point)
    formula_str = f"\\neg({self.semantics._formula_to_string(argument)})"
    
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
    witness_operators,
    exclusion_theory      # Pre-configured theory
)

# Use pre-configured theory
theory = exclusion_theory

# Or define custom theory configuration
custom_theory = {
    "semantics": WitnessSemantics,
    "proposition": WitnessProposition,
    "model": WitnessStructure,
    "operators": witness_operators,
    "dictionary": {}  # Custom operator mappings
}

# See examples.py for complete usage patterns
```

### Theory Usage Patterns

```python
# Import the theory for use with ModelChecker framework
from model_checker.theory_lib.exclusion import exclusion_theory

# Conceptual example: Double negation elimination
# Formula: ¬¬A ⊢ A (should find countermodel)
premises = ['\\neg \\neg A']    # ¬¬A
conclusions = ['A']            # A  
settings = {'N': 3}            # 8-state model

# Witness function inspection (in countermodels)
# For negation formulas like ¬¬A:
formula_str = "\\neg(\\neg(A))"
if model_structure.has_witness_for(formula_str):
    # Query witness predicates
    h_val = model_structure.get_h_witness(formula_str, state=1)
    y_val = model_structure.get_y_witness(formula_str, state=1)
    print(f"State 1 witnesses: h={h_val}, y={y_val}")

# See examples.py for complete working implementations
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

### Example Configuration Patterns

```python
# Countermodel configuration - expects to find countermodel
countermodel_config = {
    'premises': ['\\neg A'],      # ¬A
    'conclusions': ['A'],         # A
    'settings': {
        'N': 3,                   # 8-state model
        'contingent': True,       # Allow contingent propositions  
        'non_empty': True,        # Require verifiers
        'max_time': 10,           # Solver timeout
        'iterate': 1,             # Find one model
        'expectation': True       # Expect countermodel
    }
}

# Theorem configuration - expects validity (no countermodel)
theorem_config = {
    'premises': ['A'],            # A
    'conclusions': ['A'],         # A  
    'settings': {
        'N': 2,                   # 4-state model
        'max_time': 5,            # Quick timeout
        'expectation': False      # Expect validity
    }
}

# See examples.py for complete test suite with all 38 examples
```

## Available Operators

| Operator | Symbol | Syntax | Arity | Description |
|----------|---------|---------|-------|-------------|
| **Unilateral Negation** | ¬ | `\\neg` | 1 | Exclusion-based negation |
| **Conjunction** | ∧ | `\\wedge` | 2 | Standard conjunction |
| **Disjunction** | ∨ | `\\vee` | 2 | Standard disjunction |
| **Identity** | ≡ | `\\equiv` | 2 | Verifier set equality |

### Operator Implementation Pattern

```python
class UniNegationOperator(Operator):
    def __init__(self):
        super().__init__("\\neg", 1)
    
    def compute_verifiers(self, argument, model, eval_point):
        """Query witness predicates to determine verifiers."""
        # Get argument verifiers
        arg_verifiers = argument.compute_verifiers(model, eval_point)
        
        # Build formula string for witness lookup
        formula_str = f"\\neg({self.semantics._formula_to_string(argument)})"
        
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
        super().__init__("\\neg", 1)  # Name and arity
    
    def compute_verifiers(self, argument, model, eval_point):
        """Standard verifier computation method."""
        # Implementation with witness predicate queries
        pass
```

### Framework Integration

```python
# Integration with ModelChecker framework
from model_checker.theory_lib.exclusion import exclusion_theory
from model_checker.theory_lib.logos import logos_theory

# Theory comparison configuration
test_case = {
    'premises': ['\\neg \\neg A'],    # ¬¬A
    'conclusions': ['A'],            # A
    'settings': {'N': 3}
}

# Expected behavioral differences:
expected_results = {
    'exclusion': False,              # Finds countermodel (non-classical)
    'logos': True,                   # Validates inference (classical-like)
}

# The exclusion theory's witness predicates enable:
# - Non-classical negation behavior
# - Resolution of False Premise Problem
# - Queryable witness functions in countermodels

# See examples.py for complete framework integration patterns
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
if model_structure.has_witness_for("\\neg(A)"):
    for state in range(8):  # For N=3
        h = model_structure.get_h_witness("\\neg(A)", state)
        y = model_structure.get_y_witness("\\neg(A)", state)
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
formula_str = f"\\neg({self.semantics._formula_to_string(argument)})"
```

**Issue**: "Inconsistent witness values"
```python
# Solution: Verify registry pattern usage
h_pred, y_pred = self.witness_registry.get_or_create_predicates(formula_str)
```

## Advanced Features

### Model Iteration Configuration

Configuration for finding multiple distinct models:

```python
# Multiple model configuration
iteration_settings = {
    'N': 3,                      # 8-state models
    'iterate': 3,                # Find up to 3 distinct countermodels
    'max_time': 30               # Extended timeout for multiple models
}

# Example configuration for iteration
test_case = {
    'premises': ['\\neg A'],      # ¬A
    'conclusions': ['A'],         # A
    'settings': iteration_settings
}

# Model analysis pattern (conceptual)
# Each model would have distinct witness function values
for model_index in range(iteration_count):
    # Access witness functions in each countermodel
    if model_structure.has_witness_for("\\neg(A)"):
        h_val = model_structure.get_h_witness("\\neg(A)", state=1)
        print(f"Model {model_index}: h(1) = {h_val}")

# See examples.py for complete implementation patterns
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

### Theory Comparison Framework

Configuration for comparing semantic approaches:

```python
# Theory comparison configuration
from model_checker.theory_lib.exclusion import exclusion_theory
from model_checker.theory_lib.logos import logos_theory

# Test case for comparison
test_formula = {
    'premises': ['\\neg \\neg A'],    # ¬¬A
    'conclusions': ['A'],            # A
    'settings': {'N': 3, 'max_time': 10}
}

# Expected results for double negation elimination:
# - Exclusion theory: False (finds countermodel)
# - Logos theory: True (validates inference)
# - Classical theory: True (validates inference)

theory_configurations = {
    'exclusion': exclusion_theory,
    'logos': logos_theory,
    # Add other theories as needed
}

# Analysis would show different logical behaviors:
# - Exclusion: Non-classical negation with witness predicates
# - Logos: Classical behavior with hyperintensional operators

# See examples.py for complete test implementations
```

## Documentation

### For API Users

- **[Core Classes](#core-classes-and-api)** - WitnessSemantics, WitnessAwareModel, WitnessRegistry
- **[Operator Reference](#available-operators)** - All 4 operators with witness support
- **[Usage Examples](#usage-examples)** - Complete code examples

### For Framework Developers

- **[Implementation Patterns](#implementation-patterns)** - Two-pass building, registry pattern
- **[Integration Points](#integration-with-modelchecker-framework)** - Framework compatibility
- **[Performance Tuning](#performance-characteristics)** - Optimization strategies

### For Theory Researchers

- **[Semantic Relations](#core-semantic-relations)** - Exclusion, conflicts, fusion
- **[Three-Condition Semantics](#three-condition-constraint-generation)** - Bernard-Champollion implementation
- **[Theory Comparison](#theory-comparison)** - Cross-theory validation

## Available Operators

The exclusion theory implements 4 operators, all with witness predicate support:

| Operator | Symbol | Syntax | Arity | Type | Description |
|----------|---------|---------|-------|------|-------------|  
| **Unilateral Negation** | ¬ | `\\neg` | 1 | Primitive | Exclusion-based negation with witness predicates |
| **Conjunction** | ∧ | `\\wedge` | 2 | Primitive | Standard conjunction using verifier products |
| **Disjunction** | ∨ | `\\vee` | 2 | Primitive | Standard disjunction using verifier union |
| **Identity** | ≡ | `\\equiv` | 2 | Primitive | Verifier set equality check |

### UniNegationOperator

**Symbol**: `\\neg` (displayed as ¬)
**Arity**: 1
**Type**: Primitive operator with witness predicates

**Truth Conditions**: A state s verifies ¬A iff there exist witness functions h, y such that:
1. For all verifiers x of A: y(x) ⊑ x and h(x) excludes y(x)
2. For all verifiers x of A: h(x) ⊑ s
3. s is minimal satisfying conditions 1-2

**Implementation**:
```python
def compute_verifiers(self, argument, model, eval_point):
    """Query witness predicates to determine verifiers."""
    arg_verifiers = argument.compute_verifiers(model, eval_point)
    formula_str = f"\\neg({self.semantics._formula_to_string(argument)})"
    
    verifiers = []
    for state in range(2**self.semantics.N):
        if self._verifies_uninegation_with_predicates(
            state, formula_str, arg_verifiers, model
        ):
            verifiers.append(state)
    return verifiers
```

### UniConjunctionOperator

**Symbol**: `\\wedge` (displayed as ∧)
**Arity**: 2
**Type**: Primitive operator

**Truth Conditions**: A state s verifies A ∧ B iff s is the fusion of some verifier of A and some verifier of B

**Implementation**: Standard product of verifier sets with fusion operation

### UniDisjunctionOperator

**Symbol**: `\\vee` (displayed as ∨)
**Arity**: 2  
**Type**: Primitive operator

**Truth Conditions**: A state s verifies A ∨ B iff s verifies A or s verifies B

**Implementation**: Union of verifier sets

### UniIdentityOperator

**Symbol**: `\\equiv` (displayed as ≡)
**Arity**: 2
**Type**: Primitive operator

**Truth Conditions**: Identity holds at all states when A and B have exactly the same verifiers

**Implementation**: Verifier set equality check

## Examples

The exclusion theory includes 38 comprehensive test examples:

### Countermodel Examples (22 total)

**Frame Constraints** (EX_CM_1-3)
- Empty models, gaps, gluts testing

**False Premise Problems** (EX_CM_4-9)  
- All resolved by witness predicates:
  - `EX_CM_4`: ¬A ⊢ A (negation to sentence)
  - `EX_CM_6`: ¬¬A ⊢ A (double negation elimination)
  - `EX_CM_8`: ¬¬¬A ⊢ ¬A (triple negation)

**DeMorgan's Laws** (EX_CM_10-13)
- All four forms correctly find countermodels

**Identity Relations** (EX_CM_14-20)
- Double negation, DeMorgan identities

### Theorem Examples (16 total)

**Core Validities** (EX_TH_1-2)
- Reflexivity: A ⊨ A
- Disjunctive syllogism

**Distribution Laws** (EX_TH_3-6)
- Conjunction/disjunction distribution both directions

**Absorption Laws** (EX_TH_7-10)
- Both conjunction and disjunction forms

**Associativity Laws** (EX_TH_11-14)
- Full associativity for conjunction/disjunction

## References

### Implementation Details

- **[Semantic Module](../semantic.py)** - WitnessSemantics implementation
- **[Operators Module](../operators.py)** - All 4 operator implementations
- **[Examples Module](../examples.py)** - Complete test suite

### Related Documentation

- **[Architecture Guide](ARCHITECTURE.md)** - Design patterns and decisions
- **[User Guide](USER_GUIDE.md)** - Tutorial and walkthrough
- **[History](../history/)** - Development journey and lessons learned

---

[← Back to Documentation](README.md) | [Architecture →](ARCHITECTURE.md) | [Exclusion Theory →](../README.md)
