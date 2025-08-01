# Architecture: Design and Implementation of Imposition Theory

[← Back to Documentation](README.md) | [API Reference →](API_REFERENCE.md) | [Imposition Theory →](../README.md)

## Directory Structure

```
docs/
├── API_REFERENCE.md   # Complete technical reference
├── ARCHITECTURE.md    # This file - design and implementation
├── ITERATE.md         # Model iteration for counterfactuals
├── README.md          # Documentation hub
├── SETTINGS.md        # Configuration parameters
└── USER_GUIDE.md      # Tutorial and introduction
```

## Overview

The **Architecture** document describes the design and implementation of Kit Fine's counterfactual semantics within the ModelChecker framework. The imposition theory extends the Logos hyperintensional foundation with the imposition operation, enabling sophisticated counterfactual reasoning without possible worlds.

Within the imposition theory framework, this architecture implements Fine's innovative approach where counterfactuals are evaluated through state imposition rather than world accessibility. The design emphasizes modularity, reusing Logos components while adding imposition-specific operators and semantics.

This document serves developers implementing or extending counterfactual theories, providing detailed architectural patterns and design decisions.

## Architecture Overview

The imposition theory extends Logos hyperintensional semantics:

```python
# Architecture in action
from model_checker.theory_lib.imposition import ImpositionSemantics

# Core semantic framework extends Logos
class ImpositionSemantics(LogosSemantics):
    def __init__(self, settings):
        super().__init__(settings)
        # Add imposition-specific Z3 function
        self.imposition = z3.Function(
            'imposition',
            z3.BitVecSort(self.N),  # state
            z3.BitVecSort(self.N),  # world
            z3.BitVecSort(self.N),  # outcome
            z3.BoolSort()           # holds?
        )
    
    def is_alternative(self, outcome, state, eval_point):
        """Core semantic calculation for counterfactuals."""
        return self.imposition(state, eval_point['world'], outcome)

# Modular operator design
from model_checker.theory_lib.imposition import imposition_operators
operators = imposition_operators.get_all_operators()  # 11 total
```

## Core Components

### Theory Structure

```
imposition/
├── __init__.py          # Public API and theory configuration
├── semantic.py          # ImpositionSemantics implementation
├── operators.py         # Operator collection with imposition-specific operators
├── examples.py          # Comprehensive example collection
├── iterate.py           # Model iteration support
├── docs/               # Documentation (this file and others)
├── tests/              # Unit and integration tests
└── notebooks/          # Interactive tutorials
```

### Class Hierarchy

```python
# Core semantic framework
ImpositionSemantics(SemanticDefaults)
├── Inherits base truthmaker semantics
├── Adds imposition-specific evaluation methods
└── Configures Fine's semantic rules

# Reused components from Logos theory
LogosProposition as Proposition
LogosModelStructure as ModelStructure

# Operator collection
imposition_operators: OperatorCollection
├── Extensional operators (¬, ∧, ∨, →, ↔)
├── Imposition operators (↪, ⟂)
└── Extremal operators (⊤, ⊥)
```

## Semantic Framework

### Fine's Imposition Semantics

The theory implements Fine's approach to counterfactuals without possible worlds:

#### States and Propositions
```python
class ImpositionSemantics(SemanticDefaults):
    """Implements Fine's state-based semantics for counterfactuals."""
    
    def __init__(self, settings):
        super().__init__(settings)
        # Configure for imposition semantics
        self.frame_constraints = self._setup_imposition_constraints()
    
    def imposition_operation(self, state, antecedent):
        """Implement Fine's imposition operation."""
        # Minimal change to state that makes antecedent true
        return self._minimal_change(state, antecedent)
```

#### Key Semantic Operations

1. **State Verification**: `verify(state, formula)`
   - Determines when a state verifies a formula
   - Uses Fine's truthmaker semantics

2. **State Falsification**: `falsify(state, formula)`  
   - Determines when a state falsifies a formula
   - Bilateral approach to truth conditions

3. **Imposition**: `impose(state, antecedent)`
   - Core operation for counterfactual evaluation
   - Finds minimal modification of state to satisfy antecedent

4. **Possibility**: `possible(state, formula)`
   - Evaluates possibility claims within state constraints
   - Grounded in state structure, not accessibility relations

### Truth Conditions

#### Extensional Operators
Standard truth-functional evaluation using verify/falsify sets:

```python
# Conjunction: A ∧ B
def conjunction_semantic_clause(self, sentence):
    """A ∧ B is verified when both A and B are verified."""
    x, args = sentence['x'], sentence['args']
    A, B = args[0], args[1]
    
    verify_conditions = z3.And(
        self.semantics.verify(x, A),
        self.semantics.verify(x, B)
    )
    
    falsify_conditions = z3.Or(
        self.semantics.falsify(x, A),
        self.semantics.falsify(x, B)
    )
    
    return z3.And(verify_conditions, falsify_conditions)
```

#### Imposition Operator
Counterfactual conditional using Fine's imposition semantics:

```python  
def imposition_semantic_clause(self, sentence):
    """A ↪ B: If A were imposed, B would follow."""
    x, args = sentence['x'], sentence['args']
    A, B = args[0], args[1]
    
    # Find states where imposing A leads to B
    verify_conditions = z3.Or([
        z3.And(
            self.semantics.is_part_of(y, x),
            self._imposition_leads_to(y, A, B)
        )
        for y in self.semantics.get_states()
    ])
    
    # Find states where imposing A leads to ¬B
    falsify_conditions = z3.Or([
        z3.And(
            self.semantics.is_part_of(z, x),
            self._imposition_leads_to(z, A, self._negate(B))
        )
        for z in self.semantics.get_states()
    ])
    
    return z3.And(verify_conditions, falsify_conditions)
```

#### Could Operator
Possibility within imposition framework:

```python
def could_semantic_clause(self, sentence):
    """⟂ A: A could be the case."""
    x, args = sentence['x'], sentence['args']
    A = args[0]
    
    # A is possible if there's a compatible state that verifies A
    verify_conditions = z3.Or([
        z3.And(
            self.semantics.compatible(y, x),
            self.semantics.verify(y, A)
        )
        for y in self.semantics.get_states()
    ])
    
    # A is impossible if all compatible states falsify A
    falsify_conditions = z3.And([
        z3.Implies(
            self.semantics.compatible(y, x),
            self.semantics.falsify(y, A)
        )
        for y in self.semantics.get_states()
    ])
    
    return z3.And(verify_conditions, falsify_conditions)
```

## Operator Implementation

### Operator Collection Structure

```python
# In operators.py
from model_checker.syntactic import OperatorCollection

# Extensional operators (reused from logos)
from model_checker.theory_lib.logos.subtheories.extensional.operators import (
    Negation, Conjunction, Disjunction, Conditional, Biconditional, Top, Bottom
)

# Imposition-specific operators
class ImpositionOperator(Operator):
    """Counterfactual conditional with Fine's imposition semantics."""
    
    def __init__(self):
        super().__init__("\\boxright", 2)
    
    def semantic_clause(self, sentence):
        # Implementation details...
        pass

class CouldOperator(Operator):
    """Possibility operator for imposition framework."""
    
    def __init__(self):
        super().__init__("\\diamondright", 1)
    
    def semantic_clause(self, sentence):
        # Implementation details...
        pass

# Create operator collection
imposition_operators = OperatorCollection({
    # Extensional
    "\\neg": Negation(),
    "\\wedge": Conjunction(),
    "\\vee": Disjunction(), 
    "\\to": Conditional(),
    "\\leftrightarrow": Biconditional(),
    "\\top": Top(),
    "\\bot": Bottom(),
    
    # Imposition-specific
    "\\boxright": ImpositionOperator(),
    "\\diamondright": CouldOperator(),
})
```

### Operator Design Patterns

#### Bilateral Semantics Pattern
All operators implement both verification and falsification:

```python
def operator_semantic_clause(self, sentence):
    """Standard pattern for bilateral semantics."""
    x, args = sentence['x'], sentence['args']
    
    # Define verification conditions
    verify_conditions = self._define_verification(x, args)
    
    # Define falsification conditions  
    falsify_conditions = self._define_falsification(x, args)
    
    # Both must be satisfied
    return z3.And(verify_conditions, falsify_conditions)
```

#### State Quantification Pattern
Many operators quantify over states in the model:

```python
def quantify_over_states(self, condition_function):
    """Common pattern for state quantification."""
    return z3.Or([
        condition_function(state)
        for state in self.semantics.get_states()
    ])
```

## Model Construction

### Integration with BuildExample

The imposition theory integrates seamlessly with ModelChecker's BuildExample:

```python
from model_checker import BuildExample
from model_checker.theory_lib.imposition import get_theory

# Standard usage pattern
theory = get_theory()
example_case = [premises, conclusions, settings]
example = BuildExample("test", theory, example_case)
result = example.check_result()
```

### Model Structure Reuse

The theory reuses LogosModelStructure for consistency:

```python
# In __init__.py
from model_checker.theory_lib.logos import (
    LogosProposition as Proposition,
    LogosModelStructure as ModelStructure,
)

def get_theory(config=None):
    return {
        "semantics": ImpositionSemantics,
        "proposition": Proposition,      # Reused from Logos
        "model": ModelStructure,         # Reused from Logos  
        "operators": imposition_operators
    }
```

### Constraint Generation

The theory generates Z3 constraints that capture Fine's semantics:

```python
class ImpositionSemantics(SemanticDefaults):
    def generate_frame_constraints(self):
        """Generate constraints specific to imposition semantics."""
        constraints = super().generate_frame_constraints()
        
        # Add imposition-specific constraints
        constraints.extend(self._imposition_constraints())
        constraints.extend(self._possibility_constraints())
        
        return constraints
    
    def _imposition_constraints(self):
        """Constraints governing the imposition operation."""
        # Ensure imposition respects Fine's minimality conditions
        return [
            # Constraint implementation...
        ]
```

## Integration Strategy

### Theory Comparison Support

The theory supports comparison with other theories through standardized interfaces:

```python
# In examples.py
semantic_theories = {
    "Primary": imposition_theory,    # Fine's imposition semantics
    "Alternative": logos_theory,     # Logos theory for comparison
}
```

### Component Reuse Philosophy

The architecture follows a strategic reuse pattern:

1. **Semantic Core**: Custom ImpositionSemantics for theory-specific behavior
2. **Proposition/Model**: Reuse Logos components for consistency
3. **Operators**: Mix of reused extensional and custom imposition operators
4. **Examples/Tests**: Theory-specific collections

### API Consistency

The theory implements the standard theory interface:

```python
# Required functions for uniform API
def get_theory(config=None):
    """Standard theory configuration interface."""
    
def get_examples():
    """Standard example access interface."""
    
def get_test_examples():  
    """Standard test example access interface."""
```

## Performance Considerations

### Computational Complexity

Imposition semantics introduces several performance challenges:

1. **State Space Growth**: O(2^N) states for N atomic propositions
2. **Imposition Computation**: Complex minimal change calculations
3. **Constraint Density**: Many interdependent Z3 constraints

### Optimization Strategies

#### State Management
```python
class ImpositionSemantics(SemanticDefaults):
    def __init__(self, settings):
        super().__init__(settings)
        # Optimize state representation
        self._state_cache = {}
        self._imposition_cache = {}
    
    def get_states(self):
        """Cached state enumeration."""
        if 'states' not in self._state_cache:
            self._state_cache['states'] = self._enumerate_states()
        return self._state_cache['states']
```

#### Constraint Optimization
```python  
def optimize_constraints(self, constraints):
    """Apply theory-specific optimizations."""
    # Group related constraints
    # Eliminate redundant constraints
    # Apply constraint simplification
    return optimized_constraints
```

### Memory Management

```python
# Efficient constraint generation
def semantic_clause(self, sentence):
    """Generate constraints efficiently."""
    # Use generators instead of lists where possible
    # Cache expensive computations
    # Release intermediate results
    pass
```

## Extension Points

### Adding New Operators

To add a new operator to the imposition theory:

1. **Create Operator Class**:
```python
class NewImpositionOperator(Operator):
    def __init__(self):
        super().__init__("\\newop", arity)
    
    def semantic_clause(self, sentence):
        # Implement semantics using imposition framework
        pass
```

2. **Register in Collection**:
```python
imposition_operators["\\newop"] = NewImpositionOperator()
```

3. **Add Tests and Documentation**:
   - Unit tests in `tests/`
   - Examples in `examples.py`
   - Documentation updates

### Extending Semantics

To modify the semantic framework:

```python
class ExtendedImpositionSemantics(ImpositionSemantics):
    """Extended version with additional features."""
    
    def __init__(self, settings):
        super().__init__(settings)
        # Add extensions
    
    def custom_operation(self, args):
        """New semantic operation."""
        pass
```

### Alternative Imposition Theories

The architecture supports alternative imposition theories:

```python
class AlternativeImpositionSemantics(SemanticDefaults):
    """Different approach to imposition semantics."""
    
    def imposition_operation(self, state, antecedent):
        """Alternative imposition definition."""
        # Different minimal change strategy
        pass
```

## Testing Architecture

### Test Organization

```
tests/
├── test_imposition.py       # Basic functionality tests
├── test_iterate.py          # Model iteration tests
└── test_operators.py        # Individual operator tests
```

### Test Patterns

```python
# Standard test pattern
def test_operator_behavior():
    """Test specific operator behavior."""
    theory = get_theory()
    example_case = [premises, conclusions, settings]
    example = BuildExample("test", theory, example_case)
    result = example.check_result()
    
    assert result['model_found'] == expected_result
```

## Future Development

### Potential Extensions

1. **Alternative Imposition Operations**: Different minimal change strategies
2. **Probabilistic Extensions**: Probabilistic counterfactuals
3. **Temporal Integration**: Temporal counterfactuals  
4. **Modal Extensions**: Combining with modal operators

### Integration Opportunities

1. **Cross-Theory Translation**: Automatic translation between imposition and other theories
2. **Hybrid Theories**: Combining imposition with other semantic approaches
3. **Performance Optimization**: Specialized constraint solving for imposition

## Documentation

### For Architects

- **[Core Components](#core-components)** - Theory structure and class hierarchy
- **[Semantic Framework](#semantic-framework)** - Fine's imposition semantics
- **[Integration Strategy](#integration-strategy)** - Component reuse philosophy

### For Implementers

- **[Operator Implementation](#operator-implementation)** - Design patterns and collection
- **[Model Construction](#model-construction)** - BuildExample integration
- **[Extension Points](#extension-points)** - Adding operators and semantics

### For Performance Engineers

- **[Performance Considerations](#performance-considerations)** - Complexity and optimization
- **[Memory Management](#memory-management)** - Efficient constraint generation
- **[Testing Architecture](#testing-architecture)** - Test organization and patterns

## Key Design Decisions

1. **Extend Logos**: Reuse hyperintensional foundation rather than rebuild
2. **Modular Operators**: Mix inherited and theory-specific operators
3. **State-Based**: Counterfactuals via state imposition, not world accessibility
4. **Z3 Integration**: Direct encoding of Fine's semantics in constraints
5. **Component Reuse**: Strategic reuse of Proposition and ModelStructure

## References

### Implementation Files

- **[Semantic Module](../semantic.py)** - ImpositionSemantics implementation
- **[Operators Module](../operators.py)** - Counterfactual operators
- **[Examples Module](../examples.py)** - 32 test cases

### Related Documentation

- **[API Reference](API_REFERENCE.md)** - Complete technical reference
- **[User Guide](USER_GUIDE.md)** - Tutorial with examples
- **[Logos Architecture](../../logos/docs/ARCHITECTURE.md)** - Foundation theory

---

[← Back to Documentation](README.md) | [API Reference →](API_REFERENCE.md) | [Imposition Theory →](../README.md)