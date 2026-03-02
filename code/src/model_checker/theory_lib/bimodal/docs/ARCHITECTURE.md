# Bimodal Logic Architecture

## Overview

The Bimodal theory implements temporal-modal logic through a modular architecture that extends the ModelChecker framework. This document provides a comprehensive technical overview of the theory's design, implementation patterns, and integration with the broader system for reasoning about both time and possibility.

## Table of Contents

- [Core Components](#core-components)
- [Semantic Framework](#semantic-framework)
- [Operator Implementation](#operator-implementation)
- [Model Construction](#model-construction)
- [Integration Strategy](#integration-strategy)
- [Performance Considerations](#performance-considerations)
- [Extension Points](#extension-points)

## Core Components

### Theory Structure

```
bimodal/
├── __init__.py          # Public API and theory configuration
├── semantic.py          # BimodalSemantics implementation
├── operators.py         # Operator collection with temporal-modal operators
├── examples.py          # Comprehensive example collection
├── iterate.py           # Model iteration support
├── docs/               # Documentation (this file and others)
├── tests/              # Unit and integration tests
└── notebooks/          # Interactive tutorials
```

### Class Hierarchy

```python
# Core semantic framework
BimodalSemantics(SemanticDefaults)
├── Inherits base truthmaker semantics
├── Adds temporal-modal evaluation methods
└── Configures world-history semantics

# Model and proposition structures
BimodalStructure(ModelStructure)
├── Extends base model structure
├── Adds temporal dimension (time points)
└── Manages world histories

BimodalProposition(Proposition)
├── Extends base proposition handling
└── Supports temporal-modal formulas

# Operator collection
bimodal_operators: OperatorCollection
├── Extensional operators (¬, ∧, ∨, →, ↔)
├── Modal operators (□, ◇)
├── Temporal operators (⏵, ⏴)
└── Extremal operators (⊤, ⊥)
```

## Semantic Framework

### World History Semantics

The theory implements temporal-modal logic using world histories:

#### Time Points and Worlds
```python
class BimodalSemantics(SemanticDefaults):
    """Implements world-history semantics for temporal-modal logic."""
    
    def __init__(self, settings):
        super().__init__(settings)
        self.time_points = range(settings.get('M', 1))
        self.world_histories = self._generate_world_histories()
    
    def evaluate_at_point(self, world, time, formula):
        """Evaluate formula at specific (world, time) point."""
        return self._evaluate_temporal_modal(world, time, formula)
```

#### Key Semantic Operations

1. **Temporal Evaluation**: `evaluate_temporal(world, time, formula)`
   - Evaluates formulas relative to specific time points
   - Handles temporal operator progression

2. **Modal Evaluation**: `evaluate_modal(world, time, formula)`
   - Evaluates modal formulas at specific (world, time) points
   - Uses accessibility relations between worlds

3. **World History Management**: `get_world_histories()`
   - Manages sequences of worlds across time
   - Ensures temporal continuity

4. **Accessibility Relations**: `accessible_worlds(world, time)`
   - Defines modal accessibility at each time point
   - Supports temporal evolution of modal structure

### Truth Conditions

#### Extensional Operators
Standard truth-functional evaluation at each (world, time) point:

```python
# Conjunction: A ∧ B
def conjunction_semantic_clause(self, sentence):
    """A ∧ B is true when both A and B are true at the evaluation point."""
    world, time, args = sentence['world'], sentence['time'], sentence['args']
    A, B = args[0], args[1]
    
    return z3.And(
        self.evaluate_at_point(world, time, A),
        self.evaluate_at_point(world, time, B)
    )
```

#### Modal Operators
Modal evaluation considers accessible worlds at current time:

```python
def necessity_semantic_clause(self, sentence):
    """□A: A is necessary (true at all accessible worlds)."""
    world, time, args = sentence['world'], sentence['time'], sentence['args']
    A = args[0]
    
    # A is necessary if true at all accessible worlds at current time
    accessible = self.accessible_worlds(world, time)
    return z3.And([
        self.evaluate_at_point(w, time, A)
        for w in accessible
    ])

def possibility_semantic_clause(self, sentence):
    """◇A: A is possible (true at some accessible world)."""
    world, time, args = sentence['world'], sentence['time'], sentence['args']
    A = args[0]
    
    # A is possible if true at some accessible world at current time
    accessible = self.accessible_worlds(world, time)
    return z3.Or([
        self.evaluate_at_point(w, time, A)
        for w in accessible
    ])
```

#### Temporal Operators
Temporal evaluation moves along time dimension within world histories:

```python
def future_semantic_clause(self, sentence):
    """⏵A: A will be true (true at next time point)."""
    world, time, args = sentence['world'], sentence['time'], sentence['args']
    A = args[0]
    
    # Check bounds
    if time + 1 >= len(self.time_points):
        return z3.BoolVal(False)
    
    # A is true at next time point in same world
    return self.evaluate_at_point(world, time + 1, A)

def past_semantic_clause(self, sentence):
    """⏴A: A was true (true at previous time point)."""
    world, time, args = sentence['world'], sentence['time'], sentence['args']
    A = args[0]
    
    # Check bounds
    if time - 1 < 0:
        return z3.BoolVal(False)
    
    # A was true at previous time point in same world
    return self.evaluate_at_point(world, time - 1, A)
```

## Operator Implementation

### Operator Collection Structure

```python
# In operators.py
from model_checker.syntactic import OperatorCollection, Operator

# Extensional operators (standard logical operators)
class Negation(Operator):
    def __init__(self):
        super().__init__("\\neg", 1)
    
    def semantic_clause(self, sentence):
        # Classical negation at evaluation point
        pass

# Modal operators
class Necessity(Operator):
    def __init__(self):
        super().__init__("\\Box", 1)
    
    def semantic_clause(self, sentence):
        # Modal necessity across accessible worlds
        pass

class Possibility(Operator):
    def __init__(self):
        super().__init__("\\Diamond", 1)
    
    def semantic_clause(self, sentence):
        # Modal possibility across accessible worlds
        pass

# Temporal operators
class Future(Operator):
    def __init__(self):
        super().__init__("\\future", 1)
    
    def semantic_clause(self, sentence):
        # Temporal progression to next time point
        pass

class Past(Operator):
    def __init__(self):
        super().__init__("\\past", 1)
    
    def semantic_clause(self, sentence):
        # Temporal regression to previous time point
        pass

# Create operator collection
bimodal_operators = OperatorCollection({
    # Extensional
    "\\neg": Negation(),
    "\\wedge": Conjunction(),
    "\\vee": Disjunction(),
    "\\to": Conditional(),
    "\\leftrightarrow": Biconditional(),
    "\\top": Top(),
    "\\bot": Bottom(),
    
    # Modal
    "\\Box": Necessity(),
    "\\Diamond": Possibility(),
    
    # Temporal
    "\\future": Future(),
    "\\past": Past(),
})
```

### Operator Design Patterns

#### Temporal-Modal Interaction Pattern
Operators that combine temporal and modal reasoning:

```python
def temporal_modal_operator(self, sentence):
    """Pattern for operators combining temporal and modal evaluation."""
    world, time, args = sentence['world'], sentence['time'], sentence['args']
    
    # First apply temporal operation
    temporal_result = self.apply_temporal_operation(world, time, args)
    
    # Then apply modal operation to result
    modal_result = self.apply_modal_operation(temporal_result)
    
    return modal_result
```

#### World History Pattern
Many operators must consider world histories:

```python
def evaluate_across_history(self, world_history, formula):
    """Common pattern for evaluating across time points."""
    return z3.And([
        self.evaluate_at_point(world_history[t], t, formula)
        for t in self.time_points
    ])
```

## Model Construction

### Integration with BuildExample

The bimodal theory integrates seamlessly with ModelChecker's BuildExample:

```python
from model_checker import BuildExample
from model_checker.theory_lib.bimodal import get_theory

# Standard usage pattern
theory = get_theory()
example_case = [premises, conclusions, settings]
example = BuildExample("temporal_modal_test", theory, example_case)
result = example.check_result()
```

### Model Structure Implementation

The theory uses specialized model structures for temporal-modal reasoning:

```python
# In __init__.py
def get_theory(config=None):
    return {
        "semantics": BimodalSemantics,
        "proposition": BimodalProposition,
        "model": BimodalStructure,
        "operators": bimodal_operators
    }
```

### Constraint Generation

The theory generates Z3 constraints that capture temporal-modal semantics:

```python
class BimodalSemantics(SemanticDefaults):
    def generate_frame_constraints(self):
        """Generate constraints specific to temporal-modal semantics."""
        constraints = super().generate_frame_constraints()
        
        # Add temporal constraints
        constraints.extend(self._temporal_constraints())
        
        # Add modal constraints
        constraints.extend(self._modal_constraints())
        
        # Add temporal-modal interaction constraints
        constraints.extend(self._temporal_modal_constraints())
        
        return constraints
    
    def _temporal_constraints(self):
        """Constraints governing temporal structure."""
        return [
            # Time points are linearly ordered
            # Temporal operators respect boundaries
            # World histories are consistent
        ]
    
    def _modal_constraints(self):
        """Constraints governing modal structure."""
        return [
            # Accessibility relations at each time
            # Modal operator behavior
            # World branching structure
        ]
```

## Integration Strategy

### Theory Comparison Support

The theory supports comparison with other theories through standardized interfaces:

```python
# In examples.py
semantic_theories = {
    "Primary": bimodal_theory,      # Temporal-modal logic
    "Alternative": logos_theory,    # For comparison with hyperintensional logic
}
```

### Component Design Philosophy

The architecture follows a specialized design pattern:

1. **Semantic Core**: Custom BimodalSemantics for temporal-modal behavior
2. **Proposition/Model**: Specialized components for temporal-modal structures  
3. **Operators**: Comprehensive collection covering temporal, modal, and extensional operators
4. **Examples/Tests**: Theory-specific collections demonstrating temporal-modal reasoning

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

Bimodal semantics introduces significant performance challenges:

1. **State Space Growth**: O(2^(M×N)) for M time points and N propositions
2. **Modal Branching**: Multiple worlds at each time point
3. **Temporal Depth**: Linear growth with number of time points
4. **Constraint Density**: Complex interactions between temporal and modal constraints

### Optimization Strategies

#### Time Point Management
```python
class BimodalSemantics(SemanticDefaults):
    def __init__(self, settings):
        super().__init__(settings)
        # Optimize time point representation
        self.max_time = settings.get('M', 1)
        self._time_cache = {}
        self._world_cache = {}
    
    def get_time_points(self):
        """Cached time point enumeration."""
        if 'times' not in self._time_cache:
            self._time_cache['times'] = list(range(self.max_time))
        return self._time_cache['times']
```

#### World History Optimization
```python
def optimize_world_histories(self):
    """Optimize world history representation."""
    # Use efficient data structures for world sequences
    # Cache temporal transitions
    # Minimize modal branching where possible
    pass
```

### Memory Management

```python
# Efficient constraint generation for temporal-modal logic
def semantic_clause(self, sentence):
    """Generate constraints efficiently for bimodal operators."""
    # Use generators for large time/world spaces
    # Cache expensive modal computations
    # Release intermediate temporal results
    pass
```

## Extension Points

### Adding New Operators

To add a new operator to the bimodal theory:

1. **Create Operator Class**:
```python
class NewTemporalModalOperator(Operator):
    def __init__(self):
        super().__init__("\\newop", arity)
    
    def semantic_clause(self, sentence):
        # Implement semantics using temporal-modal framework
        world, time = sentence['world'], sentence['time']
        # Handle both temporal and modal aspects
        pass
```

2. **Register in Collection**:
```python
bimodal_operators["\\newop"] = NewTemporalModalOperator()
```

3. **Add Tests and Documentation**:
   - Unit tests in `tests/`
   - Examples in `examples.py`
   - Documentation updates

### Extending Semantics

To modify the semantic framework:

```python
class ExtendedBimodalSemantics(BimodalSemantics):
    """Extended version with additional temporal-modal features."""
    
    def __init__(self, settings):
        super().__init__(settings)
        # Add extensions
    
    def custom_temporal_operation(self, world, time, args):
        """New temporal operation."""
        pass
    
    def custom_modal_operation(self, world, time, args):
        """New modal operation."""
        pass
```

### Alternative Temporal-Modal Theories

The architecture supports alternative temporal-modal approaches:

```python
class AlternativeBimodalSemantics(SemanticDefaults):
    """Different approach to temporal-modal semantics."""
    
    def temporal_accessibility(self, world, time):
        """Alternative temporal accessibility relation."""
        # Different temporal structure (branching, circular, etc.)
        pass
    
    def modal_accessibility(self, world, time):
        """Alternative modal accessibility relation."""
        # Different modal structure at each time
        pass
```

## Testing Architecture

### Test Organization

```
tests/
├── test_bimodal.py         # Basic functionality tests
├── test_iterate.py         # Model iteration tests
├── test_temporal.py        # Temporal operator tests
├── test_modal.py          # Modal operator tests
└── test_interactions.py   # Temporal-modal interaction tests
```

### Test Patterns

```python
# Standard test pattern for bimodal logic
def test_temporal_modal_interaction():
    """Test interaction between temporal and modal operators."""
    theory = get_theory()
    
    # Test □⏵p vs ⏵□p distinction
    example_case = [
        ["□⏵p"],           # Premises: necessarily, p will be true
        ["⏵□p"],           # Conclusions: in the future, p will be necessary
        {"M": 3, "N": 1, "expectation": False}  # These should be different
    ]
    
    example = BuildExample("temporal_modal_test", theory, example_case)
    result = example.check_result()
    
    # Should find countermodel showing the distinction
    assert result['model_found'] == True
```

## Future Development

### Potential Extensions

1. **Temporal Logic Variants**: Branching time, circular time, dense time
2. **Modal Logic Variants**: Different accessibility relations, multi-modal systems
3. **Temporal-Modal Operators**: Until, since, always eventually, etc.
4. **Probabilistic Extensions**: Probabilistic temporal-modal logic

### Integration Opportunities

1. **Cross-Theory Translation**: Automatic translation between bimodal and other theories
2. **Temporal Hyperintensional Logic**: Combining with Logos theory
3. **Dynamic Logic Integration**: Action and temporal-modal reasoning
4. **Performance Optimization**: Specialized solvers for temporal-modal constraints

## Theoretical Background

The bimodal theory combines several logical traditions:

### Temporal Logic Foundation
- **Linear Time**: Discrete time points forming sequences
- **Temporal Operators**: Future and past operators for temporal reasoning
- **Time-Relative Evaluation**: Formulas evaluated at specific time points

### Modal Logic Foundation  
- **Possible Worlds**: Alternative possibilities at each time point
- **Accessibility Relations**: Connections between possible worlds
- **Modal Operators**: Necessity and possibility for modal reasoning

### Combined Framework
- **World Histories**: Sequences of worlds across time
- **Dual Accessibility**: Both temporal and modal accessibility relations
- **Point Evaluation**: Formulas evaluated at (world, time) pairs

## Conclusion

The Bimodal theory architecture provides a sophisticated implementation of temporal-modal logic within the ModelChecker framework. The design emphasizes:

- **Dual Reasoning**: Seamless integration of temporal and modal operators
- **Scalability**: Efficient handling of complex temporal-modal structures
- **Extensibility**: Clear extension points for new temporal-modal operators
- **Performance**: Optimization strategies for computationally intensive reasoning
- **Integration**: Full compatibility with ModelChecker ecosystem

This architecture enables researchers to explore sophisticated temporal-modal reasoning patterns while maintaining the performance and usability standards expected from the ModelChecker platform.

---

**Navigation**: [README](../README.md) | [User Guide](USER_GUIDE.md) | [Operators](OPERATORS.md) | [Settings](SETTINGS.md)