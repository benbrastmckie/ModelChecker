# Strategy 2: Witness Predicates for Exclusion Semantics

## Overview

This directory implements the **witness predicate** solution for Champollion-Bernard (CB) preclusion semantics within the ModelChecker framework. The key innovation is treating existentially quantified witness functions as first-class model predicates, enabling Z3 to correctly handle complex nested formulas with existential quantification.

**Key Achievement**: All 41 test examples execute correctly, solving the persistent "false premise problem" that affected previous implementations.

## Architecture

### Core Modules

#### [`semantic.py`](semantic.py) (1183 lines)
The central orchestration module implementing witness-aware semantics.

**Key Components:**
- `WitnessAwareModel`: Extended Z3 model with witness function access
- `WitnessRegistry`: Centralized management of witness predicate declarations
- `WitnessConstraintGenerator`: Translates CB semantic conditions to Z3 constraints
- `WitnessSemantics`: Main semantic class coordinating all components
- `WitnessStructure`: Model structure with witness printing capabilities
- `WitnessProposition`: Proposition class for the theory

**Core Innovation:**
```python
class WitnessAwareModel:
    def get_h_witness(self, formula_str: str, state: int) -> Optional[int]:
        """Query h witness function for formula at state."""
        h_pred = self.witness_predicates.get(f"{formula_str}_h")
        if h_pred is None:
            return None
        state_bv = z3.BitVecVal(state, self.semantics.N)
        result = self.eval(h_pred(state_bv))
        return result.as_long() if z3.is_bv_value(result) else None
```

#### [`operators.py`](operators.py) (656 lines)
Implements logical operators using witness predicates.

**Operators:**
- `UniNegationOperator` (`\func_unineg`): CB preclusion with witness functions
- `FineUniNegation` (`\set_unineg`): Fine's set-based preclusion (no witnesses)
- `UniConjunctionOperator` (`\uniwedge`): Standard conjunction
- `UniDisjunctionOperator` (`\univee`): Standard disjunction
- `UniIdentityOperator` (`\uniequiv`): Identity based on verifier equality

**Key Pattern:**
```python
def compute_verifiers(self, argument, model, eval_point):
    """Compute verifiers by querying witness predicates from model."""
    formula_str = f"\\func_unineg({self._formula_to_string(argument)})"
    verifiers = []
    for state in range(2**self.semantics.N):
        if self._verifies_uninegation_with_predicates(state, formula_str, model):
            verifiers.append(state)
    return verifiers
```

#### [`examples.py`](examples.py) (1053 lines)
Comprehensive test suite demonstrating the solution.

**Test Categories:**
- Frame examples (basic constraints)
- Negation chains (double, triple, quadruple)
- DeMorgan's laws (all four forms)
- Distribution laws
- Absorption laws
- Associativity laws
- Identity examples

**Notable Success:**
```python
# This previously failed due to false premise problem
de_morgan_3 = [
    ["\\func_unineg(A \\uniwedge B)"],  # Premise: ¬(A ∧ B)
    ["\\func_unineg A \\univee \\func_unineg B"],  # Conclusion: ¬A ∨ ¬B
    {"N": 3}
]
# Now correctly finds countermodel!
```

#### [`examples_fine.py`](examples_fine.py) (218 lines)
Tests comparing CB and Fine preclusion approaches.

**Key Tests:**
- CB implies Fine preclusion
- Fine doesn't imply CB preclusion
- Comparative behavior on complex formulas

### Documentation

#### [`docs/WITNESS.md`](docs/WITNESS.md)
Comprehensive explanation of witness predicates accessible to newcomers.

**Topics Covered:**
- Introduction to CB vs Fine preclusion
- The challenge of quantifying over functions
- How witness predicates solve the problem
- Implementation details
- Comparison of approaches

#### [`docs/PLAN_2.md`](docs/PLAN_2.md)
Strategic planning document for the witness predicate approach.

**Key Insights:**
- Makes witness functions explicit in the model
- Enables bidirectional constraints
- Avoids need for Skolem functions

#### [`docs/SEED_2.md`](docs/SEED_2.md)
Initial conceptual seed for the witness approach.

## How It Works

### 1. Formula Analysis Phase
When building a model, the system traverses formulas to identify all uninegation subformulas:

```python
def _register_witness_predicates_recursive(self, formula):
    """Traverse formula tree and register witnesses for each uninegation."""
    if isinstance(formula, z3.ExprRef):
        if hasattr(formula, 'decl') and formula.decl().name().startswith('\\func_unineg'):
            formula_str = self._formula_to_string(formula)
            self.witness_registry.register_witness_predicates(formula_str)
```

### 2. Witness Registration
For each `\func_unineg(φ)` formula, create witness functions:

```python
def register_witness_predicates(self, formula_str: str):
    h_pred = z3.Function(f"{formula_str}_h", z3.BitVecSort(self.N), z3.BitVecSort(self.N))
    y_pred = z3.Function(f"{formula_str}_y", z3.BitVecSort(self.N), z3.BitVecSort(self.N))
    self.predicates[f"{formula_str}_h"] = h_pred
    self.predicates[f"{formula_str}_y"] = y_pred
    return h_pred, y_pred
```

### 3. Constraint Generation
Link witness behavior to CB preclusion conditions:

```python
# If state e verifies \func_unineg(A), then h and y witness this
z3.Implies(
    verifies(e, formula_str),
    z3.And(
        # Condition 1: Exclusion property
        z3.ForAll([v], z3.Implies(
            verifies(v, 'A'),
            z3.And(is_part_of(y(v), v), excludes(h(v), y(v)))
        )),
        # Condition 2: Upper bound
        z3.ForAll([v], z3.Implies(
            verifies(v, 'A'),
            is_part_of(h(v), e)
        )),
        # Condition 3: Minimality - state is the smallest satisfying conditions 1 & 2
        z3.ForAll([z], z3.Implies(
            z3.And(
                is_part_of(z, state),  # z is a proper part of state
                z != state,
                # All h values that fit in state also fit in z
                z3.ForAll([v], z3.Implies(
                    verifies(v, 'A'),
                    is_part_of(h(v), z)
                ))
            ),
            # Then z must fail condition 1 (can't properly exclude)
            z3.Not(z3.ForAll([v], z3.Implies(
                verifies(v, 'A'),
                z3.And(is_part_of(y(v), v), excludes(h(v), y(v)))
            )))
        ))
    )
)
```

### 4. Model Solving
Z3 finds values for all witness functions simultaneously.

### 5. Witness Querying
During truth evaluation, query witness values:

```python
h_v = model.get_h_witness(formula_str, verifier)
y_v = model.get_y_witness(formula_str, verifier)
# Use these values to check CB conditions
```

## Theoretical Comparison

### CB Preclusion (with Witnesses)
- **Semantics**: Function-based mapping of verifiers to excluded parts
- **Implementation**: Requires witness predicates for function quantification
- **Expressiveness**: Can capture fine-grained exclusion relationships

### Fine Preclusion (without Witnesses)
- **Semantics**: Set-based coverage and relevance conditions
- **Implementation**: Direct enumeration of state subsets
- **Expressiveness**: Simpler but less fine-grained

### Relationship
Our tests confirm:
- CB preclusion implies Fine preclusion
- Fine preclusion does NOT imply CB preclusion
- CB is strictly stronger than Fine

## Usage Example

```python
from model_checker.theory_lib.exclusion.strategy2_witness import (
    WitnessSemantics,
    WitnessProposition,
    WitnessStructure,
    witness_operators
)

# Define theory
theory = {
    "semantics": WitnessSemantics,
    "proposition": WitnessProposition,
    "model": WitnessStructure,
    "operators": witness_operators,
    "dictionary": {}
}

# Test CB preclusion
example = [
    ["A"],                    # Premise
    ["\\func_unineg A"],     # Conclusion (should fail)
    {"N": 3}
]
```

## Key Insights

1. **Architecture Enables Logic**: The witness predicate pattern is an architectural choice that makes complex logical semantics tractable in Z3.

2. **Explicit Over Implicit**: By making witness functions explicit model citizens, we avoid the complexities of Skolemization and function synthesis.

3. **Modularity Matters**: Each formula gets its own witness functions, enabling independent reasoning about different uninegation instances.

4. **Debugging Benefits**: Witness values are inspectable in model output, aiding understanding and debugging.

## Performance Characteristics

- **Constraint Complexity**: O(|formulas| × 2^N) for witness constraints
- **Memory Usage**: Minimal overhead for storing witness functions
- **Query Performance**: O(1) witness lookups during evaluation
- **Overall**: Negligible performance cost for complete correctness

## Future Directions

1. **Optimization**: Cache witness queries for repeated evaluations
2. **Visualization**: Enhanced display of witness mappings
3. **Generalization**: Apply witness pattern to other quantified semantics
4. **Integration**: Unified interface for both CB and Fine approaches

## Related Documentation

- [Parent Exclusion Theory README](../README.md)
- [Witness Predicates Explanation](docs/WITNESS.md)
- [Implementation Planning](docs/PLAN_2.md)
- [Z3 Background](/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Docs/Z3_BACKGROUND.md)