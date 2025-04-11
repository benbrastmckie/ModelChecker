# Bimodal Logic Implementation

## Overview

The bimodal theory implements a temporal-modal logic that combines two types of modalities:

1. **Temporal operators**: For reasoning about what is true at different times (past and future)
2. **Modal operators**: For reasoning about alternative world histories

This implementation provides a framework to study bimodal logics where:

- World histories are sequences of world states evolving over time
- Each world state is an instantaneous configuration of the system
- World histories follow lawful transitions between consecutive states
- Time points can be negative, zero, or positive integers, constituting convex intervals
- Modal and temporal operators can interact in complex ways

## Contents

This package includes the following core modules:

- `semantic.py`: Defines the core semantics and model structure for bimodal logic
- `operators.py`: Implements all primitive and derived logical operators
- `examples.py`: Contains example formulas for testing and demonstration
- `__init__.py`: Exposes package definitions for external use

## Key Classes

### BimodalSemantics

The `BimodalSemantics` class defines the fundamental semantic model, including:

- **Primitive relations**: Task transitions between world states
- **Frame constraints**: Rules that define valid model structures
- **Truth conditions**: How to evaluate atomic propositions at world states

### BimodalProposition

The `BimodalProposition` class represents propositions assigned to sentences, handling:

- **Extension calculation**: Computing truth/falsity across worlds and times
- **Truth evaluation**: Checking truth values at specific world-time pairs
- **Proposition display**: Visualizing propositions in the model

### BimodalStructure

The `BimodalStructure` class manages the complete model structure:

- **World arrays**: Mappings from time points to world states
- **Time intervals**: Valid intervals for each world history
- **Time-shift relations**: Relationships between shifted world histories
- **Visualization**: Methods to display the model structure

## Frame Constraints

The bimodal logic framework is governed by nine critical frame constraints:

### 1. Valid World Constraint

Every model must have at least one world history (designated as world 0) that is marked as valid.

```python
valid_main_world = self.is_world(self.main_world)
```

### 2. Valid Time Constraint

Every model must have a valid evaluation time (designated as time 0).

```python
valid_main_time = self.is_valid_time(self.main_time)
```

### 3. Classical Truth Constraint

Each atomic sentence must have a consistent classical truth value at each world state.

```python
z3.ForAll(
    [world_state, sentence_letter],
    z3.Or(
        self.truth_condition(world_state, sentence_letter),
        z3.Not(self.truth_condition(world_state, sentence_letter))
    )
)
```

### 4. World Enumeration Constraint

World histories must be enumerated in sequence starting from 0.

```python
z3.ForAll(
    [enumerate_world],
    z3.Implies(
        self.is_world(enumerate_world),
        enumerate_world >= 0
    )
)
```

### 5. Convex World Ordering Constraint

There can be no gaps in the enumeration of worlds (ensures worlds are created in sequence).

```python
z3.ForAll(
    [convex_world],
    z3.Implies(
        z3.And(
            self.is_world(convex_world),
            convex_world > 0
        ),
        self.is_world(convex_world - 1)
    )
)
```

### 6. Lawful Transition Constraint

Each world history must follow lawful transitions between consecutive states.

```python
z3.ForAll(
    [lawful_world, lawful_time],
    z3.Implies(
        z3.And(
            self.is_world(lawful_world),
            self.is_valid_time(lawful_time, -1),
            self.is_valid_time_for_world(lawful_world, lawful_time),
            self.is_valid_time_for_world(lawful_world, lawful_time + 1)
        ),
        self.task(
            z3.Select(self.world_function(lawful_world), lawful_time),
            z3.Select(self.world_function(lawful_world), lawful_time + 1)
        )
    )
)
```

### 7. World Interval Constraint

Each world history must have a valid time interval with consistent state transitions.

```python
world_interval_constraint = z3.ForAll(
    [interval_world],
    z3.Implies(
        self.is_world(interval_world),
        z3.Or(*interval_options)  # One of the valid interval options must apply
    )
)
```

### 8. Abundance Constraint

Each world history that can be time-shifted must have appropriately shifted counterparts.

```python
z3.Implies(
    z3.And(
        self.is_world(z3.IntVal(0)),
        self.can_shift_forward(z3.IntVal(0))
    ),
    z3.Exists(
        [main_fwd],
        self.is_shifted_by(z3.IntVal(0), 1, main_fwd)
    )
)
```

### 9. World Uniqueness Constraint

No two worlds can have identical histories over their entire intervals.

```python
z3.ForAll(
    [world_one, world_two],
    z3.Implies(
        z3.And(
            self.is_world(world_one),
            self.is_world(world_two),
            world_one != world_two
        ),
        z3.Exists(
            [some_time],
            z3.And(
                self.is_valid_time(some_time),
                self.is_valid_time_for_world(world_one, some_time),
                self.is_valid_time_for_world(world_two, some_time),
                z3.Select(self.world_function(world_one), some_time) !=
                z3.Select(self.world_function(world_two), some_time)
            )
        )
    )
)
```

## Core Operators

The bimodal theory implements several categories of operators:

### Extensional Operators

- **NegationOperator (`¬`)**: Logical negation
- **AndOperator (`∧`)**: Logical conjunction
- **OrOperator (`∨`)**: Logical disjunction
- **ConditionalOperator (`→`)**: Material implication (defined)
- **BiconditionalOperator (`↔`)**: Material biconditional (defined)

### Extremal Operators

- **BotOperator (`⊥`)**: Logical contradiction/falsity
- **TopOperator (`⊤`)**: Logical tautology/truth (defined)

### Modal Operators

- **NecessityOperator (`□`)**: Truth in all possible worlds
- **DefPossibilityOperator (`◇`)**: Truth in at least one possible world (defined)

### Temporal Operators

- **FutureOperator (`⏵`)**: Truth at all future times
- **PastOperator (`⏴`)**: Truth at all past times
- **DefFutureOperator (`\future`)**: Possibility of future truth (defined)
- **DefPastOperator (`\past`)**: Possibility of past truth (defined)

## Key Operator Semantics

### Necessity Operator (`\Box`)

The necessity operator `\Box A` has a complex, bimodal semantics that combines modal and temporal requirements:

#### Truth Condition

`\Box A` is true at world `w` at time `t` if and only if:

1. A is true at time `t` in all possible worlds, **AND**
2. A is true at all future times in the current world `w`

```python
def true_at(self, argument, eval_world, eval_time):
    # Part 1: A must be true in all possible worlds at eval_time
    true_in_all_worlds = z3.ForAll(
        world_id,
        z3.Implies(
            semantics.is_world(world_id),
            semantics.true_at(argument, world_id, eval_time)
        )
    )

    # Part 2: A must be true at all future times in the current world
    true_at_future_times = z3.ForAll(
        future_time,
        z3.Implies(
            z3.And(
                semantics.is_valid_time_for_world(eval_world, future_time),
                eval_time < future_time
            ),
            semantics.true_at(argument, eval_world, future_time)
        )
    )

    # Both conditions must be satisfied for Box A to be true
    return z3.And(true_in_all_worlds, true_at_future_times)
```

#### Falsity Condition

`\Box A` is false at world `w` at time `t` if and only if:

1. A is false at time `t` in at least one possible world, **OR**
2. A is false at at least one future time in the current world `w`

### Future Operator (`\Future`)

The future operator `\Future A` has a purely temporal semantics:

#### Truth Condition

`\Future A` is true at world `w` at time `t` if and only if A is true at all future times in world `w`.

```python
def true_at(self, argument, eval_world, eval_time):
    return z3.ForAll(
        time,
        z3.Implies(
            z3.And(
                semantics.is_valid_time_for_world(eval_world, time),
                eval_time < time
            ),
            semantics.true_at(argument, eval_world, time)
        )
    )
```

#### Falsity Condition

`\Future A` is false at world `w` at time `t` if and only if A is false at at least one future time in world `w`.

### Past Operator (`\Past`)

The past operator `\Past A` has a purely temporal semantics:

#### Truth Condition

`\Past A` is true at world `w` at time `t` if and only if A is true at all past times in world `w`.

```python
def true_at(self, argument, eval_world, eval_time):
    return z3.ForAll(
        time,
        z3.Implies(
            z3.And(
                semantics.is_valid_time_for_world(eval_world, time),
                eval_time > time
            ),
            semantics.true_at(argument, eval_world, time)
        )
    )
```

#### Falsity Condition

`\Past A` is false at world `w` at time `t` if and only if A is false at at least one past time in world `w`.

## Important Theorems

The bimodal semantics validates several important theorems that demonstrate the interaction between modal and temporal operators:

1. **Box-Future Theorem**: `\Box A → \Future A`
   - If A is necessarily true, then it is always true in the future
   - This theorem shows how necessity implies future persistence

2. **Box-Past Theorem**: `\Box A → \Past A`
   - If A is necessarily true, then it was always true in the past
   - This theorem shows how necessity implies past persistence

3. **Possibility-Future Theorem**: `\future A → \Diamond A`
   - If A is possibly true in the future, then A is possible
   - This theorem connects future possibility to general possibility

4. **Possibility-Past Theorem**: `\past A → \Diamond A`
   - If A was possibly true in the past, then A is possible
   - This theorem connects past possibility to general possibility

## Implementation Details

### World and Time Representation

The bimodal implementation uses these key representations:

- **World states**: Represented as bitvectors (fusions of atomic states)
- **Time points**: Integers allowing negative, zero, and positive values
- **World histories**: Arrays mapping time points to world states
- **Time intervals**: Convex ranges of valid times for each world
- **Evaluation point**: World-time pair where formulas are evaluated (default: world 0, time 0)

### Time-Shift Relations

Each world history may have time-shifted counterparts:

- **Forward shift**: A world identical to another but shifted forward in time
- **Backward shift**: A world identical to another but shifted backward in time
- **Shift tracking**: The model maintains time-shift relationships between worlds

### Model Extraction

The model extraction process follows these steps:

1. Identify all valid world IDs in the model
2. Extract world arrays for each valid world
3. Extract time intervals for each world
4. Build world histories (time-to-state mappings) for each world
5. Determine time-shift relations between worlds
6. Compute truth and falsity extensions for propositions

## Basic Usage

### Creating a Bimodal Model

```python
from model_checker import BuildExample, get_theory

# Load the bimodal theory
theory = get_theory("bimodal")

# Create a model with default settings
model = BuildExample("temporal_example", theory)

# Check a temporal formula
result = model.check_formula("A \\rightarrow \\Future A")
```

### Custom Settings

The bimodal theory supports several configurable settings:

- `N`: Number of world states (default: 2)
- `M`: Number of time points (default: 2)
- `contingent`: Whether sentence letters are assigned to contingent propositions (default: False)
- `disjoint`: Whether sentence letters are assigned to distinct world states (default: False)
- `max_time`: Maximum Z3 solving time in seconds (default: 1)

Example with custom settings:

```python
settings = {
    'N': 3,        # 3 possible world states
    'M': 4,        # 4 times including time 0
    'contingent': True,
    'max_time': 5  # Allow up to 5 seconds for solving
}
model = BuildExample("my_example", theory, settings=settings)
```

### Testing Theorems and Countermodels

The bimodal theory includes examples for testing both theorems and countermodels:

```python
from model_checker import BuildExample, get_theory

theory = get_theory("bimodal")

# Test the Box-Future theorem
box_future_premises = ['\\Box A']
box_future_conclusions = ['\\Future A']
model = BuildExample("box_future_theorem", theory)
result = model.check_argument(box_future_premises, box_future_conclusions)
```

## Design Philosophy

The bimodal implementation follows these key design principles:

1. **Explicit World References**: Always use consistent world references with explicit world IDs
2. **Deterministic Behavior**: Avoid default values or implicit conversions that can mask errors
3. **Required Parameters**: Make parameters explicitly required with no implicit type conversions
4. **Clear Data Flow**: Keep a consistent approach to passing data between components
5. **Fail Fast**: Let errors occur naturally with standard Python tracebacks for better debugging

## Known Limitations

- **Performance**: Models with many time points or complex formulas may run slowly
- **Z3 Timeouts**: Complex models may hit solver timeouts (adjust the `max_time` setting)
- **Abundance Impact**: The abundance constraint significantly increases computational load
- **Model Complexity**: The full bimodal semantics creates models that may challenge Z3's capabilities
- **Memory Usage**: Large models with many worlds and times can consume significant memory

## References

For more information on bimodal logics and related topics, see:

- The full ModelChecker documentation in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/README.md`
- The test suite in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/test/`
- The Counterfactuals paper in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Counterfactuals.pdf`
