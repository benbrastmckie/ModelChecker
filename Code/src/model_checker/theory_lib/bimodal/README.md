# Bimodal Logic Implementation

## Overview

The bimodal theory implements a temporal-modal logic with two types of operators:

1. Temporal operators for reasoning about what is true at different times
2. Modal operators for reasoning about other world histories

This implementation is designed to study bimodal logics where:

- World histories are sequences of world states over time
- Each world state is an instantaneous configuration of the system
- World histories follow lawful transitions between consecutive states
- Time points can be negative, zero, or positive integers, constituting convex intervals

## Contents

This package includes the following components:

- `__init__.py` to expose definitions
- `examples.py` defines a number of examples to test
- `operators.py` defines the primitive and derived operators
- `semantic.py` defines the core semantics for the bimodal logic

## Frame Constraints

The bimodal logic is defined by the following key frame constraints that determine the structure of models:

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

## Operator Semantics

### Necessity Operator (`\Box`)

The necessity operator `\Box A` has a complex, bimodal semantics that combines both modal and temporal requirements:

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

```python
def false_at(self, argument, eval_world, eval_time):
    # Part 1: A is false in at least one world at eval_time
    false_in_some_world = z3.Exists(
        world_id,
        z3.And(
            semantics.is_world(world_id),
            semantics.false_at(argument, world_id, eval_time)
        )
    )

    # Part 2: A is false at at least one future time in the current world
    false_at_some_future_time = z3.Exists(
        future_time,
        z3.And(
            semantics.is_valid_time_for_world(eval_world, future_time),
            eval_time < future_time,
            semantics.false_at(argument, eval_world, future_time)
        )
    )

    # Box A is false if either condition is true
    return z3.Or(false_in_some_world, false_at_some_future_time)
```

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

```python
def false_at(self, argument, eval_world, eval_time):
    return z3.Exists(
        time,
        z3.And(
            semantics.is_valid_time_for_world(eval_world, time),
            eval_time < time,
            semantics.false_at(argument, eval_world, time)
        )
    )
```

### Past Operator (`\Past`)

The past operator `\Past A` also has a purely temporal semantics:

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

```python
def false_at(self, argument, eval_world, eval_time):
    return z3.Exists(
        time,
        z3.And(
            semantics.is_valid_time_for_world(eval_world, time),
            eval_time > time,
            semantics.false_at(argument, eval_world, time)
        )
    )
```

## Important Theorems

The bimodal semantics validates the following important theorems:

1. **Box-Future Theorem**: `\Box A → \Future A`

   - If A is necessarily true, then it is always true in the future

2. **Box-Past Theorem**: `\Box A → \Past A`

   - If A is necessarily true, then it was always true in the past

3. **Possibility-Future Theorem**: `\future A → \Diamond A`

   - If A is possibly true in the future, then A is possible

4. **Possibility-Past Theorem**: `\past A → \Diamond A`
   - If A was possibly true in the past, then A is possible

## Implementation Details

### World and Time Representation

In the bimodal implementation:

- World states are represented as bitvectors (fusions of atomic states)
- Time points are integers (allowing negative times)
- World histories are modeled as arrays mapping time points to world states
- Each world history has a valid time interval within which it is defined
- The time of evaluation is set to `0` where all time-shifted worlds that overlap with `0` are required to exist

### Time Interval Handling

Each world has a valid time interval defined by:

- `world_interval_start(world_id)`: The start time for this world history
- `world_interval_end(world_id)`: The end time for this world history

Time intervals are required to be convex, meaning they have no gaps.

### Abundance Constraint

The abundance constraint ensures that time-shifted worlds exist where needed. For example, if the main world (0) can be shifted forward by 1 time unit, then a world history that is identical but shifted forward by 1 must exist.

This constraint is critical for properly evaluating modal operators, particularly when considering their interaction with temporal operators.

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

The bimodal theory supports several settings:

- `N`: Number of world states (default: 2)
- `M`: Number of time points (default: 2)
- `contingent`: Whether sentence letters are assigned to contingent propositions
- `disjoint`: Whether sentence letters are assigned to distinct world states

Example with custom settings:

```python
settings = {
    'N': 3,        # 3 possible world states
    'M': 4,        # 4 times including time 0
    'contingent': True
}
model = BuildExample("my_example", theory, settings=settings)
```

## Known Limitations

- Performance degrades with many time points or complex formulas
- Z3 timeout can occur for complex models (adjust the `max_time` setting)
- The abundance constraint has significant performance impact
- The full bimodal semantics creates complex models that may challenge Z3's solving capabilities
