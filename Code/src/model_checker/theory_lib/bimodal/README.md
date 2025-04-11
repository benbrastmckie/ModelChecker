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

### Package Contents

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

NOTE: These codeblocks included below are abridged for readability.
Consult the modules above for complete information.

## Basic Usage

> Outline of the `examples.py` module.

### General Definitions

The following are general settings that apply to all examples in `examples.py` and are mostly useful for debugging.

```python
# Default General Settings
general_settings = {
    "print_constraints": False,  # For debugging
    "print_z3": False,  # For debugging
    "save_output": False,
}
```

The following defines the theory that will be used to test examples, consisting of the following four ingredients:

```python
bimodal_theory = {
    "semantics": BimodalSemantics,
    "proposition": BimodalProposition,
    "model": BimodalStructure,
    "operators": intensional_operators,
}
```

Although multiple theories can be used in parallel, at least one theory (such as defined above) must be included in the following:

```python
semantic_theories = {
    "Brast-McKie" : bimodal_theory,
    # additional theories will require translation dictionaries
}
```

### Examples

Each example is structured as a list containing:

1. Premises (list of formulas)
2. Conclusions (list of formulas)
3. Settings dictionary (including N, M, max_time, and crucially, expectation)

Consider the following countermodel:

```python
# Countermodel showing that Future A does not imply Box A
BM_CM_1_premises = ['\\Future A']
BM_CM_1_conclusions = ['\\Box A']
BM_CM_1_settings = {
    'N': 1,
    'M': 2,
    'contingent': False,  # (under construction)
    'disjoint': False,    # (under construction)
    'max_time': 5,
    'expectation': True,  # Expects to find a countermodel
}
BM_CM_1_example = [
    BM_CM_1_premises,
    BM_CM_1_conclusions,
    BM_CM_1_settings,
]
```

Next consider the following theorem:

```python
# Theorem showing that Box A implies Future A
BM_TH_1_premises = ['\\Box A']
BM_TH_1_conclusions = ['\\Future A']
BM_TH_1_settings = {
    'N': 1,
    'M': 2,
    'contingent': False,
    'disjoint': False,
    'max_time': 5,
    'expectation': False,  # Expects NOT to find a countermodel
}
BM_TH_1_example = [
    BM_TH_1_premises,
    BM_TH_1_conclusions,
    BM_TH_1_settings,
]
```

**Key Differences:**
- BM_CM_1 shows that "Future A → Box A" is not valid (has a countermodel)
- BM_TH_1 shows that "Box A → Future A" is valid (no countermodel exists)

### Custom Settings

The bimodal theory supports several configurable settings:

```python
DEFAULT_EXAMPLE_SETTINGS = {
    # Number of world_states
    'N': 2,
    # Number of times
    'M': 2,
    # Whether sentence_letters are assigned to contingent propositions
    'contingent': False,
    # Whether sentence_letters are assigned to distinct world_states
    'disjoint': False,
    # Maximum time Z3 is permitted to look for a model
    'max_time': 1,
    # Whether a model is expected or not (used for unit testing)
    'expectation': True,
}
```

These settings control:

- `N`: Number of possible world states (2^N total possible states)
- `M`: Number of time points in each world history
- `contingent`: Whether sentence letters are assigned to contingent propositions
- `disjoint`: Whether sentence letters are assigned to distinct world states
- `max_time`: Maximum time (in seconds) Z3 is allowed to spend trying to find a model
- `expectation`: Whether a model is expected (used for unit testing)

### Testing

The examples are then collected in dictionaries:

```python
example_range = {
    # Selected examples for current use
    "BM_CM_2": BM_CM_2_example,
    "BM_TH_1": BM_TH_1_example,
}
```

The `semantic_theories` and `example_range` are then processed by the model-checker along with `general_settings`.

```python
test_example_range = {
    # All examples for testing
    "BM_CM_1": BM_CM_1_example,
    "BM_TH_1": BM_TH_1_example,
    # ... more examples
}
```

The `test_example_range` automates unit testing and will not play a role when `model-checker examples.py` is run.

### Necessity Operator (`\Box`)

The necessity operator (`\Box`) evaluates whether a formula holds across all possible worlds at a given time.

This operator implements 'it is necessarily the case that'.
It evaluates whether its argument is true in every possible world at the evaluation time.

Key Properties:
- Evaluates truth across all possible worlds at a fixed time
- Returns true only if the argument is true in ALL possible worlds
- Returns false if there exists ANY possible world where the argument is false
- Purely modal (not temporal) - evaluates across worlds at a single time point

#### Truth Condition

`\Box A` is true at world `w` at time `t` if and only if A is true in all possible worlds at time `t`.

```python
def true_at(self, argument, eval_world, eval_time):
    return z3.ForAll(
        other_world,
        z3.Implies(
            semantics.is_world(other_world),
            semantics.true_at(argument, other_world, eval_time)
        )
    )
```

#### Falsity Condition

`\Box A` is false at world `w` at time `t` if and only if A is false in at least one possible world at time `t`.

```python
def false_at(self, argument, eval_world, eval_time):
    return z3.Exists(
        other_world,
        z3.And(
            semantics.is_world(other_world),
            semantics.false_at(argument, other_world, eval_time)
        )
    )
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
2. **Box-Past Theorem**: `\Box A → \Past A`
   - If A is necessarily true, then it was always true in the past
3. **Possibility-Future Theorem**: `\future A → \Diamond A`
   - If A is possibly true in the future, then A is possible
4. **Possibility-Past Theorem**: `\past A → \Diamond A`
   - If A was possibly true in the past, then A is possible
   - This theorem connects past possibility to general possibility

## Implementation Details

### World and Time Representation

The bimodal implementation uses these key representations:

- **World states**: Represented as bitvectors (fusions of atomic states)
- **World IDs**: Integer identifiers for world histories (starting at 0)
- **Time points**: Integers allowing negative, zero, and positive values
- **World histories**: Arrays mapping time points to world states
- **Time intervals**: Each world history has a valid interval within which it's defined
- **Evaluation point**: Fixed at world ID 0, time 0

The semantic model defines several Z3 sorts used throughout the implementation:

```python
# Define the Z3 sorts used in the bimodal logic model
self.WorldStateSort = z3.BitVecSort(self.N)  # World states as bitvectors
self.TimeSort = z3.IntSort()                 # Time points as integers
self.WorldIdSort = z3.IntSort()              # World IDs as integers
```

### Time-Shift Relations

Each world has a valid time interval defined by two functions:

```python
# Define interval tracking functions
self.world_interval_start = z3.Function(
    'world_interval_start',
    self.WorldIdSort,  # World ID
    self.TimeSort      # Start time of interval
)

self.world_interval_end = z3.Function(
    'world_interval_end',
    self.WorldIdSort,  # World ID
    self.TimeSort      # End time of interval
)
```

Time intervals are required to be convex (no gaps) and are generated within the range [-M+1, M-1]:

```python
def generate_time_intervals(self, M):
    """Generate all valid time intervals of length M that include time 0."""
    intervals = []
    for start in range(-M+1, 1):  # Start points from -M+1 to 0
        end = start + M - 1       # Each interval has exactly M time points
        intervals.append((start, end))
    return intervals
```

### World Function and Task Relation

The core of the bimodal implementation includes:

1. The world function that maps world IDs to their history arrays:

```python
# Mapping from world IDs to world histories (arrays from time to state)
self.world_function = z3.Function(
    'world_function',
    self.WorldIdSort,                          # Input: world ID
    z3.ArraySort(self.TimeSort, self.WorldStateSort)  # Output: world history
)
```

2. The task relation specifying valid transitions between world states:

```python
# Define the task relation between world states
self.task = z3.Function(
    "Task",
    self.WorldStateSort,  # From state
    self.WorldStateSort,  # To state
    z3.BoolSort()         # Is valid transition?
)
```

The model extraction process follows these steps:

The Skolem abundance constraint ensures that time-shifted worlds exist where needed. This optimization uses Skolem functions to directly define the shifted worlds:

```python
# Define Skolem functions that directly compute the necessary worlds
forward_of = z3.Function('forward_of', self.WorldIdSort, self.WorldIdSort)
backward_of = z3.Function('backward_of', self.WorldIdSort, self.WorldIdSort)
```

For example, if world ID 0 can be shifted forward by 1, then the world `forward_of(0)` must exist and must be a properly time-shifted version of world 0.

This constraint is critical for correctly modeling the interaction between modal and temporal operators in bimodal logic.

### Model Extraction Process

The model extraction process follows these steps:

1. Extract valid world IDs (`_extract_valid_world_ids`)
2. Extract world arrays for each world ID (`_extract_world_arrays`)
3. Extract time intervals for each world (`_extract_time_intervals`)
4. Build time-state mappings for each world history (`_extract_world_histories`)
5. Determine time-shift relations between worlds (`_extract_time_shift_relations`)

This highly structured extraction process helps manage the complexity of bimodal models.

## Frame Constraints

The bimodal logic is defined by the following key frame constraints that determine the structure of models, as implemented in `build_frame_constraints()`:

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
classical_truth = z3.ForAll(
    [world_state, sentence_letter],
    z3.Or(
        # Either sentence_letter is true in the world_state
        self.truth_condition(world_state, sentence_letter),
        # Or not
        z3.Not(self.truth_condition(world_state, sentence_letter))
    )
)
```

### 4. World Enumeration Constraint

World histories must be enumerated in sequence starting from 0.

```python
enumeration_constraint = z3.ForAll(
    [enumerate_world],
    z3.Implies(
        # If enumerate_world is a world
        self.is_world(enumerate_world),
        # Then it's non-negative
        enumerate_world >= 0,
    )
)
```

### 5. Convex World Ordering Constraint

There can be no gaps in the enumeration of worlds, ensuring worlds are created in sequence.

```python
convex_world_ordering = z3.ForAll(
    [convex_world],
    z3.Implies(
        # If both:
        z3.And(
            # The convex_world is a world
            self.is_world(convex_world),
            # And greater than 0
            convex_world > 0,
        ),
        # Then world_id - 1 must be valid
        self.is_world(convex_world - 1)
    )
)
```

### 6. Lawful Transition Constraint

Each world history must follow lawful transitions between consecutive states.

```python
lawful = z3.ForAll(
    [lawful_world, lawful_time],
    # If for any lawful_world and lawful time
    z3.Implies(
        z3.And(
            # The lawful_world is a valid world
            self.is_world(lawful_world),
            # The lawful_time is in (-M - 1, M - 1), so has a successor
            self.is_valid_time(lawful_time, -1),
            # The lawful_time is in the lawful_world
            self.is_valid_time_for_world(lawful_world, lawful_time),
            # The successor of the lawful_time is in the lawful_world
            self.is_valid_time_for_world(lawful_world, lawful_time + 1),
        ),
        # Then there is a task
        self.task(
            # From the lawful_world at the lawful_time
            z3.Select(self.world_function(lawful_world), lawful_time),
            # To the lawful_world at the successor of the lawful_time
            z3.Select(self.world_function(lawful_world), lawful_time + 1)
        )
    )
)
```

### 8. Skolem Abundance Constraint

An optimized version of the abundance constraint using Skolem functions to eliminate nested quantifiers, improving Z3 performance.

```python
# Define Skolem functions that directly compute the necessary worlds
forward_of = z3.Function('forward_of', self.WorldIdSort, self.WorldIdSort)
backward_of = z3.Function('backward_of', self.WorldIdSort, self.WorldIdSort)

# Use Skolem functions instead of existential quantifiers
return z3.ForAll(
    [source_world],
    z3.Implies(
        # If the source_world is a valid world
        self.is_world(source_world),
        # Then both:
        z3.And(
            # Forwards condition - if source can shift forward
            z3.Implies(
                self.can_shift_forward(source_world),
                z3.And(
                    # The forward_of function must produce a valid world
                    self.is_world(forward_of(source_world)),
                    # The produced world must be properly shifted
                    self.is_shifted_by(source_world, 1, forward_of(source_world))
                )
            ),
            # Backwards condition - if source can shift backwards
            z3.Implies(
                self.can_shift_backward(source_world),
                z3.And(
                    # The backward_of function must produce a valid world
                    self.is_world(backward_of(source_world)),
                    # The produced world must be properly shifted
                    self.is_shifted_by(source_world, -1, backward_of(source_world))
                )
            )
        )
    )
)
```

### 8. World Uniqueness Constraint

No two worlds can have identical histories over their entire intervals.

```python
world_uniqueness = z3.ForAll(
    [world_one, world_two],
    z3.Implies(
        z3.And(
            self.is_world(world_one),
            self.is_world(world_two),
            world_one != world_two
        ),
        # Worlds must differ at some time point that is valid for both
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

### 9. Time Interval Constraint

An optimized version of the world interval constraint that directly defines interval bounds for each world.

```python
# Generate valid time intervals
time_intervals = self.generate_time_intervals(self.M)

# Create direct mapping for interval bounds
interval_constraints = []

# For each valid world ID, create direct interval constraints
for world_id in range(self.max_world_id):
    # A world must have exactly one of the valid intervals if it exists
    world_constraint = z3.Implies(
        self.is_world(world_id),
        z3.Or(*world_interval_options)
    )

    interval_constraints.append(world_constraint)

# Combine all world constraints
return z3.And(*interval_constraints)
```

### Additional Optional Constraints

The semantic model also defines several optional constraints that can be enabled as needed:

#### Task Restriction Constraint

Ensures the task relation only holds between states in lawful world histories.

```python
task_restriction = z3.ForAll(
    [some_state, next_state],
    z3.Implies(
        # If there is a task from some_state to next_state
        self.task(some_state, next_state),
        # Then for some task_world at time_shifted:
        z3.Exists(
            [task_world, time_shifted],
            z3.And(
                # The task_world is a valid world
                self.is_world(task_world),
                # The successor or time_shifted is a valid time
                self.is_valid_time(time_shifted, -1),
                # Where time_shifted is a time in the task_world,
                self.is_valid_time_for_world(task_world, time_shifted),
                # The successor of time_shifted is a time in the task_world
                self.is_valid_time_for_world(task_world, time_shifted + 1),
                # The task_world is in some_state at time_shifted
                some_state == z3.Select(self.world_function(task_world), time_shifted),
                # And the task_world is in next_state at the successor of time_shifted
                next_state == z3.Select(self.world_function(task_world), time_shifted + 1)
            )
        )
    )
)
```

#### Task Minimization Constraint

Guides Z3 to prefer solutions where consecutive world states are identical when possible, reducing unnecessary state changes.

```python
task_minimization = z3.ForAll(
    [world_id, time_point],
    z3.Implies(
        z3.And(
            self.is_world(world_id),
            self.is_valid_time_for_world(world_id, time_point),
            self.is_valid_time_for_world(world_id, time_point + 1)
        ),
        # Encourage identical states if possible (soft constraint)
        z3.Select(self.world_function(world_id), time_point) ==
        z3.Select(self.world_function(world_id), time_point + 1)
    )
)
```

The frame constraints are applied in a specific order to guide Z3's model search efficiently.

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
