# Models: SMT Solving and Result Interpretation

[← Semantics Pipeline](SEMANTICS.md) | [Back to Architecture](README.md) | [Workflow →](WORKFLOW.md)

## Table of Contents

1. [Introduction](#introduction)
2. [SMT Solver Setup](#smt-solver-setup)
   - [Solver Initialization](#solver-initialization)
   - [Context Management](#context-management)
   - [Constraint Tracking](#constraint-tracking)
   - [Timeout Configuration](#timeout-configuration)
   - [Unsat Core Extraction](#unsat-core-extraction)
   - [State Isolation](#state-isolation)
   - [Future Extensibility](#future-extensibility)
3. [Constraint Organization](#constraint-organization)
   - [Frame Constraints](#frame-constraints)
   - [Model Constraints](#model-constraints)
   - [Premise Constraints](#premise-constraints)
   - [Conclusion Constraints](#conclusion-constraints)
   - [Constraint Tracking](#constraint-tracking-1)
   - [Constraint Dictionary](#constraint-dictionary)
4. [Model Finding Process](#model-finding-process)
   - [Solver Execution](#solver-execution)
   - [Satisfiability Checking](#satisfiability-checking)
   - [Model Extraction](#model-extraction)
   - [Timeout Handling](#timeout-handling)
   - [Resource Cleanup](#resource-cleanup)
   - [Solver-Agnostic Interface](#solver-agnostic-interface)
5. [ModelDefaults and Theory Structures](#modeldefaults-and-theory-structures)
   - [Model Structure Creation](#model-structure-creation)
   - [Model Differences Tracking](#model-differences-tracking)
6. [Extension Assignment](#extension-assignment)
   - [SMT Model Interpretation](#smt-model-interpretation)
   - [State Extraction](#state-extraction)
   - [Main World Assignment](#main-world-assignment)
   - [Verify/Falsify Relations](#verifyfalsify-relations)
   - [Verifier/Falsifier Sets](#verifierfalsifier-sets)
   - [World State Identification](#world-state-identification)
   - [Evaluation Point Setup](#evaluation-point-setup)
   - [State Representation](#state-representation)
7. [Sentence Interpretation](#sentence-interpretation)
   - [Proposition Update Process](#proposition-update-process)
   - [Recursive Evaluation](#recursive-evaluation)
   - [Truth Value Determination](#truth-value-determination)
   - [Model Structure Population](#model-structure-population)
8. [Output Generation](#output-generation)
   - [Model Visualization](#model-visualization)
   - [Extension Display](#extension-display)
   - [Evaluation Results](#evaluation-results)
   - [Countermodel Formatting](#countermodel-formatting)
   - [Color Coding](#color-coding)
9. [Code Examples](#code-examples)
10. [References](#references)

## Introduction

The models module handles the final stage of the model checking pipeline: solving SMT constraints and interpreting the results. Using Z3 as the current SMT solver implementation, it finds satisfying assignments that demonstrate countermodels to logical arguments or proves their validity through unsatisfiability.

This stage represents the culmination of the semantic pipeline - all the careful parsing and constraint generation comes together here, where the SMT solver determines whether the collected constraints can be simultaneously satisfied. If they can, we get a countermodel showing the argument is invalid; if not, the argument is valid.

Key architectural insights:

- **Solver Isolation**: Each example gets a fresh solver context to prevent constraint contamination
- **Result Interpretation**: Raw solver output is transformed into structured semantic models
- **Theory Independence**: The solving process works identically across different semantic theories
- **Performance Tuning**: Timeout and resource management prevent infinite loops on complex problems

The module is designed with future extensibility in mind, abstracting solver-specific operations to allow potential integration with other SMT solvers like CVC5. The result is either a concrete model showing why an argument is invalid or proof that no such countermodel exists.

For the constraint generation that feeds into this stage, see [Semantics Pipeline](SEMANTICS.md). For practical usage patterns, see [Workflow](WORKFLOW.md).

## SMT Solver Setup

The SMT solver setup orchestrates the transformation from semantic constraints to satisfiability checking:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         SMT SOLVER PIPELINE                             │
└─────────────────────────────────────────────────────────────────────────┘

1. CONSTRAINT COLLECTION           2. SOLVER SETUP
┌──────────────────────────┐           ┌───────────────────────┐
│ ModelConstraints         │           │ Fresh Z3 Context      │
│ • Frame constraints      │           │ • Reset global state  │
│ • Model constraints      │ ────────▶ │ • New solver instance │
│ • Premise constraints    │           │ • Add with tracking   │
│ • Conclusion constraints │           └───────────────────────┘
└──────────────────────────┘                     │
                                                 ▼
                                       ┌───────────────────────┐
                                       │ 3. SOLVING PROCESS    │
                                       │ • Set timeout         │
                                       │ • Check satisfiability│
                                       │ • Handle resources    │
                                       └───────────────────────┘
                                                 │
                                                 ▼
                                       ┌──────────────────────┐
                                       │ 4. RESULT PROCESSING │
                                       │ • SAT: Extract model │
                                       │ • UNSAT: Get core    │
                                       │ • UNKNOWN: Timeout   │
                                       └──────────────────────┘
```

**Add with tracking**: Constraints are added using Z3's `assert_and_track(constraint, label)` method instead of plain `assert`. This associates each constraint with a tracking label (e.g., "frame1", "model5", "premises2") that enables unsat core analysis. When constraints are unsatisfiable, the unsat core tells you exactly which labeled constraints conflict - invaluable for debugging semantic theories.

**Handle resources**: Manages solver timeouts, memory cleanup, and state isolation. This includes setting time limits to prevent infinite loops, cleaning up Z3 objects to prevent memory leaks, and ensuring complete state isolation between examples to avoid contamination from previous solving attempts.

### Solver Initialization

Each example gets a fresh solver instance to ensure isolation:

```python
def solve(self, model_constraints, max_time):
    """Create fresh Z3 context for solving."""
    import z3

    # Reset context for complete isolation
    Z3ContextManager.reset_context()  # Clears any lingering state from previous examples

    # Create new solver instance
    self.solver = z3.Solver()  # Fresh solver with no constraints

    # Setup solver with constraints
    self.solver = self._setup_solver(model_constraints)  # Add all constraint types
```

The fresh solver approach prevents a subtle but critical issue: without isolation, constraints from one example could "leak" into another, causing false unsatisfiability or incorrect models. This is especially important when comparing theories - each theory needs to evaluate the same example from a clean slate, without interference from previous solving attempts.

### Context Management

Z3 context management ensures no state leakage between examples:

```python
class Z3ContextManager:
    """Manages Z3 context lifecycle."""

    @staticmethod
    def reset_context():
        """Reset Z3 to clean state."""
        import z3

        # Clear any existing context
        if hasattr(z3, '_main_ctx'):
            z3._main_ctx = None  # Z3's global context object

        # Force garbage collection
        import gc
        gc.collect()  # Ensures old solver objects are truly freed

        # Reset parameters
        z3.reset_params()  # Clear any modified solver parameters
        z3.set_param(verbose=0)  # Silence Z3's internal debug output
```

_Full implementation: [`model_checker/utils.py`](../../Code/src/model_checker/utils.py)_

Z3 maintains a global context (`_main_ctx`) that persists across solver instances. Without explicit clearing, this context accumulates state - variable declarations, function definitions, and internal optimizations from previous solving sessions. The garbage collection step ensures Python releases all references to old solver objects, preventing memory leaks during batch processing of many examples.

### Constraint Tracking

Constraints are added with labels for debugging:

```python
def _setup_solver(self, model_constraints):
    """Add constraints with tracking labels."""
    solver = Solver()
    self.constraint_dict = {}  # Maps labels to original constraints

    constraint_groups = [
        (model_constraints.frame_constraints, "frame"),      # Semantic structure
        (model_constraints.model_constraints, "model"),      # Atomic propositions
        (model_constraints.premise_constraints, "premises"),  # Must be true
        (model_constraints.conclusion_constraints, "conclusions")  # At least one false
    ]

    for constraints, group_name in constraint_groups:
        for ix, constraint in enumerate(constraints):
            c_id = f"{group_name}{ix+1}"  # e.g., "frame1", "model5", "premises2"
            solver.assert_and_track(constraint, c_id)  # Label enables unsat core tracking
            self.constraint_dict[c_id] = constraint    # Store for later analysis

    return solver
```

The `assert_and_track` method differs from plain `assert` in a crucial way: it associates each constraint with a tracking literal that Z3 includes in its unsat core analysis. When constraints are unsatisfiable, the unsat core tells us exactly which constraints conflict - invaluable for debugging semantic theories. The labeling scheme ("frame1", "model5", etc.) immediately reveals which type of constraint causes issues.

### Timeout Configuration

Solver timeout prevents infinite loops:

```python
# Set timeout in milliseconds
max_time_ms = int(max_time * 1000)  # Convert seconds to milliseconds
self.solver.set("timeout", max_time_ms)  # Z3 parameter for solving time limit

# Check result
result = self.solver.check()  # Blocks until solution, timeout, or memory exhaustion

# Handle timeout
if self.solver.reason_unknown() == "timeout":  # Z3 stopped due to time limit
    return self._create_result(
        True,        # timeout_occurred
        None,        # no_model
        False,       # not_satisfiable
        start_time   # for_runtime_calculation
    )
```

The timeout mechanism serves two purposes: it prevents the solver from running indefinitely on complex problems, and it provides predictable performance bounds for batch processing. Complex theories with many constraints might need longer timeouts - the default of 10 seconds works for most examples, but counterfactual reasoning or fine-grained hyperintensional distinctions may require 30-60 seconds.

### Unsat Core Extraction

For unsatisfiable constraints, extract minimal conflicting set:

```python
if result == z3.unsat:
    # Get unsat core - minimal set of conflicting constraints
    unsat_core = self.solver.unsat_core()  # Returns tracking literals, not constraints

    # Map back to original constraints
    core_constraints = [
        self.constraint_dict[str(c)]   # Look up constraint by its tracking label
        for c in unsat_core            # e.g., "frame1", "model5", "premises2"
    ]

    return self._create_result(
        False,            # no_timeout
        core_constraints, # conflicting_constraints (for debugging)
        False,            # not_satisfiable
        start_time        # for_runtime_calculation
    )
```

The unsat core is a minimal subset of constraints that are mutually unsatisfiable - removing any constraint from this set would make the remaining constraints satisfiable. This is invaluable for debugging: if "frame1" (possibility downward closure) conflicts with "model3" (contingency requirement), you immediately know where to look. The core often reveals subtle interactions between semantic principles that wouldn't be obvious from examining constraints individually.

### State Isolation

Complete cleanup after solving:

```python
def _cleanup_solver_resources(self):
    """Ensure complete isolation between examples."""
    # Remove solver references
    self.solver = None
    self.z3_model = None

    # Clear constraint tracking
    self.constraint_dict = {}

    # Force cleanup in finally block
    try:
        result = self.solver.check()
    finally:
        self._cleanup_solver_resources()
```

The cleanup is critical because Z3 maintains internal references to solver objects and constraint variables that persist across solving sessions. Without explicit cleanup, these references accumulate in memory, causing performance degradation and potential memory exhaustion when processing hundreds of examples. The finally block ensures cleanup happens even if solving throws an exception.

### Future Extensibility

Abstract interface for multiple solvers:

```python
# Future solver interface
class SMTSolver:
    """Abstract interface for SMT solvers."""

    def add_constraint(self, constraint, label=None):
        """Add constraint to solver."""

    def check_satisfiability(self, timeout=None):
        """Check if constraints are satisfiable."""

    def get_model(self):
        """Extract satisfying assignment."""

    def get_unsat_core(self):
        """Get minimal unsatisfiable subset."""

# Concrete implementations
class Z3Solver(SMTSolver):
    """Z3-specific implementation."""

class CVC5Solver(SMTSolver):
    """CVC5-specific implementation."""
```

This abstract interface pattern allows the framework to support multiple SMT solvers without changing the core logic. The base `SMTSolver` class defines the methods that any solver must implement. Concrete classes like `Z3Solver` provide the actual implementation. This means we could switch from Z3 to CVC5 by simply changing which concrete class we instantiate - all the rest of the code remains unchanged because it only depends on the abstract interface.

## Constraint Organization

The constraint generation process is fully documented in [SEMANTICS.md](SEMANTICS.md). As a reminder, the solver receives four types of constraints from the semantic stage:

1. **Frame constraints** - Define the semantic structure (possibility, worlds, compatibility)
2. **Model constraints** - Atomic proposition properties (classical, contingent, non-empty)
3. **Premise constraints** - Ensure all premises are true at the main world
4. **Conclusion constraints** - Require at least one conclusion to be false

Each constraint type is tracked with labels for debugging purposes:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      CONSTRAINT HIERARCHY                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. FRAME CONSTRAINTS (Semantic Structure)                              │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ • Possibility downward closure: possible(y) ∧ x≤y → possible(x)    │ │
│  │ • Main world exists: is_world(w) ∧ possible(w)                     │ │
│  │ • Compatibility symmetry: compatible(x,y) ↔ compatible(y,x)        │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                              ↓                                          │
│  2. MODEL CONSTRAINTS (Atomic Propositions)                             │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ For each sentence letter A:                                        │ │
│  │ • Classical: fusion closure, no gaps/gluts                         │ │
│  │ • Contingent: ∃x(possible(x) ∧ verify(x,A))                        │ │
│  │ • Non-empty: ∃x(verify(x,A)) ∧ ∃y(falsify(y,A))                    │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                              ↓                                          │
│  3. PREMISE CONSTRAINTS (Must be True)                                  │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ For each premise P:                                                │ │
│  │ • true_at(main_world, P, main_point)                               │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                              ↓                                          │
│  4. CONCLUSION CONSTRAINTS (At Least One False)                         │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ • Or([false_at(main_world, C, main_point) for C in conclusions])   │ │
│  └────────────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────────┘
```

### Frame Constraints

Structural constraints defining the semantic framework:

```python
# Example frame constraints from Logos
frame_constraints = [
    # Possibility is downward-closed
    ForAll([x, y],
        Implies(
            And(possible(y), is_part_of(x, y)),  # If y is possible and x is part of y
            possible(x)                          # Then x must be possible too
        )
    ),
    # Main world exists and is possible
    is_world(main_world),  # Ensures w is maximal (no proper extensions)
    # State compatibility is symmetric
    ForAll([x, y],
        compatible(x, y) == compatible(y, x)  # If x fits with y, then y fits with x
    )
]
```

Frame constraints establish the fundamental properties of the semantic space. The downward closure principle ensures coherence: you can't have impossible parts of possible wholes. This reflects the intuition that if a complex situation is possible, all its constituent parts must be possible too. The main world constraint guarantees we're evaluating formulas at a genuine possible world, not some arbitrary partial state.

### Model Constraints

Constraints from atomic propositions:

```python
# For each sentence letter
for letter in sentence_letters:
    # Classical constraints
    constraints.extend([
        verifier_fusion_closure(letter),
        falsifier_fusion_closure(letter),
        no_gluts(letter),
        no_gaps(letter)
    ])

    # Setting-based constraints
    if settings['contingent']:
        constraints.extend([
            possible_verifier(letter),
            possible_falsifier(letter)
        ])
```

### Premise Constraints

All premises must be true at evaluation point:

```python
premise_constraints = []
for premise in premises:
    # Premise is true at main world
    constraint = true_at(main_world, premise, main_point)
    premise_constraints.append(constraint)
```

### Conclusion Constraints

At least one conclusion must be false:

```python
# Invalidity requires false conclusion
false_conclusions = []
for conclusion in conclusions:
    constraint = false_at(main_world, conclusion, main_point)
    false_conclusions.append(constraint)

# Disjunction - at least one false
conclusion_constraint = Or(false_conclusions)
```

### Constraint Tracking

Labels enable debugging and analysis:

```python
# Add with tracking
solver.assert_and_track(constraint, "frame1")
solver.assert_and_track(constraint, "model5")
solver.assert_and_track(constraint, "premises2")
solver.assert_and_track(constraint, "conclusions1")

# Later analysis
if unsat:
    core = solver.unsat_core()
    print(f"Conflict in: {[str(c) for c in core]}")
```

### Constraint Dictionary

Maps labels to original constraints:

```python
self.constraint_dict = {
    "frame1": possibility_downward_closure,
    "frame2": main_world_exists,
    "model1": classical_A,
    "model2": contingent_A,
    "premises1": A_and_B_true,
    "conclusions1": C_false
}
```

## Model Finding Process

The model finding process transforms constraints into concrete semantic structures:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        MODEL FINDING FLOW                               │
└─────────────────────────────────────────────────────────────────────────┘

                    ┌─────────────────────┐
                    │ All Constraints     │
                    │ • Frame (~3-5)      │
                    │ • Model (~15-60)    │
                    │ • Premises (~1-5)   │
                    │ • Conclusions (1)   │
                    └──────────┬──────────┘
                               │
                               ▼
                    ┌─────────────────────┐
                    │ Z3 Solver.check()   │
                    │ • Apply heuristics  │
                    │ • Search for model  │
                    │ • Track time/memory │
                    └──────────┬──────────┘
                               │
                ┌──────────────┼──────────────┐
                │              │              │
                ▼              ▼              ▼
       ┌──────────────┐ ┌─────────────┐ ┌─────────────┐
       │ SAT          │ │ UNSAT       │ │ UNKNOWN     │
       │ • Model found│ │ • No model  │ │ • Timeout   │
       │ • Extract    │ │ • Get core  │ │ • Memory    │
       │   assignments│ │ • Valid arg │ │   limit     │
       └──────────────┘ └─────────────┘ └─────────────┘
```

### Solver Execution

Complete solving pipeline:

```python
def solve(self, model_constraints, max_time):
    """Execute solver and return results."""
    # Setup
    solver = self._setup_solver(model_constraints)
    solver.set("timeout", int(max_time * 1000))

    # Solve
    start_time = time.time()
    result = solver.check()
    runtime = time.time() - start_time

    # Process results
    if result == z3.sat:
        return (False, solver.model(), True, runtime)
    elif solver.reason_unknown() == "timeout":
        return (True, None, False, runtime)
    else:  # unsat
        return (False, solver.unsat_core(), False, runtime)
```

The `solve` method orchestrates the complete solving process. SAT solving determines whether a set of logical constraints can all be satisfied simultaneously. The solver returns a tuple: (timeout_occurred, model_or_core, is_satisfiable, runtime). If satisfiable (SAT), we get a model - concrete values for all variables that make all constraints true. If unsatisfiable (UNSAT), the argument is valid because no countermodel exists. The unsat core returned helps debug which constraints conflict.

### Satisfiability Checking

Three possible outcomes:

```python
result = solver.check()

# 1. Satisfiable - countermodel found
if result == z3.sat:
    model = solver.model()
    # Extract assignments

# 2. Unsatisfiable - argument is valid
elif result == z3.unsat:
    core = solver.unsat_core()
    # Analyze conflict

# 3. Unknown - typically timeout
else:
    reason = solver.reason_unknown()
    # Handle timeout or other issues
```

SAT solving has three possible outcomes. **SAT (satisfiable)** means the solver found values that satisfy all constraints - we have a countermodel showing the argument is invalid. **UNSAT (unsatisfiable)** means no such values exist - the constraints conflict, proving the argument valid. **UNKNOWN** typically means the solver hit its time limit before finding an answer, though it can also indicate memory exhaustion or numerical overflow in complex problems.

### Model Extraction

Extract satisfying assignments from Z3:

```python
if z3_model_status:
    # Extract state assignments
    for state in all_states:
        for letter in sentence_letters:
            # Get verify/falsify values
            verifies = z3_model.evaluate(verify(state, letter))
            falsifies = z3_model.evaluate(falsify(state, letter))

    # Extract world states
    main_world_value = z3_model.evaluate(main_world)
    possible_states = [
        state for state in all_states
        if z3_model.evaluate(possible(state))
    ]
```

When Z3 finds a satisfying model, we extract the concrete values it assigned to our semantic functions. The `evaluate` method takes a Z3 expression and returns its value in the model. For each state and sentence letter, we check whether the model assigns true to `verify(state, letter)` and `falsify(state, letter)`. This builds up the complete picture of which states verify or falsify which propositions, giving us the countermodel structure.

### Timeout Handling

Graceful handling of solver timeouts:

```python
# Set conservative timeout
solver.set("timeout", max_time * 1000)

# Check if timeout occurred
if solver.reason_unknown() == "timeout":
    self.timeout = True
    self.z3_model = None
    self.z3_model_status = False
    print(f"Solver timed out after {max_time}s")

    # Optionally try with increased time
    if retry_on_timeout:
        max_time *= 2
        return self.solve(model_constraints, max_time)
```

Timeouts are crucial for practical SAT solving because satisfiability is NP-complete - some problems take exponential time. The timeout prevents the solver from running forever on hard instances. When a timeout occurs, we can optionally retry with more time, but this is a tradeoff: longer timeouts find more countermodels but slow down batch processing. Most examples solve in under a second, but complex theories may need 30-60 seconds.

### Resource Cleanup

Ensure proper resource management:

```python
try:
    # Solver operations
    solver = self._setup_solver(model_constraints)
    result = solver.check()

except Exception as e:
    # Handle errors
    print(f"Solver error: {e}")
    return (True, None, False, None)

finally:
    # Always cleanup
    self._cleanup_solver_resources()
    solver = None
```

The try-finally pattern ensures resources are always cleaned up, even if the solver crashes or throws an exception. This is critical in SAT solving because solvers allocate significant memory for internal data structures (clause databases, variable watches, learned clauses). Without proper cleanup, this memory leaks between examples, eventually exhausting system resources. The finally block guarantees cleanup runs regardless of success or failure.

### Solver-Agnostic Interface

Design for future solver support:

```python
# Abstract result structure
SolverResult = {
    'status': 'sat' | 'unsat' | 'unknown',
    'model': dict | None,          # Variable assignments
    'unsat_core': list | None,     # Conflicting constraints
    'runtime': float,              # Solving time
    'reason': str | None           # For unknown status
}

# Solver-independent model extraction
def extract_model_values(solver_result):
    """Extract values regardless of solver."""
    if solver_result['status'] != 'sat':
        return None

    model = solver_result['model']
    return {
        'states': extract_states(model),
        'relations': extract_relations(model),
        'functions': extract_functions(model)
    }
```

This standardized result format decouples the framework from specific solver implementations. Any SMT solver (Z3, CVC5, Yices) can return results in this format, and the rest of ModelChecker doesn't need to know which solver was used. The `extract_model_values` function further abstracts model extraction - it takes the solver-specific model format and converts it to a uniform dictionary structure that the framework understands, enabling true solver independence.

## ModelDefaults and Theory Structures

ModelDefaults provides the base infrastructure for solving and interpreting models, while theory-specific subclasses add specialized extraction and display logic:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    MODEL STRUCTURE HIERARCHY                            │
└─────────────────────────────────────────────────────────────────────────┘

                         ┌─────────────────────┐
                         │   ModelDefaults     │
                         │ • Solve constraints │
                         │ • Extract states    │
                         │ • Basic display     │
                         └──────────┬──────────┘          Aditional theories...
                                    │ Inheritance
        ┌───────────────────────────┼───────────────────────────┬────────── ...
        │                           │                           │
        ▼                           ▼                           ▼
┌────────────────────┐ ┌───────────────────────┐ ┌────────────────────────┐
│ LogosModelStructure│ │ExclusionModelStructure│ │ImpositionModelStructure│
│ • Verifier sets    │ │ • Exclusion relation  │ │ • Selection function   │
│ • Falsifier sets   │ │ • Unilateral verify   │ │ • Comparative sim.     │ ...
│ • Hyperintensional │ │ • Topic sensitivity   │ │ • Counterfactuals      │
└────────────────────┘ └───────────────────────┘ └────────────────────────┘
```

### Model Structure Creation

ModelDefaults manages the solving pipeline:

```python
class ModelDefaults:
    """Core model structure and solving."""

    def __init__(self, model_constraints, settings):
        # Store components
        self.model_constraints = model_constraints
        self.semantics = model_constraints.semantics
        self.settings = settings

        # Extract key elements
        self.N = self.semantics.N
        self.all_states = self.semantics.all_states
        self.main_point = self.semantics.main_point

        # Solve constraints
        solver_results = self.solve(model_constraints, settings['max_time'])
        self._process_solver_results(solver_results)
```

The ModelDefaults constructor sets up the solving infrastructure. It stores the constraint collection and settings, extracts key semantic elements like the number of atomic propositions (N) and all possible states, then immediately calls the solver. The `_process_solver_results` method interprets the solver's output, storing either the satisfying model or information about why no model was found. This design makes ModelDefaults a complete, self-contained solving engine.

_Full implementation: [`model_checker/model.py`](../../Code/src/model_checker/model.py)_

### Model Differences Tracking

For tracking differences between models during iteration:

```python
def track_model_differences(self, other_model):
    """Track differences between two models."""
    differences = {
        'states': self.z3_possible_states != other_model.z3_possible_states,
        'worlds': self.z3_world_states != other_model.z3_world_states,
        'main_world': self.main_world_value != other_model.main_world_value
    }
    return differences
```

This functionality is primarily used by the iteration system to ensure distinct models are found. See [Iterator System](ITERATE.md) for complete details on model iteration.

## Extension Assignment

### SMT Model Interpretation

Convert Z3 model to usable structure:

```python
def _process_solver_results(self, solver_results):
    """Process raw solver output."""
    timeout, z3_model, status, runtime = solver_results

    self.timeout = timeout
    self.z3_model_status = status
    self.z3_model_runtime = runtime

    if status:
        self.z3_model = z3_model
        self._extract_model_structure()
    else:
        self.unsat_core = z3_model
```

This method unpacks the solver results tuple and branches based on satisfiability status. If a model was found (status=True), it stores the Z3 model object and extracts the semantic structure. If no model exists (status=False), it stores the unsat core for debugging. The timeout flag and runtime are always recorded for performance analysis. This separation of concerns keeps the solving logic clean and the model interpretation organized.

### State Extraction

Identify possible states and world states:

```python
def _extract_model_structure(self):
    """Extract semantic structure from Z3 model."""
    # Find possible states
    self.z3_possible_states = {
        state for state in self.all_states
        if self.z3_model.evaluate(self.semantics.possible(state))
    }

    # Find world states
    self.z3_world_states = {
        state for state in self.z3_possible_states
        if self.z3_model.evaluate(self.semantics.is_world(state))
    }

    # Extract main world value
    self.main_world_value = self.z3_model.evaluate(self.main_world)
```

This extraction process converts Z3's internal model representation into Python data structures. First, it finds all states marked as possible by the model. Then it filters these to find world states (maximal consistent states). Finally, it extracts the specific world chosen as the main evaluation point. These sets form the foundation for interpreting formulas - we need to know which states exist and which are worlds to properly evaluate truth conditions.

### Main World Assignment

Identify evaluation world:

```python
# Extract main world from model
main_world_bitvec = z3_model.evaluate(semantics.main_world)

# Convert to integer for display
main_world_int = main_world_bitvec.as_long()

# Create evaluation point
self.main_point = {
    "world": main_world_bitvec
}

# Display representation
main_world_str = bitvec_to_worldstate(main_world_int)
print(f"Main world: {main_world_str}")
```

The main world extraction demonstrates the conversion from Z3's internal bit vector representation to human-readable format. Z3 represents states as bit vectors for efficiency, but we need readable strings for output. The evaluation point dictionary structure supports theories that may have additional parameters beyond just the world (like temporal theories with time indices). The `bitvec_to_worldstate` function converts numeric values like 7 into state labels like "w1" or "a.b.c".

### Verify/Falsify Relations

Extract truth-making relations from model:

```python
def extract_verify_falsify_relations(self):
    """Extract verify/falsify for all sentence letters."""
    relations = {}

    for letter in self.sentence_letters:
        verifiers = set()
        falsifiers = set()

        for state in self.z3_possible_states:
            # Check verification
            if self.z3_model.evaluate(
                self.semantics.verify(state, letter.sentence_letter)
            ):
                verifiers.add(state)

            # Check falsification
            if self.z3_model.evaluate(
                self.semantics.falsify(state, letter.sentence_letter)
            ):
                falsifiers.add(state)

        relations[letter.name] = {
            'verifiers': verifiers,
            'falsifiers': falsifiers
        }

    return relations
```

This method extracts the fundamental semantic relations from the Z3 model. For each sentence letter, it checks every possible state to see if that state verifies or falsifies the letter according to the model. The result is a complete mapping from sentence letters to their verifier and falsifier sets - the core data that defines how atomic propositions behave in this particular countermodel. These sets are the building blocks for evaluating complex formulas.

### Building Propositions

Build exact sets for each proposition:

```python
def find_proposition(self, sentence_letter):
    """Find exact verifier/falsifier sets."""
    verifiers = set()
    falsifiers = set()

    # Only check possible states
    for state in self.model_structure.z3_possible_states:
        state_verifies = self.z3_model.evaluate(
            self.semantics.verify(state, sentence_letter)
        )
        state_falsifies = self.z3_model.evaluate(
            self.semantics.falsify(state, sentence_letter)
        )

        if state_verifies:
            verifiers.add(state)
        if state_falsifies:
            falsifiers.add(state)

    return verifiers, falsifiers
```

This method builds the exact proposition expressed by a sentence letter by finding its verifier and falsifier sets. This is crucial because it connects the abstract sentence letters in our formulas to concrete semantic content in the model. Once we have these sets, we can recursively compute the propositions for complex sentences using the semantic clauses (conjunction intersects verifiers, disjunction unions them, etc.). This bridge from syntax to semantics is the heart of model interpretation.

### World State Identification

Distinguish worlds from other states:

```python
# Define is_world predicate
def is_world(self, state):
    """Check if state is a possible world."""
    return And(
        self.possible(state),      # State must be possible
        self.maximal(state)        # State must be maximal (no proper extensions)
    )

# Extract from model
world_states = {
    state for state in possible_states
    if z3_model.evaluate(semantics.is_world(state))
}
```

A world is defined as a possible state that is maximal - it has no proper extensions that are also possible. This captures the intuition that worlds are complete scenarios where everything is settled. In the bit vector encoding, a state s is maximal if there's no state m where s is a proper part of m (all bits set in s are also set in m, but m has additional bits set). This distinguishes worlds from partial states that could be extended with more information.

### Evaluation Point Setup

Create evaluation contexts:

```python
# Main evaluation point
main_point = {
    "world": main_world_value
}

# Alternative evaluation points
alt_points = []
for world in world_states:
    if world != main_world_value:
        alt_point = {
            "world": world
        }
        alt_points.append(alt_point)
```

The evaluation point structure is designed to be extensible. While simple modal theories only need a world parameter, more complex theories require additional context. For example, bimodal theory includes temporal indices: `{"world": w, "time": t}`. Epistemic theories might add agent parameters: `{"world": w, "agent": a}`. This dictionary structure allows each theory to define its own evaluation parameters without changing the core framework.

### State Representation

Convert bitvectors to readable format:

```python
def bitvec_to_substates(bit_vec, N):
    """Convert bitvector to fusion of atomic states."""
    # Get binary representation
    binary = format(bit_vec.as_long(), f'0{N}b')[::-1]  # Reverse for LSB-first indexing

    # Build state representation
    parts = []
    for i, bit in enumerate(binary):
        if bit == '1':  # This bit position is "on"
            # Convert index to state label
            parts.append(index_to_substate(i))  # 0→'a', 1→'b', 2→'c', etc.

    # Join with fusion operator
    return '.'.join(parts) if parts else '□'  # Empty state is null (□)

# Example: BitVec(5, 3) → "a.c" (bits 0 and 2 set)
```

The bit vector representation encodes states as binary numbers where each bit position corresponds to an atomic state. This clever encoding enables efficient mereological operations:

```
State Encoding (N=3):
┌─────────────────────────────────────────┐
│ BitVec │ Binary │ State │ Meaning       │
├────────┼────────┼───────┼───────────────┤
│   0    │  000   │   □   │ Null state    │
│   1    │  001   │   a   │ Atomic 'a'    │
│   2    │  010   │   b   │ Atomic 'b'    │
│   3    │  011   │  a.b  │ Fusion a,b    │
│   4    │  100   │   c   │ Atomic 'c'    │
│   5    │  101   │  a.c  │ Fusion a,c    │
│   6    │  110   │  b.c  │ Fusion b,c    │
│   7    │  111   │ a.b.c │ Fusion all    │
└─────────────────────────────────────────┘
```

Fusion becomes bitwise OR: `fusion(a, b) = 001 | 010 = 011 = a.b`. Parthood becomes bitwise AND equality: `is_part_of(a, a.b) ≡ (001 & 011 == 001) = True`.

_See also: [`model_checker/utils.py`](../../Code/src/model_checker/utils.py) for state conversion utilities_

## Sentence Interpretation

### Proposition Update Process

Attach semantic interpretation to sentences:

```python
def interpret(self, sentences):
    """Update sentences with propositions."""
    if not self.z3_model:
        return

    for sentence in sentences:
        # Skip if already interpreted
        if sentence.proposition is not None:
            continue

        # Recursively interpret arguments first
        if sentence.arguments:
            self.interpret(sentence.arguments)

        # Create proposition for this sentence
        sentence.update_proposition(self)
```

The `interpret` method implements the recursive semantics that assigns propositions to sentences. In truthmaker semantics, a model assigns each sentence letter to a proposition (a pair of verifier/falsifier sets). For complex sentences, their propositions are computed from their parts: conjunction intersects verifiers, disjunction unions them, etc. This bottom-up interpretation ensures each sentence gets assigned exactly the proposition it expresses given the base assignments to sentence letters.

### Recursive Evaluation

Build propositions bottom-up:

```python
# 1. Atomic sentences
sentence_A.proposition = LogosProposition(sentence_A, model_structure)
# Finds verifiers/falsifiers from model

# 2. Complex sentences use operator methods
sentence_and = Sentence("A \\wedge B")
sentence_and.proposition = LogosProposition(sentence_and, model_structure)
# Operator computes from argument propositions
```

Recursive evaluation mirrors standard compositional semantics: the meaning of a complex sentence is determined by the meanings of its parts. Starting with sentence letters (which get propositions from the model's verify/falsify assignments), we build up propositions for increasingly complex sentences. Crucially, we only interpret sentences that actually appear as subformulas of our premises or conclusions - there's no need to compute propositions for sentences that never get evaluated. This lazy evaluation significantly improves performance on large examples.

### Truth Value Determination

Evaluate truth at worlds:

```python
def truth_value_at(self, world):
    """Determine truth value at world."""
    sentence = self.sentence
    semantics = self.model_structure.semantics
    z3_model = self.model_structure.z3_model

    # Check if true
    is_true = z3_model.evaluate(
        semantics.true_at(world, sentence, self.eval_point)
    )

    # Check if false
    is_false = z3_model.evaluate(
        semantics.false_at(world, sentence, self.eval_point)
    )

    # Return truth value
    if is_true and not is_false:
        return "T"
    elif is_false and not is_true:
        return "F"
    elif is_true and is_false:
        return "B"  # Both (glut)
    else:
        return "N"  # Neither (gap)
```

This method determines a sentence's truth value at a world by checking the Z3 model's assignments to the `true_at` and `false_at` predicates. The four-valued logic allows for truth value gaps (neither true nor false) and gluts (both true and false). Classical theories will only return "T" or "F", but non-classical theories may produce gaps when no state in the world verifies or falsifies the sentence, or gluts in paraconsistent contexts. This flexibility supports a wide range of semantic theories.

### Model Structure Population

Store interpretation results:

```python
# Store in model structure
self.propositions = {}
for sentence in all_sentences:
    self.propositions[sentence.name] = sentence.proposition

# Access later
prop_A = self.propositions["A"]
verifiers_A = prop_A.verifiers
falsifiers_A = prop_A.falsifiers
```

### Witness Finding

Find states witnessing truth/falsity:

```python
def find_witness(self, world, sentence):
    """Find state witnessing truth/falsity."""
    # Find verifying witness
    for state in self.all_states:
        if self.z3_model.evaluate(And(
            self.is_part_of(state, world),
            self.extended_verify(state, sentence, eval_point)
        )):
            return ('verify', state)

    # Find falsifying witness
    for state in self.all_states:
        if self.z3_model.evaluate(And(
            self.is_part_of(state, world),
            self.extended_falsify(state, sentence, eval_point)
        )):
            return ('falsify', state)

    return (None, None)
```

## Output Generation

The output generation transforms raw model data into human-readable countermodel displays:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        OUTPUT GENERATION FLOW                           │
└─────────────────────────────────────────────────────────────────────────┘

                    ┌─────────────────────┐
                    │ Raw Z3 Model        │
                    │ • BitVec values     │
                    │ • Function mappings │
                    │ • Boolean values    │
                    └──────────┬──────────┘
                               │ Transform
                               ▼
                    ┌─────────────────────┐
                    │ Structured Data     │
                    │ • State space       │
                    │ • Extensions        │
                    │ • Truth values      │
                    └──────────┬──────────┘
                               │ Format
                               ▼
                    ┌─────────────────────┐
                    │ Display Output      │
                    │ • World structure   │
                    │ • Evaluation trees  │
                    └─────────────────────┘
```

### Example Output:

```
┌─────────────────────────────────────────┐
│ MODAL_TH_1: countermodel found          │
│ Semantic theory: Logos                  │
│ Model size (N): 3                       │
│                                         │
│ WORLD STATES:                           │
│   w = a.b.c (main)                      │
│                                         │
│ SENTENCE LETTER EXTENSIONS:             │
│ A:                                      │
│   Verifiers: {a, a.b, a.c, a.b.c}       │
│   Falsifiers: {b}                       │
│ B:                                      │
│   Verifiers: {b, a.b, b.c, a.b.c}       │
│   Falsifiers: {c}                       │
│                                         │
│ INTERPRETED PREMISES:                   │
│ 1. (A \wedge B)                         │
│    └─ true at w (witness: a.b)          │
└─────────────────────────────────────────┘
```

### Model Visualization

Display model structure:

```python
def print_states(self, output):
    """Print state information."""
    print("\nMODEL STATES:", file=output)

    # Possible states
    print(f"\nPossible states ({len(self.z3_possible_states)}):", file=output)
    for state in sorted(self.z3_possible_states):
        state_str = bitvec_to_substates(state, self.N)
        print(f"  {state_str}", file=output)

    # World states
    print(f"\nWorld states ({len(self.z3_world_states)}):", file=output)
    for world in sorted(self.z3_world_states):
        world_str = bitvec_to_worldstate(world)
        is_main = " (main)" if world == self.main_world_value else ""
        print(f"  {world_str}{is_main}", file=output)
```

This visualization method presents the model structure in a human-readable format. It lists all possible states (showing their atomic components) and identifies which are worlds. The main world is specially marked since that's where premises and conclusions are evaluated. The state representation uses fusion notation (a.b.c) making the mereological structure clear. This output helps users understand the countermodel's structure at a glance.

### Extension Display

Show proposition extensions:

```python
def print_evaluation(self, output):
    """Print sentence letter extensions."""
    print("\nSENTENCE LETTER EXTENSIONS:", file=output)

    for letter in self.sentence_letters:
        prop = letter.proposition

        # Format verifiers
        ver_str = pretty_set_print({
            bitvec_to_substates(v, self.N)
            for v in prop.verifiers
        })

        # Format falsifiers
        fal_str = pretty_set_print({
            bitvec_to_substates(f, self.N)
            for f in prop.falsifiers
        })

        print(f"\n{letter.name}:", file=output)
        print(f"  Verifiers: {ver_str}", file=output)
        print(f"  Falsifiers: {fal_str}", file=output)
```

This method displays the extensions of sentence letters - the verifier and falsifier sets that define their semantic content. The `pretty_set_print` function formats these sets in a readable way, converting bit vectors to state labels. This visualization is crucial for understanding the countermodel: it shows exactly which states make each atomic proposition true or false, revealing the fine-grained structure that distinguishes logically equivalent formulas in hyperintensional contexts.

### Evaluation Results

Display premise/conclusion evaluation:

```python
def print_input_sentences(self, output):
    """Print interpreted sentences."""
    print("\nINTERPRETED PREMISES:", file=output)

    for i, premise in enumerate(self.premises, 1):
        print(f"{i}. ", end="", file=output)
        self.recursive_print(
            premise,
            self.main_point,
            indent=1,
            use_colors=True
        )

    # Similar for conclusions...
```

This method shows how each premise and conclusion evaluates at the main world. The `recursive_print` function displays the formula structure as a tree, showing truth values and witnessing states at each level. The indentation and optional color coding make it easy to trace through complex formulas to see exactly why they're true or false. This detailed evaluation breakdown is essential for understanding why the argument is invalid.

### Countermodel Formatting

Format complete countermodel:

```python
def print_to(self, settings, example_name, theory_name, output):
    """Print complete model output."""
    # Header
    status = "countermodel" if self.z3_model_status else "no countermodel"
    print(f"\n{example_name}: {status}", file=output)

    # Settings
    print(f"Semantic theory: {theory_name}", file=output)
    print(f"Model size (N): {settings['N']}", file=output)

    # Model structure
    if self.z3_model_status:
        self.print_states(output)
        self.print_evaluation(output)
        self.print_input_sentences(output)
    else:
        print("\nNo model found - argument is valid", file=output)
        if self.unsat_core:
            print(f"Unsat core size: {len(self.unsat_core)}", file=output)
```

The main output method orchestrates the complete countermodel display. It prints a header with the example name and theory, then conditionally displays the model structure based on satisfiability. For countermodels, it shows states, extensions, and sentence evaluations in sequence. For valid arguments (no countermodel), it reports the unsat core size to help debug why the constraints conflict. This structured output format makes results easy to interpret across different theories and examples.

### Color Coding

ANSI colors for terminal output:

```python
# Color definitions
COLORS = {
    "true": "\033[32m",      # Green
    "false": "\033[31m",     # Red
    "both": "\033[33m",      # Yellow (glut)
    "neither": "\033[90m",   # Gray (gap)
    "world": "\033[34m",     # Blue
    "state": "\033[36m",     # Cyan
    "reset": "\033[0m"
}

# Usage in output
def format_truth_value(value):
    """Color code truth values."""
    color = COLORS.get(value.lower(), COLORS["reset"])
    return f"{color}{value}{COLORS['reset']}"

# Example output
print(f"A: {format_truth_value('T')} at world w")
```

Color coding enhances readability by providing visual cues for different truth values and model elements. Green for true and red for false follow standard conventions, while yellow for gluts and gray for gaps make non-classical values immediately visible. Blue highlights worlds and cyan marks states, helping users quickly identify structural elements. This visual differentiation is especially valuable when examining complex countermodels with many states and formulas.

## Code Examples

### Complete Solving Pipeline

```python
from model_checker.model import ModelDefaults, ModelConstraints
from model_checker.syntactic import Syntax

# Setup
syntax = Syntax(premises, conclusions, operators)  # Parse formulas to ASTs
constraints = ModelConstraints(
    settings,           # Controls semantic properties
    syntax,             # Parsed formula structures
    semantics,          # Theory class (not instance)
    proposition_class   # How to interpret atoms
)

# Solve
model = ModelDefaults(constraints, settings)  # This runs Z3 solver internally

# Check results
if model.z3_model_status:  # True if SAT (countermodel exists)
    print("Countermodel found")
    model.print_to(settings, "example", "theory", sys.stdout)
else:
    print("No countermodel - valid argument")
```

This pipeline demonstrates the complete flow from logical formulas to validity checking. The ModelDefaults constructor handles all the complexity: it extracts constraints from ModelConstraints, sets up Z3 with proper isolation, attempts to find a satisfying model, and processes the results. The boolean `z3_model_status` tells us whether the argument is valid (False = no countermodel) or invalid (True = countermodel found).

### Custom Model Structure

```python
class LogosModelStructure(ModelDefaults):
    """Logos-specific model structure."""

    def __init__(self, model_constraints, settings):
        super().__init__(model_constraints, settings)

        # Extract Logos-specific elements
        if self.z3_model:
            self._extract_logos_structure()

    def _extract_logos_structure(self):
        """Extract truthmaker structure."""
        # Get possible/world states
        self.z3_possible_states = self._get_possible_states()
        self.z3_world_states = self._get_world_states()

        # Extract compatibility relation
        self.compatibility = self._extract_compatibility()
```

_Note: Theory-specific model structures are typically implemented as subclasses of ModelDefaults in their respective theory packages._

### Debugging Support

```python
# Enable verbose output
if settings.get('verbose'):
    print(f"Constraints: {len(all_constraints)}")
    print(f"Variables: {num_variables}")
    print(f"Solving...")

# Save constraints
if settings.get('save_constraints'):
    with open('constraints.smt2', 'w') as f:
        f.write(solver.to_smt2())

# Print unsat core
if not model.z3_model_status:
    print("Unsat core:")
    for label in model.unsat_core:
        constraint = model.constraint_dict[str(label)]
        print(f"  {label}: {constraint}")
```

These debugging features help diagnose issues during development. Verbose output shows constraint counts and solving progress. Saving constraints to SMT2 format allows inspection with external tools or sharing problem instances. The unsat core display is particularly valuable - it shows exactly which constraints conflict when no model exists, helping identify bugs in semantic theories or understand why certain arguments are necessarily valid.

### Output Customization

```python
# Minimal output
model.print_to(
    settings,
    example_name,
    theory_name,
    output=sys.stdout,
    verbose=False,
    show_extensions=False
)

# Full debug output
model.print_to(
    settings,
    example_name,
    theory_name,
    output=debug_file,
    verbose=True,
    show_constraints=True,
    show_z3_model=True
)
```

The output customization options allow tailoring the display to different use cases. Minimal output suits batch processing where only essential results matter. Full debug output helps during theory development by showing all constraints, the raw Z3 model, and detailed solving statistics. These flexible output modes support both end users who want clean results and developers who need comprehensive debugging information.

## References

### Implementation Files

**Core Model Classes:**

- [`model_checker/model.py`](../../Code/src/model_checker/model.py) - ModelDefaults base class and ModelConstraints
## Technical Implementation

For detailed implementation information, see:
- [Models Package Documentation](../../Code/src/model_checker/models/README.md) - Complete API reference
- [Model Base Classes](../../Code/src/model_checker/models/model.py) - Core model infrastructure
- [Model Defaults](../../Code/src/model_checker/models/defaults.py) - Default model implementation
- [Model Utilities](../../Code/src/model_checker/models/utilities.py) - Helper functions

## See Also

### Related Architecture
- [Semantic Framework](SEMANTICS.md) - Constraint generation that feeds into models
- [Iterator System](ITERATE.md) - Finding multiple distinct models
- [Builder Pipeline](BUILDER.md) - Model orchestration
- [Theory Framework](THEORY_LIB.md) - Theory-specific model extensions

### Technical Documentation
- [Z3 Python API](https://z3prover.github.io/api/html/namespacez3py.html) - Official Z3 documentation
- [API Reference](../../Code/src/model_checker/README.md) - Framework APIs

---

[← Back to Architecture](README.md) | [Semantics →](SEMANTICS.md) | [Iterator →](ITERATE.md)
