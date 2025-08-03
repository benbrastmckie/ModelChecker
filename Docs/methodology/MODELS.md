# Models: SMT Solving and Result Interpretation

[← Semantics Pipeline](SEMANTICS.md) | [Back to Methodology](README.md) | [Workflow →](WORKFLOW.md)

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
   - [SMT Model Interpretation](#smt-model-interpretation)
   - [State Extraction](#state-extraction)
   - [Main World Assignment](#main-world-assignment)
   - [Model Differences Tracking](#model-differences-tracking)
6. [Extension Assignment](#extension-assignment)
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
   - [Witness Finding](#witness-finding)
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

The module is designed with future extensibility in mind, abstracting solver-specific operations to allow potential integration with other SMT solvers like CVC5 or MathSAT. The result is either a concrete model showing why an argument is invalid or proof that no such countermodel exists.

## SMT Solver Setup

### Solver Initialization

Each example gets a fresh solver instance to ensure isolation:

```python
def solve(self, model_constraints, max_time):
    """Create fresh Z3 context for solving."""
    import z3
    
    # Reset context for complete isolation
    Z3ContextManager.reset_context()
    
    # Create new solver instance
    self.solver = z3.Solver()
    
    # Setup solver with constraints
    self.solver = self._setup_solver(model_constraints)
```

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
            z3._main_ctx = None
            
        # Force garbage collection
        import gc
        gc.collect()
        
        # Reset parameters
        z3.reset_params()
        z3.set_param(verbose=0)
```

### Constraint Tracking

Constraints are added with labels for debugging:

```python
def _setup_solver(self, model_constraints):
    """Add constraints with tracking labels."""
    solver = Solver()
    self.constraint_dict = {}
    
    constraint_groups = [
        (model_constraints.frame_constraints, "frame"),
        (model_constraints.model_constraints, "model"),
        (model_constraints.premise_constraints, "premises"),
        (model_constraints.conclusion_constraints, "conclusions")
    ]
    
    for constraints, group_name in constraint_groups:
        for ix, constraint in enumerate(constraints):
            c_id = f"{group_name}{ix+1}"
            solver.assert_and_track(constraint, c_id)
            self.constraint_dict[c_id] = constraint
            
    return solver
```

### Timeout Configuration

Solver timeout prevents infinite loops:

```python
# Set timeout in milliseconds
max_time_ms = int(max_time * 1000)
self.solver.set("timeout", max_time_ms)

# Check result
result = self.solver.check()

# Handle timeout
if self.solver.reason_unknown() == "timeout":
    return self._create_result(True, None, False, start_time)
```

### Unsat Core Extraction

For unsatisfiable constraints, extract minimal conflicting set:

```python
if result == z3.unsat:
    # Get unsat core - minimal set of conflicting constraints
    unsat_core = self.solver.unsat_core()
    
    # Map back to original constraints
    core_constraints = [
        self.constraint_dict[str(c)] 
        for c in unsat_core
    ]
    
    return self._create_result(False, core_constraints, False, start_time)
```

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

## Constraint Organization

### Frame Constraints

Structural constraints defining the semantic framework:

```python
# Example frame constraints from Logos
frame_constraints = [
    # Possibility is downward-closed
    ForAll([x, y], 
        Implies(
            And(possible(y), is_part_of(x, y)),
            possible(x)
        )
    ),
    # Main world exists and is possible
    is_world(main_world),
    # State compatibility is symmetric
    ForAll([x, y],
        compatible(x, y) == compatible(y, x)
    )
]
```

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

## ModelDefaults and Theory Structures

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

### State Extraction

Identify possible and world states:

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

### Model Differences Tracking

Support for model iteration:

```python
def calculate_model_differences(self, previous_structure):
    """Find differences from previous model."""
    differences = {
        'sentence_letters': {},
        'semantic_functions': {},
        'model_structure': {}
    }
    
    # Compare sentence letter extensions
    for letter in self.sentence_letters:
        old_verifiers = previous_structure.get_verifiers(letter)
        new_verifiers = self.get_verifiers(letter)
        
        if old_verifiers != new_verifiers:
            differences['sentence_letters'][letter] = {
                'old': old_verifiers,
                'new': new_verifiers
            }
    
    return differences
```

## Extension Assignment

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

### Verifier/Falsifier Sets

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

### World State Identification

Distinguish worlds from other states:

```python
# Define is_world predicate
def is_world(self, state):
    """Check if state is a possible world."""
    return And(
        self.possible(state),
        # Additional world conditions
        self.world_closed(state),
        self.world_consistent(state)
    )

# Extract from model
world_states = {
    state for state in possible_states
    if z3_model.evaluate(semantics.is_world(state))
}
```

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

### State Representation

Convert bitvectors to readable format:

```python
def bitvec_to_substates(bit_vec, N):
    """Convert bitvector to fusion of atomic states."""
    # Get binary representation
    binary = format(bit_vec.as_long(), f'0{N}b')[::-1]
    
    # Build state representation
    parts = []
    for i, bit in enumerate(binary):
        if bit == '1':
            # Convert index to state label
            parts.append(index_to_substate(i))
            
    # Join with fusion operator
    return '.'.join(parts) if parts else '□'

# Example: BitVec(5, 3) → "a.c" (bits 0 and 2 set)
```

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

## Code Examples

### Complete Solving Pipeline

```python
from model_checker.model import ModelDefaults, ModelConstraints
from model_checker.syntactic import Syntax

# Setup
syntax = Syntax(premises, conclusions, operators)
constraints = ModelConstraints(settings, syntax, semantics, proposition_class)

# Solve
model = ModelDefaults(constraints, settings)

# Check results
if model.z3_model_status:
    print("Countermodel found")
    model.print_to(settings, "example", "theory", sys.stdout)
else:
    print("No countermodel - valid argument")
```

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

### Model Iteration Support

```python
def find_next_model(self, previous_model):
    """Find a different model."""
    # Add constraint excluding previous model
    difference = self._create_difference_constraint(previous_model)
    self.solver.add(difference)
    
    # Re-solve
    results = self.re_solve()
    
    if results[2]:  # satisfiable
        return self._create_new_structure(results[1])
    else:
        return None
```

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

## References

### Implementation Files
- `model_checker/model.py` - ModelDefaults implementation
- `model_checker/utils.py` - Z3 helpers and utilities
- `model_checker/theory_lib/*/models.py` - Theory-specific models

### Related Documentation
- [Semantics Pipeline](SEMANTICS.md) - Constraint generation
- [Workflow](WORKFLOW.md) - Using the complete system
- [Z3 Documentation](https://z3prover.github.io/api/html/namespacez3py.html)

---

[← Semantics Pipeline](SEMANTICS.md) | [Back to Methodology](README.md) | [Workflow →](WORKFLOW.md)