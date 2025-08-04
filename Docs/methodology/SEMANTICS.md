# Semantics: From Strings to Z3 Constraints

[← Syntax Pipeline](SYNTAX.md) | [Back to Methodology](README.md) | [Model Finding →](MODELS.md)

## Table of Contents

1. [Introduction](#introduction)
2. [Base Classes Overview](#base-classes-overview)
   - [SemanticDefaults](#semanticdefaults)
   - [PropositionDefaults](#propositiondefaults)
   - [ModelDefaults](#modeldefaults)
   - [ModelConstraints](#modelconstraints)
3. [Logos Semantic Pipeline](#logos-semantic-pipeline)
   - [LogosSemantics Structure](#logossemantics-structure)
   - [Z3 Primitive Declaration](#z3-primitive-declaration)
   - [Frame Constraints](#frame-constraints)
   - [Truth/Falsity Evaluation](#truthfalsity-evaluation)
   - [Main Evaluation Point](#main-evaluation-point)
4. [LogosProposition Class](#logosproposition-class)
   - [Role in Constraining](#role-in-constraining)
   - [Verifier/Falsifier Computation](#verifierfalsifier-computation)
   - [Proposition Constraints Hierarchy](#proposition-constraints-hierarchy)
   - [Settings Interaction](#settings-interaction)
5. [Operator Implementation Pattern](#operator-implementation-pattern)
   - [Operator Base Class](#operator-base-class)
   - [Required Methods](#required-methods)
   - [Finding Verifiers/Falsifiers](#finding-verifiersfalsifiers)
   - [Print Methods](#print-methods)
6. [Subtheory Architecture](#subtheory-architecture)
   - [Operator Registry System](#operator-registry-system)
   - [Dynamic Loading](#dynamic-loading)
   - [Dependency Management](#dependency-management)
   - [Conflict Resolution](#conflict-resolution)
7. [Z3 Constraint Collection](#z3-constraint-collection)
   - [Frame Constraints](#frame-constraints-1)
   - [Model Constraints](#model-constraints-1)
   - [Premise Constraints](#premise-constraints)
   - [Conclusion Constraints](#conclusion-constraints)
   - [Settings-Based Generation](#settings-based-generation)
   - [Complete Aggregation](#complete-aggregation)
   - [Debugging Techniques](#debugging-techniques)
8. [Example Constraint Pipeline](#example-constraint-pipeline)
9. [Code Examples](#code-examples)
10. [References](#references)

## Introduction

The semantics module bridges the gap between parsed logical formulas and SMT solver constraints. It provides a flexible framework for implementing various semantic theories, from classical possible worlds semantics to more complex approaches like truthmaker semantics. Each theory defines its own interpretation rules while sharing the common constraint generation pipeline.

The pipeline transforms syntactic structures into Z3 constraints through a series of semantic interpretation layers, each adding specific constraints based on the logical theory and configured settings. The result is a complete set of constraints that, when solved, yields models demonstrating validity or invalidity of logical arguments.

## Base Classes Overview

### SemanticDefaults

The foundation for all semantic implementations, providing core operations:

```python
class SemanticDefaults:
    """Base semantic operations for modal logics."""
    
    def __init__(self, combined_settings):
        self.N = combined_settings['N']  # Number of atomic states
        self.name = self.__class__.__name__
        
        # Core state operations
        self.full_state = BitVecVal((1 << N) - 1, N)  # All bits set
        self.null_state = BitVecVal(0, N)             # No bits set
        self.all_states = [BitVecVal(i, N) for i in range(1 << N)]
        
    def fusion(self, bit_s, bit_t):
        """State combination via bitwise OR."""
        return bit_s | bit_t
        
    def is_part_of(self, bit_s, bit_t):
        """Mereological part-of relation."""
        return self.fusion(bit_s, bit_t) == bit_t
```

### PropositionDefaults

Base class for proposition representation and constraint generation:

```python
class PropositionDefaults:
    """Links sentences to semantic interpretation."""
    
    def __init__(self, sentence, model_structure):
        self.sentence = sentence
        self.model_structure = model_structure
        self.semantics = model_structure.semantics
        self.N = self.semantics.N
        
    def find_proposition(self):
        """Find verifier and falsifier sets."""
        # Implemented by subclasses
        
    def proposition_constraints(self, sentence_letter):
        """Generate constraints for atomic propositions."""
        # Implemented by subclasses
```

### ModelDefaults

Core model structure and solving capabilities:

```python
class ModelDefaults:
    """Handles Z3 solving and model interpretation."""
    
    def __init__(self, model_constraints, settings):
        self.model_constraints = model_constraints
        self.semantics = model_constraints.semantics
        self.settings = settings
        
        # Constraint collection
        self.frame_constraints = []
        self.model_constraints_list = []
        self.premise_constraints = []
        self.conclusion_constraints = []
        
        # Z3 solving
        self.z3_model = self.evaluate_constraints()
```

### ModelConstraints

Bridges syntax to semantics by generating constraints:

```python
class ModelConstraints:
    """Links parsed syntax to semantic constraints."""
    
    def __init__(self, settings, syntax, semantics, proposition_class):
        self.settings = settings
        self.syntax = syntax
        self.semantics = semantics
        self.proposition_class = proposition_class
        
        # Instantiate operators with semantics
        self.operators = self.instantiate_operators()
        
        # Update sentences with semantic operators
        for sentence in self.syntax.all_sentences.values():
            sentence.update_objects(self)
```

## Example: Logos Semantic Pipeline

### Theory Implementation Example: LogosSemantics

As an example, LogosSemantics implements hyperintensional truthmaker semantics:

```python
class LogosSemantics(SemanticDefaults):
    """Hyperintensional truthmaker semantics for Logos theory."""
    
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 16,                  # Default state space size
        'contingent': True,       # Require contingent propositions
        'non_empty': True,        # No empty verifier/falsifier sets
        'non_null': True,         # No null state verifiers/falsifiers
        'disjoint': True,         # Disjoint verifier/falsifier sets
        'max_time': 10,           # Solver timeout
    }
```

### Z3 Primitive Declaration

Core semantic primitives as Z3 functions:

```python
# Verification relation: state × proposition → bool
self.verify = z3.Function(
    "verify",
    z3.BitVecSort(self.N),    # State (bitvector)
    syntactic.AtomSort,        # Atomic proposition
    z3.BoolSort()              # Truth value
)

# Falsification relation: state × proposition → bool
self.falsify = z3.Function(
    "falsify",
    z3.BitVecSort(self.N),
    syntactic.AtomSort,
    z3.BoolSort()
)

# Possibility predicate: state → bool
self.possible = z3.Function(
    "possible",
    z3.BitVecSort(self.N),
    z3.BoolSort()
)
```

### Frame Constraints

Structural constraints defining the semantic framework:

```python
# Possibility is downward-closed under parthood
x, y = z3.BitVecs("frame_x frame_y", self.N)
possibility_downward_closure = ForAll(
    [x, y],
    z3.Implies(
        z3.And(
            self.possible(y),           # If y is possible
            self.is_part_of(x, y)       # and x is part of y
        ),
        self.possible(x)                # then x is possible
    )
)

# Main world must be possible
self.main_world = z3.BitVec("w", self.N)
main_world_constraint = self.is_world(self.main_world)

self.frame_constraints = [
    possibility_downward_closure,
    main_world_constraint
]
```

### Truth/Falsity Evaluation

Extended verification and falsification for complex formulas:

```python
def true_at(self, world, sentence, eval_point):
    """Sentence is true at world if some part verifies it."""
    x = z3.BitVec("true_at_x", self.N)
    return Exists(
        x,
        z3.And(
            self.is_part_of(x, world),
            self.extended_verify(x, sentence, eval_point)
        )
    )

def false_at(self, world, sentence, eval_point):
    """Sentence is false at world if some part falsifies it."""
    x = z3.BitVec("false_at_x", self.N)
    return Exists(
        x,
        z3.And(
            self.is_part_of(x, world),
            self.extended_falsify(x, sentence, eval_point)
        )
    )
```

### Main Evaluation Point

The evaluation context for premises and conclusions:

```python
# Define main evaluation point
self.main_point = {
    "world": self.main_world    # Main world variable
}

# Used in constraint generation
premise_true = self.true_at(
    self.main_point["world"],
    premise_sentence,
    self.main_point
)
```

## LogosProposition Class

### Role in Constraining

LogosProposition constrains how atomic sentence letters are interpreted:

```python
class LogosProposition(PropositionDefaults):
    """Constrains atomic proposition interpretation."""
    
    def __init__(self, sentence, model_structure, eval_world='main'):
        super().__init__(sentence, model_structure)
        self.eval_world = (
            model_structure.main_point["world"] 
            if eval_world == 'main' 
            else eval_world
        )
        self.verifiers, self.falsifiers = self.find_proposition()
```

### Verifier/Falsifier Computation

Finding exact verifier and falsifier sets:

```python
def find_proposition(self):
    """Compute verifier and falsifier sets for the sentence."""
    if self.sentence.sentence_letter:
        # Atomic sentence - extract from Z3 model
        return self.find_exact_proposition()
    else:
        # Complex sentence - use operator method
        operator = self.sentence.operator
        arguments = self.sentence.arguments
        return operator.find_verifiers_and_falsifiers(
            self.model_structure, 
            *arguments, 
            self.eval_world
        )
```

### Proposition Constraints Hierarchy

Constraints are applied in layers based on settings:

```python
def proposition_constraints(self, sentence_letter):
    """Generate constraints based on semantic settings."""
    
    # Always applied - enforce classical logic
    classical = get_classical_constraints()
    
    # Setting-dependent constraints
    constraints = classical.copy()
    
    if self.settings.get('contingent', False):
        constraints.extend(get_contingent_constraints())
        
    if self.settings.get('non_empty', False):
        constraints.extend(get_non_empty_constraints())
        
    if self.settings.get('disjoint', False):
        constraints.extend(get_disjoint_constraints())
        
    if self.settings.get('non_null', False):
        constraints.extend(get_non_null_constraints())
        
    return constraints
```

### Settings Interaction

Each constraint type serves a specific purpose:

```python
# Classical constraints (always active)
- Verifier fusion closure: verify(x,p) ∧ verify(y,p) → verify(x|y,p)
- Falsifier fusion closure: falsify(x,p) ∧ falsify(y,p) → falsify(x|y,p)
- No gluts: verify(x,p) ∧ falsify(y,p) → ¬compatible(x,y)
- No gaps: possible(x) → ∃y(compatible(x,y) ∧ (verify(y,p) ∨ falsify(y,p)))

# Contingent constraints (setting: 'contingent')
- Possible verifier: ∃x(possible(x) ∧ verify(x,p))
- Possible falsifier: ∃x(possible(x) ∧ falsify(x,p))

# Non-empty constraints (setting: 'non_empty')  
- Some verifier exists: ∃x(verify(x,p))
- Some falsifier exists: ∃x(falsify(x,p))

# Disjoint constraints (setting: 'disjoint')
- No overlap: ¬∃x(verify(x,p) ∧ falsify(x,p))

# Non-null constraints (setting: 'non_null')
- No null verifier: ¬verify(0,p)
- No null falsifier: ¬falsify(0,p)
```

## Operator Implementation Pattern

### Operator Base Class

All operators follow a consistent implementation pattern:

```python
class Operator:
    """Base class for logical operators."""
    
    name = None        # LaTeX name like "\\wedge"
    arity = None       # Number of arguments
    primitive = True   # False for defined operators
    
    def __init__(self, semantics):
        self.semantics = semantics
        
    # Required semantic methods
    def true_at(self, world, sentence, model):
        """When is the sentence true at a world?"""
        
    def false_at(self, world, sentence, model):
        """When is the sentence false at a world?"""
        
    def extended_verify(self, state, *args, eval_point):
        """When does a state verify the sentence?"""
        
    def extended_falsify(self, state, *args, eval_point):
        """When does a state falsify the sentence?"""
```

### Required Methods

Each operator must implement four semantic methods:

```python
class AndOperator(Operator):
    name = "\\wedge"
    arity = 2
    
    def extended_verify(self, state, arg1, arg2, eval_point):
        """State verifies A∧B iff it's the fusion of an A-verifier
        and a B-verifier."""
        x = z3.BitVec("and_x", self.semantics.N)
        y = z3.BitVec("and_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                state == self.semantics.fusion(x, y),
                self.semantics.extended_verify(x, arg1, eval_point),
                self.semantics.extended_verify(y, arg2, eval_point)
            )
        )
```

### Finding Verifiers/Falsifiers

Operators compute exact verifier/falsifier sets:

```python
def find_verifiers_and_falsifiers(self, model_structure, *args):
    """Find all verifiers and falsifiers for the operator."""
    semantics = model_structure.semantics
    z3_model = model_structure.z3_model
    
    # Collect possible verifiers
    verifiers = {
        state for state in model_structure.possible_states
        if z3_model.evaluate(
            self.extended_verify(state, *args, eval_point)
        )
    }
    
    # Collect possible falsifiers
    falsifiers = {
        state for state in model_structure.possible_states
        if z3_model.evaluate(
            self.extended_falsify(state, *args, eval_point)
        )
    }
    
    return verifiers, falsifiers
```

### Print Methods

Operators define visualization for results:

```python
def print_method(self, sentence, eval_point, indent, colors):
    """Display evaluation details for the operator."""
    # Default: show general evaluation
    self.general_print(sentence, eval_point, indent, colors)
    
    # Modal operators might show alternative worlds
    self.print_over_worlds(sentence, eval_point, alt_worlds, indent, colors)
    
    # Temporal operators might show time sequences
    self.print_over_times(sentence, eval_point, times, indent, colors)
```

## Subtheory Architecture

### Operator Registry System

LogosOperatorRegistry manages modular operator loading:

```python
class LogosOperatorRegistry:
    """Central registry for all Logos operators."""
    
    def __init__(self):
        self.operators = OperatorCollection()
        self.loaded_subtheories = set()
        
    def load_subtheories(self, subtheory_names):
        """Dynamically load requested subtheories."""
        for name in subtheory_names:
            if name not in self.loaded_subtheories:
                self._load_subtheory(name)
                self.loaded_subtheories.add(name)
```

### Dynamic Loading

Subtheories are loaded on demand:

```python
def _load_subtheory(self, name):
    """Load operators from a subtheory module."""
    # Import subtheory module
    module = importlib.import_module(
        f'model_checker.theory_lib.logos.{name}.operators'
    )
    
    # Get operator list
    if hasattr(module, 'OPERATORS'):
        operators = module.OPERATORS
    elif hasattr(module, '__all__'):
        operators = [
            getattr(module, op_name) 
            for op_name in module.__all__
        ]
        
    # Add to collection
    self.operators.add_operator(operators)
```

### Dependency Management

Subtheories can declare dependencies:

```python
# In modal/operators.py
DEPENDENCIES = []  # No dependencies

# In counterfactual/operators.py  
DEPENDENCIES = ['modal']  # Requires modal operators

# Registry loads dependencies automatically
def _load_subtheory(self, name):
    # Load dependencies first
    for dep in module.DEPENDENCIES:
        if dep not in self.loaded_subtheories:
            self._load_subtheory(dep)
```

### Conflict Resolution

Operator name conflicts are resolved by precedence:

```python
def add_operator(self, operator):
    """Add operator, skipping if name exists."""
    if operator.name in self.operator_dictionary:
        # First loaded wins - dependencies load first
        return
    self.operator_dictionary[operator.name] = operator
```

## Z3 Constraint Collection

### Frame Constraints

Structural constraints from the semantic theory:

```python
# From LogosSemantics
frame_constraints = [
    possibility_downward_closure,    # Possible states closed under parts
    main_world_is_possible,          # Evaluation world exists
    compatibility_relations,         # State compatibility rules
]
```

### Model Constraints

Constraints from atomic propositions:

```python
# For each atomic sentence letter
for letter in syntax.sentence_letters:
    constraints = proposition_class.proposition_constraints(letter)
    model_constraints.extend(constraints)
    
# Results in constraints like:
- Classical logic constraints (no gaps/gluts)
- Contingency constraints (if enabled)
- Non-emptiness constraints (if enabled)
- Disjointness constraints (if enabled)
```

### Premise Constraints

Premises must be true at the main world:

```python
for premise in syntax.premises:
    constraint = semantics.true_at(
        semantics.main_point["world"],
        premise,
        semantics.main_point
    )
    premise_constraints.append(constraint)
```

### Conclusion Constraints

At least one conclusion must be false:

```python
# Invalidity requires some conclusion false
false_conclusions = []
for conclusion in syntax.conclusions:
    false_constraint = semantics.false_at(
        semantics.main_point["world"],
        conclusion,
        semantics.main_point
    )
    false_conclusions.append(false_constraint)

conclusion_constraint = z3.Or(false_conclusions)
```

### Settings-Based Generation

Settings control which constraints are active:

```python
def generate_constraints(settings):
    constraints = []
    
    # Always include frame constraints
    constraints.extend(frame_constraints)
    
    # Atomic proposition constraints based on settings
    for letter in sentence_letters:
        prop_constraints = generate_prop_constraints(letter, settings)
        constraints.extend(prop_constraints)
        
    # Evaluation constraints
    constraints.extend(premise_constraints)
    constraints.append(conclusion_constraint)
    
    return constraints
```

### Complete Aggregation

ModelConstraints collects all constraint types:

```python
class ModelDefaults:
    def evaluate_constraints(self):
        """Aggregate and solve all constraints."""
        solver = z3.Solver()
        
        # Add all constraint types with tracking
        solver.assert_and_track(frame_constraints, "frame")
        solver.assert_and_track(model_constraints, "model")
        solver.assert_and_track(premise_constraints, "premises")
        solver.assert_and_track(conclusion_constraint, "conclusions")
        
        # Solve with timeout
        solver.set("timeout", settings['max_time'] * 1000)
        result = solver.check()
        
        return solver.model() if result == z3.sat else None
```

### Debugging Techniques

Tools for constraint debugging:

```python
# Print constraints by type
if settings.get('verbose'):
    print(f"Frame constraints: {len(frame_constraints)}")
    print(f"Model constraints: {len(model_constraints)}")
    print(f"Premise constraints: {len(premise_constraints)}")
    
# Get unsat core for failed models
if solver.check() == z3.unsat:
    core = solver.unsat_core()
    print(f"Unsat core: {core}")
    
# Save constraints to file
if settings.get('save_constraints'):
    with open('constraints.smt2', 'w') as f:
        f.write(solver.to_smt2())
```

## Example Constraint Pipeline

Complete example showing all constraint types for `A ∧ B → C`:

```python
# 1. Input
premises = ["A \\wedge B"]
conclusions = ["C"]
settings = {
    'N': 3,
    'contingent': True,
    'non_empty': True
}

# 2. Frame constraints (always present)
frame = [
    # Possibility downward closure
    ∀x,y: (possible(y) ∧ x≤y) → possible(x),
    # Main world exists
    is_world(w)
]

# 3. Model constraints for A, B, C
model = [
    # Classical constraints for each letter
    ∀x,y: verify(x,A) ∧ verify(y,A) → verify(x|y,A),
    ∀x,y: verify(x,A) ∧ falsify(y,A) → ¬compatible(x,y),
    
    # Contingent constraints  
    ∃x: possible(x) ∧ verify(x,A),
    ∃x: possible(x) ∧ falsify(x,A),
    
    # Non-empty constraints
    ∃x: verify(x,A),
    ∃x: falsify(x,A),
    
    # Same pattern for B and C...
]

# 4. Premise constraint
premise = [
    # A ∧ B is true at main world
    ∃x: x≤w ∧ extended_verify(x, "A ∧ B", {"world": w})
    
    # Which expands to:
    ∃x: x≤w ∧ ∃y,z: x=y|z ∧ verify(y,A) ∧ verify(z,B)
]

# 5. Conclusion constraint  
conclusion = [
    # C is false at main world
    ∃x: x≤w ∧ falsify(x,C)
]

# Total constraints passed to Z3
all_constraints = frame + model + premise + conclusion
```

## Code Examples

### Complete Semantic Setup

```python
from model_checker.theory_lib.logos import (
    LogosSemantics, LogosProposition, LogosOperatorRegistry
)

# Configure settings
settings = {
    'N': 4,
    'contingent': True,
    'non_empty': True,
    'disjoint': True
}

# Initialize semantics
semantics = LogosSemantics(settings)

# Load operators
registry = LogosOperatorRegistry()
registry.load_subtheories(['modal', 'constitutive'])
operators = registry.operators
```

### Z3 Primitive Usage

```python
# Direct Z3 function usage
from z3 import BitVec, Bool

# Create state and atom
state = BitVec('s', 4)
atom_A = Const('A', AtomSort)

# Use semantic primitives
verifies_A = semantics.verify(state, atom_A)
falsifies_A = semantics.falsify(state, atom_A)
is_possible = semantics.possible(state)

# Create constraint
constraint = Implies(
    And(is_possible, verifies_A),
    Not(falsifies_A)  # No gluts
)
```

### Operator Implementation Example

```python
class NegationOperator(Operator):
    name = "\\neg"
    arity = 1
    
    def extended_verify(self, state, arg, eval_point):
        """State verifies ¬A iff it falsifies A."""
        return self.semantics.extended_falsify(state, arg, eval_point)
        
    def extended_falsify(self, state, arg, eval_point):
        """State falsifies ¬A iff it verifies A."""
        return self.semantics.extended_verify(state, arg, eval_point)
        
    def find_verifiers_and_falsifiers(self, model_structure, arg):
        """Swap verifiers and falsifiers of argument."""
        arg_verifiers, arg_falsifiers = arg.proposition.find_proposition()
        return arg_falsifiers, arg_verifiers  # Swapped
```

### Settings Impact Example

```python
# Minimal settings - few constraints
settings_minimal = {
    'N': 3,
    'contingent': False,
    'non_empty': False
}
# Results in: Only classical constraints

# Maximal settings - many constraints  
settings_maximal = {
    'N': 3,
    'contingent': True,
    'non_empty': True,
    'disjoint': True,
    'non_null': True
}
# Results in: Classical + all optional constraints

# Impact on solving
# Minimal: Faster solving, more models
# Maximal: Slower solving, fewer models
```

### Complete Constraint Generation

```python
from model_checker.model import ModelConstraints
from model_checker.syntactic import Syntax

# Parse formulas
syntax = Syntax(premises, conclusions, operators)

# Generate constraints
model_constraints = ModelConstraints(
    settings,
    syntax,
    semantics,
    LogosProposition
)

# Access different constraint types
frame = semantics.frame_constraints
model = model_constraints.model_constraints
premises = model_constraints.premise_constraints
conclusions = model_constraints.conclusion_constraints

print(f"Total constraints: {len(frame + model + premises + [conclusions])}")
```

## References

### Implementation Files
- `model_checker/model.py` - Base semantic classes
- `model_checker/theory_lib/logos/semantic.py` - Logos implementation
- `model_checker/theory_lib/logos/*/operators.py` - Subtheory operators

### Related Documentation
- [Syntax Pipeline](SYNTAX.md) - How formulas become sentences
- [Model Finding](MODELS.md) - How constraints are solved
- [Theory Development](../../Code/docs/DEVELOPMENT.md) - Creating new theories

---

[← Syntax Pipeline](SYNTAX.md) | [Back to Methodology](README.md) | [Model Finding →](MODELS.md)