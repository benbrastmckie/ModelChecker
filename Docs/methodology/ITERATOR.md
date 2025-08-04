# Iterator: Model Iteration and the 'iterate' Setting

[← Back to Methodology](README.md) | [Architecture →](ARCHITECTURE.md) | [Workflow →](../usage/WORKFLOW.md)

## Table of Contents

1. [Introduction](#introduction)
2. [Overview](#overview)
   - [What Iteration Means in ModelChecker](#what-iteration-means-in-modelchecker)
   - [Finding Structurally Distinct Countermodels](#finding-structurally-distinct-countermodels)
   - [Theory-Specific Semantic Differences](#theory-specific-semantic-differences)
   - [Use Cases for Iteration](#use-cases-for-iteration)
3. [The 'iterate' Setting](#the-iterate-setting)
   - [Setting Format](#setting-format)
   - [Interaction with Other Settings](#interaction-with-other-settings)
   - [Performance Implications](#performance-implications)
   - [Default Behaviors](#default-behaviors)
4. [Iteration Algorithm](#iteration-algorithm)
   - [Initial Model as Starting Point](#initial-model-as-starting-point)
   - [Difference Constraint Generation](#difference-constraint-generation)
   - [Isomorphism Detection and Avoidance](#isomorphism-detection-and-avoidance)
   - [Escape Strategies for Stuck Iterations](#escape-strategies-for-stuck-iterations)
   - [Invalid Model Handling](#invalid-model-handling)
5. [Theory-Specific Behaviors](#theory-specific-behaviors)
   - [Logos: Verification/Falsification Differences](#logos-verificationfalsification-differences)
   - [Exclusion: Witness and Exclusion Variations](#exclusion-witness-and-exclusion-variations)
   - [Default: Classical Valuation Changes](#default-classical-valuation-changes)
   - [Bimodal: Temporal-Modal Variations](#bimodal-temporal-modal-variations)
   - [Imposition: Imposition Relation Changes](#imposition-imposition-relation-changes)
6. [Implementation Details](#implementation-details)
   - [BaseModelIterator Abstract Methods](#basemodeliterator-abstract-methods)
   - [Constraint Generation Strategies](#constraint-generation-strategies)
   - [Graph Representation for Isomorphism](#graph-representation-for-isomorphism)
   - [Progress Tracking and Statistics](#progress-tracking-and-statistics)
7. [Configuration and Tuning](#configuration-and-tuning)
   - [Basic Configuration](#basic-configuration)
   - [Advanced Settings](#advanced-settings)
   - [Performance Tuning](#performance-tuning)
   - [Debug Options](#debug-options)
8. [Examples and Usage](#examples-and-usage)
   - [Basic Iteration in examples.py](#basic-iteration-in-examplespy)
   - [Programmatic Iteration Usage](#programmatic-iteration-usage)
   - [Interpreting Iteration Output](#interpreting-iteration-output)
   - [Debug Message Categories](#debug-message-categories)
9. [References](#references)

## Introduction

The ModelChecker's iteration system provides a framework for finding multiple semantically distinct models that satisfy or violate logical formulas. This capability is essential for understanding the full space of possible interpretations, discovering diverse counterexamples, and validating the robustness of logical principles across model variations.

The iteration system goes beyond simply finding multiple models—it ensures that each discovered model is meaningfully different from previous ones according to the semantic theory being used. This involves constraint generation, isomorphism detection, and theory-specific difference calculations.

Key insights this system provides:
- **Model Space Exploration**: Discover all structurally distinct ways formulas can be satisfied or violated
- **Counterexample Diversity**: Find qualitatively different failures, not just variations
- **Theory Comparison**: See how different semantic theories generate different model spaces
- **Robustness Testing**: Verify that logical principles hold across all possible interpretations

For the complete pipeline context including how models are generated, see [Models Pipeline](MODELS.md). For settings that control iteration behavior, see [Settings Management](BUILDER.md#settings-management).

## Overview

### What Iteration Means in ModelChecker

In the ModelChecker context, iteration means systematically finding multiple models that:

1. **Satisfy the logical constraints** - Each model must be valid for the given formulas
2. **Differ semantically** - Models must have different truth assignments or structural properties
3. **Avoid isomorphism** - Models should not be mere relabelings of the same structure
4. **Respect theory semantics** - Differences should be meaningful within the theory

```python
# Without iteration: Find one model
model = find_model(premises, conclusions)  # Single countermodel

# With iteration: Find multiple distinct models
models = find_models(premises, conclusions, count=5)  # Up to 5 different models
for i, model in enumerate(models):
    print(f"Model {i+1}: {model}")  # Each structurally distinct
    if i > 0:
        print(f"Differs from previous: {model.differences}")  # Theory-specific changes
```

The iteration system transforms model finding from a binary question ("Is there a countermodel?") into an exploration of the semantic landscape. Each new model reveals a different way the logical constraints can be satisfied, helping researchers understand not just whether their principles fail, but how many qualitatively different ways they can fail.

### Finding Structurally Distinct Countermodels

The system focuses on structural distinctness:

```
┌────────────────────────────────────────────────────────────────────┐
│ Iteration Process: Finding Structurally Distinct Models            │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│  Model 1: Basic countermodel                                       │
│  ┌─────────┐      ┌─────────┐                                      │
│  │   w1    │ ───▶ │   w2    │    A: true at w1, false at w2        │
│  │ A: true │      │ A: false│    Accessibility: bidirectional      │
│  └─────────┘ ◀─── └─────────┘                                      │
│                                                                    │
│  Model 2: Different world structure                                │
│  ┌─────────┐      ┌─────────┐      ┌─────────┐                     │
│  │   w1    │ ───▶ │   w2    │ ───▶ │   w3    │                     │
│  │ A: true │      │ A: false│      │ A: true │                     │
│  └─────────┘      └─────────┘      └─────────┘                     │
│  New feature: Additional world changes truth patterns              │
│                                                                    │
│  Model 3: Different accessibility                                  │
│  ┌─────────┐      ┌─────────┐                                      │
│  │   w1    │ ───▶ │   w2    │    A: true at both worlds            │
│  │ A: true │      │ A: true │    Accessibility: asymmetric         │
│  └─────────┘      └─────────┘    (w1→w2 but not w2→w1)             │
│                                                                    │
└────────────────────────────────────────────────────────────────────┘
```

Structural distinctness goes beyond mere relabeling since each model is required to represent a different semantic situation. The system detects when models are isomorphic (same structure with different labels) and continues searching for genuinely new structures.

### Theory-Specific Semantic Differences

Each theory defines what constitutes a "meaningful difference":

- **Logos**: Changes in verification/falsification patterns
- **Exclusion**: Different exclusion relations or witness assignments
- **Imposition**: Variations in imposition structures
- **Bimodal**: Different temporal or modal configurations

These semantic differences reflect each theory's core concepts: Logos tracks what makes sentences true/false (hyperintensional content), Exclusion monitors incompatibility relations, Imposition varies counterfactual dependencies, and Bimodal explores temporal-modal interactions.

### Use Cases for Iteration

1. **Semantic Exploration**: Understanding all possible models for a given formula set
2. **Robustness Testing**: Ensuring logical principles hold across all structural variations
3. **Counterexample Diversity**: Finding qualitatively different ways formulas can fail
4. **Theory Comparison**: Revealing how different semantic theories generate different model spaces
5. **Educational Demonstration**: Visualizing the variety of semantic interpretations

## The 'iterate' Setting

### Setting Format

The `iterate` setting specifies how many models to find:

```python
# In examples.py
EXAMPLE_settings = {
    'N': 4,             # 2^4 = 16 states for model construction
    'iterate': 3,       # Find 3 distinct models (not just isomorphic variants)
    'max_time': 10,     # 10 second timeout per model
    'expectation': True # Expecting countermodels (not theorems)
}

# Command line override
model-checker examples.py --iterate=5  # Override to find 5 models instead
```

The `iterate` setting controls how many structurally distinct models the system attempts to find. Setting it to 1 (default) finds just one model, while higher values trigger the iteration algorithm to search for additional models that differ meaningfully from those already found.

### Interaction with Other Settings

The `iterate` setting interacts with other configuration (see [Settings Management](BUILDER.md#settings-management) for complete settings documentation including visual flowcharts):

```python
# Iteration-specific settings
{
    'iterate': 5,                      # Primary: number of models to find
    'max_time': 10,                    # Overall timeout per model search
    'iteration_timeout': 1.0,          # Timeout for isomorphism checking
    'iteration_solver_timeout': 5.0,   # Z3 timeout per iteration attempt
    'max_invalid_attempts': 5,         # Give up after 5 invalid models in a row
    'iteration_attempts': 5,           # Try escape after 5 isomorphic models
    'escape_attempts': 3,              # Maximum escape strategies to try
}

# Theory settings affect iteration
{
    'N': 4,              # Larger N = exponentially more possible models (2^N states)
    'contingent': True,  # Requires both verifiers and falsifiers - reduces models
    'non_empty': True,   # No empty extensions - further restricts model space
}
```

```
┌────────────────────────────────────────────────────────────────────┐
│ How Settings Affect Iteration Model Space                          │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│  State Space Size:              Semantic Constraints:              │
│  N=3 → 8 states → Fast         contingent=True → Fewer models    │
│  N=4 → 16 states → Moderate    non_empty=True → Fewer models     │
│  N=5 → 32 states → Slower      disjoint=True → Fewer models      │
│  N=6 → 64 states → Very slow   non_null=True → Fewer models      │
│                                                                    │
│  Timeout Cascade:                                                  │
│  max_time (10s) ─────────────────────────┐                     │
│                                          │                     │
│  iteration_solver_timeout (5s) ─────────┤ Per attempt        │
│                                          │                     │
│  iteration_timeout (1s) ────────────────┘ Isomorphism check  │
│                                                                    │
└────────────────────────────────────────────────────────────────────┘
```

The interaction between state space size and semantic constraints determines how many distinct models exist and how hard they are to find. Larger N provides more room for variation but exponentially increases search complexity.

### Performance Implications

Iteration performance depends on:

1. **State space size** (2^N states)
2. **Constraint complexity**
3. **Theory semantics**
4. **Isomorphism checking overhead**

Performance characteristics by state space size:
- `N=3`: Fast iteration (8 states) - milliseconds per model
- `N=4`: Moderate (16 states) - sub-second per model
- `N=5`: Slower (32 states) - seconds per model
- `N=6+`: May struggle (64+ states) - exponential constraint complexity

The exponential growth occurs because each additional atomic proposition doubles the state space, and constraint generation must consider all possible state combinations for semantic properties.

### Default Behaviors

Without explicit configuration:

```python
# Default: No iteration
'iterate': 1  # Just find one model (standard behavior)

# When specified without value
'iterate': True  # Interpreted as iterate=2 (find one alternative)

# Automatic limits
if iterate > 2**(N-1):  # Can't have more distinct models than state combinations
    # Limit to reasonable maximum based on state space
    iterate = min(iterate, 2**(N-1))
```

The automatic limiting prevents requesting more models than could possibly exist - with N atomic propositions and 2^N states, there's a finite (though large) number of structurally distinct models possible.

## Iteration Algorithm

### Initial Model as Starting Point

The iteration process begins with a valid model:

```python
# Phase 1: Find initial model
initial_model = solve(constraints)  # Standard constraint solving
if not initial_model:
    return []  # No models exist - formula is theorem

models = [initial_model]  # Start collection with first model

# Phase 2: Find additional models
while len(models) < iterate:
    # Add constraints: new model must differ from ALL previous
    new_model = find_different_model(models)
    if new_model:
        models.append(new_model)
    else:
        break  # No more distinct models exist
```

```
┌────────────────────────────────────────────────────────────────────┐
│ Iteration Algorithm Flow                                           │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│  1. Initial Model Finding                                          │
│     ┌─────────────────┐      ┌──────────────────┐                  │
│     │ Frame + Model   │ ───▶ │ Z3 Solver        │ ──▶ Model 1      │
│     │ + Evaluation    │      │ solve()          │                  │
│     └─────────────────┘      └──────────────────┘                  │
│                                                                    │
│  2. Iterative Model Finding (repeat for each new model)            │
│     ┌─────────────────┐      ┌──────────────────┐                  │
│     │ Original        │      │ Difference       │                  │
│     │ Constraints     │ ───▶ │ Constraints      │                  │
│     └─────────────────┘      │ from Previous    │                  │
│            +                 └──────────────────┘                  │
│     ┌─────────────────┐              │                             │
│     │ All Previous    │              │                             │
│     │ Models          │              ▼                             │
│     └─────────────────┘      ┌──────────────────┐                  │
│                              │ Z3 with Added    │                  │
│                              │ Constraints      │ ──▶ Model N      │
│                              └──────────────────┘                  │
│                                                                    │
└────────────────────────────────────────────────────────────────────┘
```

The iteration algorithm builds on the standard model-finding process by adding difference constraints. Each iteration must find a model that satisfies the original logical constraints while differing from all previously found models.

### Difference Constraint Generation

Each new model must differ from all previous ones:

```python
def create_difference_constraint(previous_models):
    """Require difference from ALL previous models."""
    constraints = []  # Collect constraints for each previous model
    
    for prev_model in previous_models:
        differences = []  # Ways this model can differ
        
        # Semantic differences (theory-specific)
        for state in all_states:
            for atom in atoms:
                prev_value = prev_model.eval(verify(state, atom))  # What was true before
                differences.append(verify(state, atom) != prev_value)  # Require change
        
        # At least one difference required from this model
        constraints.append(Or(differences))  # Disjunction of all possible changes
    
    # Must differ from ALL previous models
    return And(constraints)  # Conjunction ensures difference from each
```

This constraint generation ensures semantic diversity - each new model must change at least one verification fact from every previous model. The nested structure (AND of ORs) guarantees that we don't just toggle back and forth between two configurations but explore genuinely new semantic territories.

### Isomorphism Detection and Avoidance

The system detects structurally identical models:

```python
def check_isomorphism(model1, model2):
    """Check if models are structurally identical."""
    # Create graph representations
    graph1 = create_model_graph(model1)  # Nodes: worlds, edges: accessibility
    graph2 = create_model_graph(model2)  # Properties: truth values at worlds
    
    # Check graph isomorphism with property matching
    return nx.is_isomorphic(
        graph1, graph2,
        node_match=lambda n1, n2: n1['props'] == n2['props']  # Same truth pattern
    )

# Avoidance strategy
if is_isomorphic(new_model, previous_models):
    # Add stronger constraints to break symmetry
    add_non_isomorphic_constraint(new_model)  # E.g., different world count
    continue  # Try again with additional constraints
```

Isomorphism detection prevents the system from presenting essentially identical models with different labels. Two models are isomorphic if you can relabel the worlds in one to exactly match the structure and truth values of the other - they represent the same semantic situation.

### Escape Strategies for Stuck Iterations

When finding too many isomorphic models:

```python
# Escalating escape strategies
escape_level = 0

while stuck_on_isomorphic_models:
    escape_level += 1
    
    if escape_level == 1:
        # Level 1: Different world count
        add_constraint(world_count != current_world_count)  # Simple structural change
        
    elif escape_level == 2:
        # Level 2: Significant structural change
        add_constraint(
            Or(
                world_count >= current + 2,  # Much larger model
                world_count <= current - 2   # Much smaller model
            )
        )
        
    elif escape_level == 3:
        # Level 3: Force specific semantic differences
        force_different_verification_pattern()  # Change truth-making patterns
        
    else:
        # Give up - no more distinct models in reasonable search space
        break
```

```
┌────────────────────────────────────────────────────────────────────┐
│ Escape Strategy Escalation                                         │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│  Found 5 isomorphic models → Trigger Level 1                       │
│  ┌────────────────────────────────────────────────────────────┐    │
│  │ Level 1: Require different world count                     │    │
│  │ Current: 2 worlds → Try: 1, 3, 4, ... worlds               │    │
│  └────────────────────────────────────────────────────────────┘    │
│                             │                                      │
│  Still finding isomorphic ──┘                                      │
│                                                                    │
│  ┌────────────────────────────────────────────────────────────┐    │
│  │ Level 2: Force significant structural change               │    │
│  │ Current: 3 worlds → Try: ≤1 or ≥5 worlds                   │    │
│  └────────────────────────────────────────────────────────────┘    │
│                             │                                      │
│  Still finding isomorphic ──┘                                      │
│                                                                    │
│  ┌────────────────────────────────────────────────────────────┐    │
│  │ Level 3: Force different semantic patterns                 │    │
│  │ Change which states verify/falsify propositions            │    │
│  └────────────────────────────────────────────────────────────┘    │
│                                                                    │
└────────────────────────────────────────────────────────────────────┘
```

The escalation strategy prevents the iteration from getting stuck in local regions of the model space where all variations are isomorphic. Each level forces increasingly dramatic changes to break out of symmetry patterns.

### Invalid Model Handling

Some models may be invalid (e.g., no possible worlds):

```python
def validate_model(model):
    """Check if model is valid."""
    if not model.has_possible_worlds():  # No worlds = degenerate model
        return False
    if not model.satisfies_frame_constraints():  # Violates theory axioms
        return False
    return True

# Handle invalid models gracefully
consecutive_invalid = 0
while searching:
    new_model = solve(constraints)
    
    if not validate_model(new_model):
        consecutive_invalid += 1
        if consecutive_invalid > max_invalid_attempts:  # Default: 5
            break  # Too many invalid models - likely exhausted space
        add_constraint(exclude_this_model(new_model))  # Don't try this again
        continue
    
    # Valid model found - reset counter
    consecutive_invalid = 0
    process_model(new_model)
```

Invalid models can arise when constraint interactions create degenerate cases (like models with no possible worlds) or when the solver finds technically satisfying assignments that violate framework assumptions. The system tracks consecutive failures to avoid infinite loops in exhausted search spaces.

## Theory-Specific Behaviors

### Logos: Verification/Falsification Differences

Logos theory focuses on hyperintensional differences:

```python
class LogosModelIterator(BaseModelIterator):
    def _calculate_differences(self, new_model, prev_model):
        differences = {
            "verify": {},    # Changes in what verifies sentences
            "falsify": {},   # Changes in what falsifies sentences
            "worlds": {},    # World structure changes (count, accessibility)
            "parthood": {}   # Mereological differences (fusion, overlap)
        }
        
        # Check verification changes - the heart of hyperintensional semantics
        for state in all_states:
            for atom in atoms:
                old_verify = prev_model.eval(verify(state, atom))  # Previous verifier
                new_verify = new_model.eval(verify(state, atom))  # Current verifier
                if old_verify != new_verify:
                    differences["verify"][f"{state} verifies {atom}"] = {
                        "old": old_verify,
                        "new": new_verify
                    }
        
        return differences
```

*See also: [`model_checker/theory_lib/logos/iterate.py`](../../Code/src/model_checker/theory_lib/logos/iterate.py)*

**Example output**:
```
=== DIFFERENCES FROM PREVIOUS MODEL ===
Verification Changes:
  □ verifies A: False → True      # Null state now makes A true
  a.b verifies B: True → False    # Fusion of a and b no longer makes B true
  
World Structure:
  World count: 2 → 3
  New world: a.b.c                # Fusion of all three atoms is now possible
  
Falsification Changes:
  c falsifies A: False → True     # State c now actively makes A false
```

The difference tracking reveals how hyperintensional content shifts between models - not just what's true where, but what makes things true (verifiers) and false (falsifiers).

### Exclusion: Witness and Exclusion Variations

Exclusion theory adds witness-specific differences:

```python
class ExclusionModelIterator(LogosModelIterator):
    def _calculate_differences(self, new_model, prev_model):
        # Get parent differences (verification/falsification from Logos)
        differences = super()._calculate_differences(new_model, prev_model)
        
        # Add exclusion-specific semantics
        differences["exclusions"] = {}  # Which states exclude each other
        differences["witnesses"] = {}   # World-state witness relations
        
        # Check exclusion relations - core of unilateral semantics
        for s1 in all_states:
            for s2 in all_states:
                old_excludes = prev_model.eval(excludes(s1, s2))  # Previous exclusion
                new_excludes = new_model.eval(excludes(s1, s2))  # Current exclusion
                if old_excludes != new_excludes:
                    differences["exclusions"][f"{s1} excludes {s2}"] = {
                        "old": old_excludes,
                        "new": new_excludes
                    }
        
        return differences
```

*See also: [`model_checker/theory_lib/exclusion/iterate.py`](../../Code/src/model_checker/theory_lib/exclusion/iterate.py)*

**Example output**:
```
=== DIFFERENCES FROM PREVIOUS MODEL ===
Exclusion Changes:
  a excludes b: False → True      # States a and b now incompatible
  
Witness Changes:
  witness(W1, a): True → False    # World W1 no longer witnesses state a
  witness(W2, b): False → True    # World W2 now witnesses state b
  
Coherence:
  States a and b now incoherent    # Cannot both be witnessed at same world
  
Negation Behavior:
  ¬A now true at W1               # Because W1 doesn't witness any A-verifier
```

Exclusion semantics implements Bernard & Champollion's unilateral approach where negation is primitive - ¬A is true when the world witnesses a state that excludes all A-verifiers, solving the False Premise Problem.

### Default: Classical Valuation Changes

Default theory uses simple truth value differences:

```python
class DefaultModelIterator(BaseModelIterator):
    def _create_difference_constraint(self, previous_models):
        # Focus on truth value changes at worlds - classical semantics
        constraints = []
        for prev_model in previous_models:
            differences = []  # Ways to differ from this model
            
            for world in worlds:
                for atom in atoms:
                    prev_truth = prev_model.eval(true_at(atom, world))  # Was A true at w?
                    differences.append(true_at(atom, world) != prev_truth)  # Flip it
            
            constraints.append(Or(differences))  # At least one truth value change
        
        return And(constraints)  # Differ from all previous models
```

Default iteration uses classical possible worlds semantics where models differ by changing which propositions are true at which worlds. This simpler approach contrasts with hyperintensional theories that track what makes propositions true.

### Bimodal: Temporal-Modal Variations

Bimodal theory varies temporal and modal structure:

```python
class BimodalModelIterator(BaseModelIterator):
    def _calculate_differences(self, new_model, prev_model):
        differences = {
            "temporal": {},   # Changes in time ordering (before relation)
            "modal": {},      # Changes in world accessibility
            "history": {}     # World-time state assignments h(w,t)
        }
        
        # Check temporal accessibility - which times come before others
        for t1 in times:
            for t2 in times:
                old_before = prev_model.eval(before(t1, t2))  # t1 < t2 previously?
                new_before = new_model.eval(before(t1, t2))  # t1 < t2 now?
                if old_before != new_before:
                    differences["temporal"][f"{t1} < {t2}"] = {
                        "old": old_before,
                        "new": new_before
                    }
        
        return differences
```

*See also: [`model_checker/theory_lib/bimodal/iterate.py`](../../Code/src/model_checker/theory_lib/bimodal/iterate.py)*

Bimodal iteration explores different temporal-modal structures: how time flows (linear vs branching), how worlds relate across time, and which world-states exist at which times. This reveals different ways necessity and temporality can interact.

### Imposition: Imposition Relation Changes

Imposition theory varies imposition structures:

```python
class ImpositionModelIterator(BaseModelIterator):
    def _create_difference_constraint(self, previous_models):
        # Focus on imposition relation changes - Fine's counterfactual semantics
        constraints = []
        for prev_model in previous_models:
            differences = []  # Ways imposition structure can change
            
            # Vary imposition relations: s1 imposed on s2 yields s3
            for s1 in states:
                for s2 in states:
                    for s3 in states:
                        prev_imp = prev_model.eval(impose(s1, s2, s3))  # Previous relation
                        differences.append(impose(s1, s2, s3) != prev_imp)  # Change it
            
            constraints.append(Or(differences))  # At least one imposition change
        
        return And(constraints)
```

*See also: [`model_checker/theory_lib/imposition/iterate.py`](../../Code/src/model_checker/theory_lib/imposition/iterate.py)*

Imposition iteration varies how states combine under counterfactual supposition. Different imposition structures yield different counterfactual dependencies - revealing multiple ways the same counterfactual can be true or false.

## Implementation Details

### BaseModelIterator Abstract Methods

To implement iteration for a new theory:

```python
class BaseModelIterator:
    """Base class for theory-specific model iteration."""
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate semantic differences between models.
        
        This is an abstract method that should be implemented by theory-specific subclasses.
        
        Returns:
            dict: Categorized differences by semantic feature
            
        Raises:
            NotImplementedError: If the subclass does not implement this method
        """
        raise NotImplementedError("This method must be implemented by a theory-specific subclass")
    
    def _create_difference_constraint(self, previous_models):
        """Create Z3 constraints ensuring difference from all previous.
        
        This is an abstract method that should be implemented by theory-specific subclasses.
        
        Returns:
            z3.ExprRef: Constraint expression (AND of ORs typically)
            
        Raises:
            NotImplementedError: If the subclass does not implement this method
        """
        raise NotImplementedError("This method must be implemented by a theory-specific subclass")
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Create constraints to avoid graph-isomorphic models.
        
        This is an abstract method that should be implemented by theory-specific subclasses.
        
        Returns:
            z3.ExprRef or None: Constraint to break symmetry
            
        Raises:
            NotImplementedError: If the subclass does not implement this method
        """
        raise NotImplementedError("This method must be implemented by a theory-specific subclass")
    
    def _create_stronger_constraint(self, isomorphic_model):
        """Create aggressive constraints when stuck on isomorphisms.
        
        This is an abstract method that should be implemented by theory-specific subclasses.
        
        Returns:
            z3.ExprRef or None: Strong escape constraint
            
        Raises:
            NotImplementedError: If the subclass does not implement this method
        """
        raise NotImplementedError("This method must be implemented by a theory-specific subclass")
```

*Full implementation: [`model_checker/iterate/core.py`](../../Code/src/model_checker/iterate/core.py)*

To implement iteration for a new theory, extend this base class and define what constitutes meaningful semantic differences in your theory. The framework handles the iteration mechanics - you specify what varies.

### Constraint Generation Strategies

Effective constraint generation patterns:

```python
# 1. Prioritized constraints (simple first)
def create_prioritized_constraints(previous_models):
    constraints = []  # Build up constraint list
    
    # Level 1: World count (fast to check, often effective)
    constraints.extend(world_count_constraints(previous_models))
    
    # Level 2: Truth values (moderate complexity)
    if len(constraints) < 10:  # Don't overwhelm solver
        constraints.extend(truth_value_constraints(previous_models))
    
    # Level 3: Semantic relations (expensive, many variables)
    if len(constraints) < 20:  # Last resort
        constraints.extend(relation_constraints(previous_models))
    
    return And(constraints)

# 2. Focused constraints (target likely differences)
def create_focused_constraints(previous_models):
    # Identify patterns in previous models
    patterns = analyze_model_patterns(previous_models)  # What's common?
    
    # Target uncommon features for variety
    return create_constraints_avoiding_patterns(patterns)

# 3. Incremental constraints (add constraints until different)
def create_incremental_constraints(previous_models):
    solver = z3.Solver()
    
    # Start with basic constraints
    solver.add(basic_difference_constraints(previous_models))
    
    # Add more constraints if still too similar
    while solver.check() == sat:
        model = solver.model()
        if not is_similar_to_previous(model, previous_models):
            return solver.assertions()  # Found good constraints
        solver.add(stronger_constraints(model))  # Need more difference
```

Effective constraint generation balances specificity (finding genuinely different models) with tractability (not overwhelming the solver). The prioritized approach works well in practice - simple constraints often suffice, avoiding expensive semantic relation constraints.

### Graph Representation for Isomorphism

Models are represented as directed graphs:

```python
class ModelGraph:
    def __init__(self, model_structure, z3_model):
        self.graph = self._create_graph()  # Build directed graph representation
    
    def _create_graph(self):
        G = nx.DiGraph()  # Directed graph for accessibility relations
        
        # Add worlds as nodes with their properties
        for i, world in enumerate(world_states):
            # Node properties include truth values at this world
            properties = {
                str(atom): str(z3_model.eval(true_at(atom, world)))
                for atom in atoms  # What's true here?
            }
            G.add_node(i, **properties)  # Node ID with properties
        
        # Add accessibility as directed edges
        for i, w1 in enumerate(world_states):
            for j, w2 in enumerate(world_states):
                if z3_model.eval(accessible(w1, w2)):  # Can reach w2 from w1?
                    G.add_edge(i, j)  # Add directed edge
        
        return G
    
    def get_invariant_hash(self):
        """Hash that's identical for isomorphic graphs."""
        invariants = {
            "degree_sequence": sorted(G.degree()),  # In/out connections
            "property_counts": count_node_properties(G),  # Truth patterns
            "triangle_count": nx.triangles(G)  # Structural feature
        }
        return hash(json.dumps(invariants))  # Same hash = likely isomorphic
```

*See also: [`model_checker/iterate/graph_utils.py`](../../Code/src/model_checker/iterate/graph_utils.py)*

Graph representation enables efficient isomorphism detection using NetworkX's algorithms. Models with the same graph structure (after relabeling) represent the same semantic situation and should be filtered out.

### Progress Tracking and Statistics

The system provides detailed progress information:

```python
class IterationProgress:
    """Real-time progress display for model finding."""
    def __init__(self, total, desc="Finding models"):
        self.total = total  # Target number of models
        self.start_time = time.time()
    
    def update(self, found, checked):
        elapsed = time.time() - self.start_time
        rate = checked / elapsed if elapsed > 0 else 0  # Models/second
        
        # Progress bar visualization
        progress = found / self.total
        bar = "█" * int(30 * progress) + "░" * int(30 * (1-progress))
        
        # Display with statistics
        print(f"\r{self.desc}: [{bar}] {found}/{self.total} "
              f"(checked {checked}, {rate:.1f}/s)", end="")

class IterationStatistics:
    """Collect and analyze iteration metrics."""
    def add_model(self, model, differences):
        self.stats.append({
            'world_count': len(model.worlds),  # Model size
            'difference_count': count_differences(differences),  # How different
            'solve_time': model.solve_time,  # Performance
            'iteration': len(self.stats) + 1  # Order found
        })
    
    def get_summary(self):
        return {
            'models_found': len(self.stats),
            'avg_solve_time': mean(s['solve_time'] for s in self.stats),
            'diversity_score': calculate_diversity(self.stats)  # Variety metric
        }
```

*See also: [`model_checker/iterate/progress.py`](../../Code/src/model_checker/iterate/progress.py) and [`model_checker/iterate/stats.py`](../../Code/src/model_checker/iterate/stats.py)*

Progress tracking provides real-time feedback during potentially long iteration searches, while statistics help analyze the quality and diversity of the found model set.

## Configuration and Tuning

### Basic Configuration

Start with simple iteration settings:

```python
# Minimal iteration - quick exploration
{
    'iterate': 2,        # Find 2 models (one alternative)
    'max_time': 10       # 10 second timeout per model
}

# Standard iteration - thorough analysis  
{
    'iterate': 5,        # Find 5 different models
    'max_time': 30,      # 30 seconds per model search
    'verbose': True      # Show progress bar and statistics
}
```

Start with minimal settings to verify iteration works for your formulas, then increase the count for more thorough exploration. The verbose flag helps monitor progress during longer searches.

### Advanced Settings

Fine-tune iteration behavior:

```python
# Complete iteration configuration with all options
{
    # Basic
    'iterate': 10,                    # Target: find 10 distinct models
    
    # Timeout cascade (each timeout is within the previous)
    'max_time': 60,                   # Overall timeout per model (outermost)
    'iteration_solver_timeout': 10.0, # Z3 timeout per iteration attempt
    'iteration_timeout': 2.0,         # Isomorphism check timeout (innermost)
    
    # Failure handling thresholds
    'max_invalid_attempts': 5,        # Give up after 5 invalid models in a row
    'iteration_attempts': 5,          # Try escape after 5 isomorphic models
    'escape_attempts': 3,             # Try at most 3 escape strategies
    
    # Theory-specific constraints
    'N': 4,                          # 2^4 = 16 states in model
    'contingent': True,              # Require verifiers AND falsifiers
}
```

These settings control how aggressively the system searches for new models and when it gives up. Lower timeouts mean faster iteration but might miss complex models; higher thresholds explore more thoroughly but take longer.

### Performance Tuning

Optimize for different scenarios:

```python
# Fast exploration (prioritize speed over completeness)
FAST_CONFIG = {
    'iterate': 3,                    # Just a few models
    'N': 3,                          # Small state space (8 states)
    'iteration_timeout': 0.5,        # Quick isomorphism checks
    'escape_attempts': 1             # Don't try hard to escape
}

# Thorough analysis (prioritize finding all variations)
THOROUGH_CONFIG = {
    'iterate': 20,                   # Many models wanted
    'N': 5,                          # Larger state space (32 states)
    'iteration_timeout': 5.0,        # Careful isomorphism detection
    'escape_attempts': 5,            # Try hard to find differences
    'max_invalid_attempts': 10       # Tolerate degenerate cases
}

# Memory-conscious (for complex theories with many operators)
MEMORY_CONFIG = {
    'iterate': 5,                    # Moderate model count
    'iteration_solver_timeout': 5.0, # Prevent constraint explosion
    'incremental_solving': True      # Build constraints gradually
}
```

Choose configurations based on your goals: FAST for quick semantic exploration, THOROUGH for exhaustive analysis, MEMORY for complex theories where constraint generation is expensive.

### Debug Options

Enable debugging for iteration issues:

```python
# Debug configuration for troubleshooting iteration issues
DEBUG_CONFIG = {
    'iterate': 2,                    # Small count for debugging
    'verbose': True,                 # Show all progress messages
    'show_progress': True,           # Display progress bar
    'print_constraints': True,       # Show Z3 difference constraints
    'debug_isomorphism': True,       # Log isomorphism check details
    'save_graphs': True              # Export model graphs for analysis
}

# Command line debugging
./dev_cli.py --iso-debug examples/iterate_test.py  # Enable debug logging

# Debug output locations
/tmp/isomorphism_debug.log       # Why models were considered isomorphic
/tmp/graph_debug.log             # Graph construction details
/tmp/iteration_constraints.smt2   # Actual Z3 constraints generated
```

Debug mode helps diagnose why iteration gets stuck or produces unexpected results. The constraint log shows exactly what differences the system is trying to enforce, while the isomorphism log explains why models were considered identical.

## Examples and Usage

### Basic Iteration in examples.py

Enable iteration in your examples:

```python
# theory_lib/logos/examples.py

# Simple iteration example - explore how disjunction can be true
ITERATE_EX_premises = ["A \\vee B"]  # A or B is true
ITERATE_EX_conclusions = ["A"]       # But A needn't be true
ITERATE_EX_settings = {
    'N': 3,                 # Small model space
    'iterate': 3,           # Find 3 different countermodels
    'expectation': True,    # Expecting to find countermodels
    'max_time': 10          # Quick timeout
}
ITERATE_EX_example = [
    ITERATE_EX_premises,
    ITERATE_EX_conclusions,
    ITERATE_EX_settings
]

# Complex iteration with semantic constraints
COMPLEX_ITER_settings = {
    'N': 4,                     # Larger state space
    'iterate': 5,               # Find 5 distinct models
    'contingent': True,         # A and B must have both verifiers and falsifiers
    'non_empty': True,          # No empty extensions allowed
    'iteration_timeout': 2.0,   # Moderate isomorphism checking
    'escape_attempts': 3        # Try escape strategies if stuck
}
```

Iteration examples demonstrate how the same logical relationship can be realized in multiple ways. The simple example shows different ways "A or B" can be true without A being true, while the complex example adds semantic constraints that limit the model space.

### Programmatic Iteration Usage

Use iteration in Python code:

```python
# Direct iteration
from model_checker.builder import BuildModule
from model_checker.theory_lib.logos import iterate_example

# Create example
module = BuildModule(args)
example = module.create_example("test", theory)

# Find multiple models
models = iterate_example(example, max_iterations=5)

# Process results
for i, model in enumerate(models):
    print(f"\n=== Model {i+1} ===")
    model.print_model()
    
    if i > 0:
        # Show differences
        diffs = model.model_differences
        print("\nDiffers from previous:")
        for category, changes in diffs.items():
            print(f"  {category}: {len(changes)} changes")

# Access iteration statistics
if hasattr(example, '_iterator'):
    stats = example._iterator.get_iteration_summary()
    print(f"\nFound {stats['total_models']} models")
    print(f"Average solve time: {stats['avg_solve_time']:.2f}s")
```

### Interpreting Iteration Output

Understanding iteration results:

```
$ model-checker examples/iterate_test.py

[ITERATION] Running ITERATE_EX

MODEL 1/3
══════════════════════════════════════════════════

Premises:
  A ∨ B: true                      # Given: A or B holds

Conclusions:
  A: false (countermodel found)    # A needn't be true

Model Structure:
  Worlds: w1
  Extensions:
    A: false at w1                 # A is false
    B: true at w1                  # B is true (making A∨B true)

[ITERATION] Searching for model 2/3...
Finding models: [████████████████░░░░░░░░░░░░] 2/3 (checked 4) 1.2s

MODEL 2/3
══════════════════════════════════════════════════

=== DIFFERENCES FROM PREVIOUS MODEL ===
Verification Changes:              # Hyperintensional differences
  □ verifies A: False → True      # Null state now verifies A
  □ verifies B: True → False     # Null state no longer verifies B

Structural Properties:
  Worlds: 1 → 2                   # Added complexity
  Added world: w2

Model Structure:
  Worlds: w1, w2
  Extensions:
    A: true at w1, false at w2     # Mixed truth values
    B: false at w1, true at w2     # Opposite pattern

[ITERATION] Searching for model 3/3...
[ITERATION] Found isomorphic model #5 - will try different constraints
[ITERATION] Applying stronger constraints (attempt 1/3)...

MODEL 3/3
══════════════════════════════════════════════════

=== DIFFERENCES FROM PREVIOUS MODEL ===
Truth Value Changes:
  A at w1: True → False           # Flipped at w1
  B at w2: True → False           # Now false everywhere

Structural Properties:
  Worlds: 2 (unchanged)            # Same world count
  
Model Structure:
  Worlds: w1, w2
  Extensions:
    A: false at w1, true at w2     # Still makes A∨B true at w2
    B: false at both worlds        # B uniformly false

[ITERATION] Successfully found all 3 requested models

=== Iteration Statistics ===
Total models found: 3              # All structurally distinct
Models checked: 7                  # Including rejected isomorphic ones
Isomorphic models skipped: 2       # Avoided duplicates
Average solve time: 0.4s           # Fast due to small N
```

### Debug Message Categories

Iteration produces various debug messages:

```python
# User-visible messages (always shown)
"[ITERATION] Searching for model 2/5..."
"[ITERATION] Found isomorphic model #3 - will try different constraints"
"[ITERATION] Successfully found all 5 requested models"
"[ITERATION] Found 3 distinct models (requested 5)"

# Debug messages (with --verbose)
"Solver check took 0.23 seconds, result: sat"
"Creating stronger constraints after 3 isomorphic models"
"Adding constraint to exclude invalid model"

# Error messages
"[ITERATION] Timeout exceeded after 30.0 seconds"
"[ITERATION] Too many consecutive invalid models (5) - no more valid models exist"
"[ITERATION] Exhausted 3 escape attempts - no more distinct models found"
```

## References

### Implementation Files
- `iterate/core.py` - BaseModelIterator framework
- `iterate/progress.py` - Progress tracking utilities
- `iterate/stats.py` - Statistics collection
- `iterate/graph_utils.py` - Graph-based isomorphism
- `theory_lib/*/iterate.py` - Theory-specific iterators

### Related Documentation
- [Architecture](ARCHITECTURE.md) - System design and iterator architecture
- [Workflow](WORKFLOW.md) - Using iteration in practice
- [Theory Library](../../Code/src/model_checker/theory_lib/README.md) - Theory implementations
- [Iterator README](../../Code/src/model_checker/iterate/README.md) - Technical details

### Academic References
- Graph Isomorphism Problem - Complexity and algorithms
- SMT-based Model Enumeration - Constraint generation strategies
- Semantic Difference Detection - Theory-specific approaches

---

[← Back to Methodology](README.md) | [Architecture →](ARCHITECTURE.md) | [Workflow →](../usage/WORKFLOW.md)
