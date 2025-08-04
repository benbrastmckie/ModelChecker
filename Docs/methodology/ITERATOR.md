# Iterator: Model Iteration and the 'iterate' Setting

[← Back to Methodology](README.md) | [Architecture →](../ARCHITECTURE.md) | [Workflow →](../usage/WORKFLOW.md)

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

The ModelChecker's iteration system provides a sophisticated framework for finding multiple semantically distinct models that satisfy or violate logical formulas. This capability is essential for understanding the full space of possible interpretations, discovering diverse counterexamples, and validating the robustness of logical principles across model variations.

The iteration system goes beyond simply finding multiple models—it ensures that each discovered model is meaningfully different from previous ones according to the semantic theory being used. This involves sophisticated constraint generation, isomorphism detection, and theory-specific difference calculations.

## Overview

### What Iteration Means in ModelChecker

In the ModelChecker context, iteration means systematically finding multiple models that:

1. **Satisfy the logical constraints** - Each model must be valid for the given formulas
2. **Differ semantically** - Models must have different truth assignments or structural properties
3. **Avoid isomorphism** - Models should not be mere relabelings of the same structure
4. **Respect theory semantics** - Differences should be meaningful within the theory

```python
# Without iteration: Find one model
model = find_model(premises, conclusions)

# With iteration: Find multiple distinct models
models = find_models(premises, conclusions, count=5)
for i, model in enumerate(models):
    print(f"Model {i+1}: {model}")
    if i > 0:
        print(f"Differs from previous: {model.differences}")
```

### Finding Structurally Distinct Countermodels

The system focuses on structural distinctness:

```
Model 1: Basic countermodel
- Worlds: {w1, w2}
- A true at w1, false at w2

Model 2: Structurally different
- Worlds: {w1, w2, w3}  # Different world count
- A true at w1 and w3, false at w2

Model 3: Different accessibility
- Worlds: {w1, w2}
- A true at both worlds  # Different valuation pattern
- w1 accesses w2 but not vice versa
```

### Theory-Specific Semantic Differences

Each theory defines what constitutes a "meaningful difference":

- **Logos**: Changes in verification/falsification patterns
- **Exclusion**: Different exclusion relations or witness assignments
- **Imposition**: Variations in imposition structures
- **Bimodal**: Different temporal or modal configurations

### Use Cases for Iteration

1. **Semantic Exploration**: Understanding all possible models
2. **Robustness Testing**: Ensuring principles hold across variations
3. **Counterexample Diversity**: Finding different ways formulas can fail
4. **Theory Comparison**: How different theories handle the same formulas
5. **Educational Demonstration**: Showing semantic variety

## The 'iterate' Setting

### Setting Format

The `iterate` setting specifies how many models to find:

```python
# In examples.py
EXAMPLE_settings = {
    'N': 4,
    'iterate': 3,      # Find 3 distinct models
    'max_time': 10,
    'expectation': True
}

# Command line override
model-checker examples.py --iterate=5
```

### Interaction with Other Settings

The `iterate` setting interacts with other configuration:

```python
# Iteration-specific settings
{
    'iterate': 5,                      # Primary: number of models
    'max_time': 10,                    # Timeout per model
    'iteration_timeout': 1.0,          # Timeout for isomorphism check
    'iteration_solver_timeout': 5.0,   # Z3 timeout per iteration
    'max_invalid_attempts': 5,         # Tolerance for invalid models
    'iteration_attempts': 5,           # Isomorphic models before escape
    'escape_attempts': 3,              # Maximum escape tries
}

# Theory settings affect iteration
{
    'N': 4,              # Larger N = more possible models
    'contingent': True,  # More constraints = fewer models
    'non_empty': True,   # Restrictions limit variety
}
```

### Performance Implications

Iteration performance depends on:

1. **State space size** (2^N states)
2. **Constraint complexity**
3. **Theory semantics**
4. **Isomorphism checking overhead**

Performance characteristics:
- `N=3`: Fast iteration (8 states)
- `N=4`: Moderate (16 states)
- `N=5`: Slower (32 states)
- `N=6+`: May struggle to find distinct models

### Default Behaviors

Without explicit configuration:

```python
# Default: No iteration
'iterate': 1  # Just find one model

# When specified without value
'iterate': True  # Interpreted as iterate=2

# Automatic limits
if iterate > 2^(N-1):
    # Limit to reasonable maximum
    iterate = min(iterate, 2^(N-1))
```

## Iteration Algorithm

### Initial Model as Starting Point

The iteration process begins with a valid model:

```python
# Phase 1: Find initial model
initial_model = solve(constraints)
if not initial_model:
    return []  # No models exist

models = [initial_model]

# Phase 2: Find additional models
while len(models) < iterate:
    new_model = find_different_model(models)
    if new_model:
        models.append(new_model)
    else:
        break  # No more distinct models
```

### Difference Constraint Generation

Each new model must differ from all previous ones:

```python
def create_difference_constraint(previous_models):
    """Require difference from ALL previous models."""
    constraints = []
    
    for prev_model in previous_models:
        differences = []
        
        # Semantic differences (theory-specific)
        for state in all_states:
            for atom in atoms:
                prev_value = prev_model.eval(verify(state, atom))
                differences.append(verify(state, atom) != prev_value)
        
        # At least one difference required
        constraints.append(Or(differences))
    
    # Must differ from all
    return And(constraints)
```

### Isomorphism Detection and Avoidance

The system detects structurally identical models:

```python
def check_isomorphism(model1, model2):
    """Check if models are structurally identical."""
    # Create graph representations
    graph1 = create_model_graph(model1)
    graph2 = create_model_graph(model2)
    
    # Check graph isomorphism
    return nx.is_isomorphic(
        graph1, graph2,
        node_match=lambda n1, n2: n1['props'] == n2['props']
    )

# Avoidance strategy
if is_isomorphic(new_model, previous_models):
    # Add stronger constraints
    add_non_isomorphic_constraint(new_model)
    continue  # Try again
```

### Escape Strategies for Stuck Iterations

When finding too many isomorphic models:

```python
# Escalating escape strategies
escape_level = 0

while stuck_on_isomorphic_models:
    escape_level += 1
    
    if escape_level == 1:
        # Level 1: Different world count
        add_constraint(world_count != current_world_count)
        
    elif escape_level == 2:
        # Level 2: Significant structural change
        add_constraint(
            Or(
                world_count >= current + 2,
                world_count <= current - 2
            )
        )
        
    elif escape_level == 3:
        # Level 3: Force specific differences
        force_different_verification_pattern()
        
    else:
        # Give up - no more distinct models
        break
```

### Invalid Model Handling

Some models may be invalid (e.g., no possible worlds):

```python
def validate_model(model):
    """Check if model is valid."""
    if not model.has_possible_worlds():
        return False
    if not model.satisfies_frame_constraints():
        return False
    return True

# Handle invalid models
consecutive_invalid = 0
while searching:
    new_model = solve(constraints)
    
    if not validate_model(new_model):
        consecutive_invalid += 1
        if consecutive_invalid > max_invalid_attempts:
            break  # Too many invalid models
        add_constraint(exclude_this_model(new_model))
        continue
    
    # Valid model found
    consecutive_invalid = 0
    process_model(new_model)
```

## Theory-Specific Behaviors

### Logos: Verification/Falsification Differences

Logos theory focuses on hyperintensional differences:

```python
class LogosModelIterator(BaseModelIterator):
    def _calculate_differences(self, new_model, prev_model):
        differences = {
            "verify": {},    # Changes in what verifies sentences
            "falsify": {},   # Changes in what falsifies sentences
            "worlds": {},    # World structure changes
            "parthood": {}   # Mereological differences
        }
        
        # Check verification changes
        for state in all_states:
            for atom in atoms:
                old_verify = prev_model.eval(verify(state, atom))
                new_verify = new_model.eval(verify(state, atom))
                if old_verify != new_verify:
                    differences["verify"][f"{state} verifies {atom}"] = {
                        "old": old_verify,
                        "new": new_verify
                    }
        
        return differences
```

**Example output**:
```
=== DIFFERENCES FROM PREVIOUS MODEL ===
Verification Changes:
  □ verifies A: False → True
  a.b verifies B: True → False
  
World Structure:
  World count: 2 → 3
  New world: a.b.c
```

### Exclusion: Witness and Exclusion Variations

Exclusion theory adds witness-specific differences:

```python
class ExclusionModelIterator(LogosModelIterator):
    def _calculate_differences(self, new_model, prev_model):
        # Get parent differences
        differences = super()._calculate_differences(new_model, prev_model)
        
        # Add exclusion-specific
        differences["exclusions"] = {}
        differences["witnesses"] = {}
        
        # Check exclusion relations
        for s1 in all_states:
            for s2 in all_states:
                old_excludes = prev_model.eval(excludes(s1, s2))
                new_excludes = new_model.eval(excludes(s1, s2))
                if old_excludes != new_excludes:
                    differences["exclusions"][f"{s1} excludes {s2}"] = {
                        "old": old_excludes,
                        "new": new_excludes
                    }
        
        return differences
```

**Example output**:
```
=== DIFFERENCES FROM PREVIOUS MODEL ===
Exclusion Changes:
  a excludes b: False → True
  
Witness Changes:
  witness(W1, a): True → False
  
Coherence:
  States a and b now incoherent
```

### Default: Classical Valuation Changes

Default theory uses simple truth value differences:

```python
class DefaultModelIterator(BaseModelIterator):
    def _create_difference_constraint(self, previous_models):
        # Focus on truth value changes at worlds
        constraints = []
        for prev_model in previous_models:
            differences = []
            
            for world in worlds:
                for atom in atoms:
                    prev_truth = prev_model.eval(true_at(atom, world))
                    differences.append(true_at(atom, world) != prev_truth)
            
            constraints.append(Or(differences))
        
        return And(constraints)
```

### Bimodal: Temporal-Modal Variations

Bimodal theory varies temporal and modal structure:

```python
class BimodalModelIterator(BaseModelIterator):
    def _calculate_differences(self, new_model, prev_model):
        differences = {
            "temporal": {},   # Changes in time relations
            "modal": {},      # Changes in possibility
            "history": {}     # World-time assignments
        }
        
        # Check temporal accessibility
        for t1 in times:
            for t2 in times:
                old_before = prev_model.eval(before(t1, t2))
                new_before = new_model.eval(before(t1, t2))
                if old_before != new_before:
                    differences["temporal"][f"{t1} < {t2}"] = {
                        "old": old_before,
                        "new": new_before
                    }
        
        return differences
```

### Imposition: Imposition Relation Changes

Imposition theory varies imposition structures:

```python
class ImpositionModelIterator(BaseModelIterator):
    def _create_difference_constraint(self, previous_models):
        # Focus on imposition relation changes
        constraints = []
        for prev_model in previous_models:
            differences = []
            
            # Vary imposition relations
            for s1 in states:
                for s2 in states:
                    for s3 in states:
                        prev_imp = prev_model.eval(impose(s1, s2, s3))
                        differences.append(impose(s1, s2, s3) != prev_imp)
            
            constraints.append(Or(differences))
        
        return And(constraints)
```

## Implementation Details

### BaseModelIterator Abstract Methods

To implement iteration for a new theory:

```python
class BaseModelIterator(ABC):
    """Abstract base class for model iteration."""
    
    @abstractmethod
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate semantic differences between models.
        
        Returns:
            dict: Categorized differences
        """
        pass
    
    @abstractmethod
    def _create_difference_constraint(self, previous_models):
        """Create Z3 constraints ensuring difference.
        
        Returns:
            z3.ExprRef: Constraint expression
        """
        pass
    
    @abstractmethod
    def _create_non_isomorphic_constraint(self, z3_model):
        """Create constraints to avoid isomorphism.
        
        Returns:
            z3.ExprRef or None: Constraint to break symmetry
        """
        pass
    
    @abstractmethod
    def _create_stronger_constraint(self, isomorphic_model):
        """Create aggressive constraints when stuck.
        
        Returns:
            z3.ExprRef or None: Strong escape constraint
        """
        pass
```

### Constraint Generation Strategies

Effective constraint generation patterns:

```python
# 1. Prioritized constraints (simple first)
def create_prioritized_constraints(previous_models):
    constraints = []
    
    # Level 1: World count (fast)
    constraints.extend(world_count_constraints(previous_models))
    
    # Level 2: Truth values (moderate)
    if len(constraints) < 10:
        constraints.extend(truth_value_constraints(previous_models))
    
    # Level 3: Semantic relations (slow)
    if len(constraints) < 20:
        constraints.extend(relation_constraints(previous_models))
    
    return And(constraints)

# 2. Focused constraints (likely differences)
def create_focused_constraints(previous_models):
    # Identify patterns in previous models
    patterns = analyze_model_patterns(previous_models)
    
    # Target uncommon features
    return create_constraints_avoiding_patterns(patterns)

# 3. Incremental constraints (add as needed)
def create_incremental_constraints(previous_models):
    solver = z3.Solver()
    
    # Start with basic constraints
    solver.add(basic_difference_constraints(previous_models))
    
    # Add more if still satisfiable
    while solver.check() == sat:
        model = solver.model()
        if not is_similar_to_previous(model, previous_models):
            return solver.assertions()
        solver.add(stronger_constraints(model))
```

### Graph Representation for Isomorphism

Models are represented as directed graphs:

```python
class ModelGraph:
    def __init__(self, model_structure, z3_model):
        self.graph = self._create_graph()
    
    def _create_graph(self):
        G = nx.DiGraph()
        
        # Add worlds as nodes
        for i, world in enumerate(world_states):
            # Node properties include truth values
            properties = {
                str(atom): str(z3_model.eval(true_at(atom, world)))
                for atom in atoms
            }
            G.add_node(i, **properties)
        
        # Add accessibility as edges
        for i, w1 in enumerate(world_states):
            for j, w2 in enumerate(world_states):
                if z3_model.eval(accessible(w1, w2)):
                    G.add_edge(i, j)
        
        return G
    
    def get_invariant_hash(self):
        """Hash that's same for isomorphic graphs."""
        invariants = {
            "degree_sequence": sorted(G.degree()),
            "property_counts": count_node_properties(G),
            "triangle_count": nx.triangles(G)
        }
        return hash(json.dumps(invariants))
```

### Progress Tracking and Statistics

The system provides detailed progress information:

```python
class IterationProgress:
    """Real-time progress display."""
    def __init__(self, total, desc="Finding models"):
        self.total = total
        self.start_time = time.time()
    
    def update(self, found, checked):
        elapsed = time.time() - self.start_time
        rate = checked / elapsed if elapsed > 0 else 0
        
        # Progress bar
        progress = found / self.total
        bar = "█" * int(30 * progress) + "░" * int(30 * (1-progress))
        
        # Display
        print(f"\r{self.desc}: [{bar}] {found}/{self.total} "
              f"(checked {checked}, {rate:.1f}/s)", end="")

class IterationStatistics:
    """Collect and analyze iteration metrics."""
    def add_model(self, model, differences):
        self.stats.append({
            'world_count': len(model.worlds),
            'difference_count': count_differences(differences),
            'solve_time': model.solve_time,
            'iteration': len(self.stats) + 1
        })
    
    def get_summary(self):
        return {
            'models_found': len(self.stats),
            'avg_solve_time': mean(s['solve_time'] for s in self.stats),
            'diversity_score': calculate_diversity(self.stats)
        }
```

## Configuration and Tuning

### Basic Configuration

Start with simple iteration settings:

```python
# Minimal iteration
{
    'iterate': 2,        # Find 2 models
    'max_time': 10       # 10 second timeout
}

# Standard iteration
{
    'iterate': 5,        # Find 5 models
    'max_time': 30,      # 30 seconds per model
    'verbose': True      # Show progress
}
```

### Advanced Settings

Fine-tune iteration behavior:

```python
# Complete iteration configuration
{
    # Basic
    'iterate': 10,                    # Target model count
    
    # Timeouts
    'max_time': 60,                   # Overall timeout per model
    'iteration_timeout': 2.0,         # Isomorphism check timeout
    'iteration_solver_timeout': 10.0, # Z3 timeout per iteration
    
    # Failure handling
    'max_invalid_attempts': 5,        # Invalid model tolerance
    'iteration_attempts': 5,          # Isomorphic models before escape
    'escape_attempts': 3,             # Maximum escape strategies
    
    # Theory-specific
    'N': 4,                          # State space size
    'contingent': True,              # Allow contingent propositions
}
```

### Performance Tuning

Optimize for different scenarios:

```python
# Fast exploration (prioritize speed)
FAST_CONFIG = {
    'iterate': 3,
    'N': 3,                          # Small state space
    'iteration_timeout': 0.5,        # Quick isomorphism checks
    'escape_attempts': 1             # Don't try too hard
}

# Thorough analysis (prioritize completeness)
THOROUGH_CONFIG = {
    'iterate': 20,
    'N': 5,                          # Larger state space
    'iteration_timeout': 5.0,        # Careful isomorphism checks
    'escape_attempts': 5,            # Try hard to find differences
    'max_invalid_attempts': 10       # Tolerate more failures
}

# Memory-conscious (large theories)
MEMORY_CONFIG = {
    'iterate': 5,
    'iteration_solver_timeout': 5.0,  # Prevent runaway solving
    'incremental_solving': True       # Add constraints gradually
}
```

### Debug Options

Enable debugging for iteration issues:

```python
# Debug configuration
DEBUG_CONFIG = {
    'iterate': 2,
    'verbose': True,
    'show_progress': True,
    'print_constraints': True,       # Show difference constraints
    'debug_isomorphism': True,       # Log isomorphism checks
    'save_graphs': True              # Save model graphs
}

# Command line debugging
./dev_cli.py --iso-debug examples/iterate_test.py

# Debug output location
/tmp/isomorphism_debug.log       # Isomorphism details
/tmp/graph_debug.log             # Graph construction
/tmp/iteration_constraints.smt2   # Z3 constraints
```

## Examples and Usage

### Basic Iteration in examples.py

Enable iteration in your examples:

```python
# theory_lib/logos/examples.py

# Simple iteration example
ITERATE_EX_premises = ["A \\vee B"]
ITERATE_EX_conclusions = ["A"]
ITERATE_EX_settings = {
    'N': 3,
    'iterate': 3,           # Find 3 models
    'expectation': True,    # Expect countermodels
    'max_time': 10
}
ITERATE_EX_example = [
    ITERATE_EX_premises,
    ITERATE_EX_conclusions,
    ITERATE_EX_settings
]

# Complex iteration with tuning
COMPLEX_ITER_settings = {
    'N': 4,
    'iterate': 5,
    'contingent': True,
    'non_empty': True,
    'iteration_timeout': 2.0,
    'escape_attempts': 3
}
```

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
  A ∨ B: true

Conclusions:
  A: false (countermodel found)

Model Structure:
  Worlds: w1
  Extensions:
    A: false at w1
    B: true at w1

[ITERATION] Searching for model 2/3...
Finding models: [████████████████░░░░░░░░░░░░] 2/3 (checked 4) 1.2s

MODEL 2/3
══════════════════════════════════════════════════

=== DIFFERENCES FROM PREVIOUS MODEL ===
Verification Changes:
  □ verifies A: False → True
  □ verifies B: True → False

Structural Properties:
  Worlds: 1 → 2
  Added world: w2

Model Structure:
  Worlds: w1, w2
  Extensions:
    A: true at w1, false at w2
    B: false at w1, true at w2

[ITERATION] Searching for model 3/3...
[ITERATION] Found isomorphic model #5 - will try different constraints
[ITERATION] Applying stronger constraints (attempt 1/3)...

MODEL 3/3
══════════════════════════════════════════════════

=== DIFFERENCES FROM PREVIOUS MODEL ===
Truth Value Changes:
  A at w1: True → False
  B at w2: True → False

Structural Properties:
  Worlds: 2 (unchanged)
  
Model Structure:
  Worlds: w1, w2
  Extensions:
    A: false at w1, true at w2
    B: false at both worlds

[ITERATION] Successfully found all 3 requested models

=== Iteration Statistics ===
Total models found: 3
Models checked: 7
Isomorphic models skipped: 2
Average solve time: 0.4s
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
- [Architecture](../ARCHITECTURE.md) - System design and iterator architecture
- [Workflow](WORKFLOW.md) - Using iteration in practice
- [Theory Library](../../Code/src/model_checker/theory_lib/README.md) - Theory implementations
- [Iterator README](../../Code/src/model_checker/iterate/README.md) - Technical details

### Academic References
- Graph Isomorphism Problem - Complexity and algorithms
- SMT-based Model Enumeration - Constraint generation strategies
- Semantic Difference Detection - Theory-specific approaches

---

[← Back to Methodology](README.md) | [Architecture →](../ARCHITECTURE.md) | [Workflow →](../usage/WORKFLOW.md)