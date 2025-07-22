# Logos Theory Model Iteration

This documentation explains how model iteration works specifically within the Logos theory, including its hyperintensional semantics, difference detection mechanisms, and practical usage patterns.

## Overview

The Logos theory implements a sophisticated hyperintensional semantic framework that goes beyond classical truth-functional logic. The LogosModelIterator leverages this rich semantic structure to find multiple distinct models that differ in meaningful ways according to the theory's hyperintensional distinctions.

### Hyperintensional Distinctness

Unlike classical logic where models are distinguished primarily by truth value assignments, Logos theory models can differ across multiple semantic dimensions:

1. **Verification/Falsification**: Which states verify or falsify sentence letters
2. **World Structure**: Which states count as possible worlds vs. impossible/merely possible states  
3. **Mereological Relations**: Part-whole relationships between states
4. **Modal Structure**: Accessibility relations for necessity and possibility
5. **Constitutive Relations**: Grounding and essence relationships between propositions
6. **Counterfactual Structure**: Similarity orderings and selection functions

## Architecture

The LogosModelIterator extends BaseModelIterator with Logos-specific implementations:

```python
class LogosModelIterator(BaseModelIterator):
    """Model iterator for the logos theory with hyperintensional semantics."""
    
    # Core difference detection
    def _calculate_differences(self, new_structure, previous_structure)
    
    # Constraint generation for semantic differences  
    def _create_difference_constraint(self, previous_models)
    
    # Structural isomorphism handling
    def _create_non_isomorphic_constraint(self, z3_model)
    def _create_stronger_constraint(self, isomorphic_model)
```

### Integration with Logos Subtheories

The iterator automatically adapts to different Logos subtheory configurations:

- **Extensional**: Basic verification/falsification differences
- **Modal**: Adds necessity/possibility and accessibility relation differences
- **Constitutive**: Incorporates grounding, essence, and identity relation differences
- **Counterfactual**: Includes similarity ordering and counterfactual evaluation differences  
- **Relevance**: Adds content-based relevance relation differences

## Usage

### Basic Example Configuration

```python
# In logos/subtheories/counterfactual/examples.py
CF_CM_1_settings = {
    'N': 6,                    # 6 atomic propositions for rich state space
    'contingent': True,        # Allow contingent valuations
    'non_null': True,          # Require non-empty witness sets
    'non_empty': True,         # Require non-empty state space
    'disjoint': False,         # Allow overlapping states
    'max_time': 1,             # Base timeout for finding models
    'iterate': 3,              # Find 3 distinct models
    'expectation': True,       # Expect countermodels
}

CF_CM_1_example = [
    ['¬A', '(A ¡’ C)'],                    # Premises
    ['((A ' B) ¡’ C)'],                    # Conclusions  
    CF_CM_1_settings
]
```

### Advanced Configuration

```python
# For complex counterfactual examples
settings = {
    'N': 4,                                # Manageable state space
    'contingent': True,                    # Enable contingent propositions
    'non_null': True,                      # Ensure witness functions exist
    'non_empty': True,                     # Prevent empty models
    'iterate': 5,                          # Search for 5 models
    
    # Iteration-specific tuning
    'max_invalid_attempts': 3,             # Fewer retries for invalid models
    'iteration_attempts': 7,               # More isomorphism attempts
    'escape_attempts': 4,                  # More escape attempts  
    'iteration_timeout': 2.0,              # Longer isomorphism checking
    'iteration_solver_timeout': 8000,      # Extended solver timeout
}
```

### Programmatic Usage

```python
from model_checker.theory_lib.logos import iterate_example
from model_checker import BuildExample, get_theory

# Create a logos theory example
logos_theory = get_theory('logos')
example = BuildExample(
    "counterfactual_antecedent_strengthening",
    logos_theory,
    premises=['¬A', '(A ¡’ C)'],
    conclusions=['((A ' B) ¡’ C)'],
    settings={'N': 4, 'contingent': True}
)

# Find multiple models
models = iterate_example(example, max_iterations=3)

print(f"Found {len(models)} distinct counterfactual models:")
for i, model in enumerate(models, 1):
    print(f"\n=== Model {i} ===")
    model.print_model()  # Shows hyperintensional structure
    
    # Access model-specific information
    world_states = [s for s in model.all_states if model.semantics.is_world(s)]
    print(f"Possible worlds: {len(world_states)}")
```

## Semantic Difference Detection

### Verification/Falsification Changes

The most basic form of difference in Logos theory involves changes in which states verify or falsify sentence letters:

```python
def _calculate_verification_differences(self, new_structure, previous_structure):
    """Detect changes in verification and falsification patterns."""
    differences = {"verification": {}, "falsification": {}}
    
    # Compare verification for each state/letter pair
    for state in all_states:
        for letter in sentence_letters:
            atom = letter.sentence_letter
            
            # Check verification changes
            old_verifies = previous_model.eval(semantics.verify(state, atom))
            new_verifies = new_model.eval(semantics.verify(state, atom))
            if bool(old_verifies) != bool(new_verifies):
                differences["verification"][f"{state_name} verifies {atom_name}"] = {
                    "old": bool(old_verifies), "new": bool(new_verifies)
                }
```

**Example Output:**
```
Verification Changes:
  ¡ verifies A: False ’ True
  a.b verifies B: True ’ False
  a.c falsifies C: False ’ True
```

### World Structure Changes

Changes in which states count as possible worlds represent significant hyperintensional differences:

```python
def _calculate_world_differences(self, new_structure, previous_structure):
    """Detect changes in world structure."""
    differences = {"worlds": {"added": [], "removed": []}}
    
    # Find states that changed world status
    for state in all_states:
        old_is_world = bool(previous_model.eval(semantics.is_world(state)))
        new_is_world = bool(new_model.eval(semantics.is_world(state)))
        
        if old_is_world and not new_is_world:
            differences["worlds"]["removed"].append(state_name)
        elif not old_is_world and new_is_world:
            differences["worlds"]["added"].append(state_name)
```

**Example Output:**
```
Structural Properties:
  Worlds: 2 ’ 3
  Added worlds: [a.c]
  Removed worlds: []
  Possible states: {¡, a, b, a.b} ’ {¡, a, b, a.b, c, a.c}
```

### Modal Relation Changes

For modal subtheories, the iterator detects changes in accessibility relations:

```python
def _calculate_modal_differences(self, new_structure, previous_structure):
    """Detect changes in modal accessibility."""
    differences = {"accessibility": {}}
    
    # Compare accessibility between world pairs  
    for world1 in world_states:
        for world2 in world_states:
            old_accessible = bool(previous_model.eval(semantics.accessible(world1, world2)))
            new_accessible = bool(new_model.eval(semantics.accessible(world1, world2)))
            
            if old_accessible != new_accessible:
                differences["accessibility"][f"{world1_name} ’ {world2_name}"] = {
                    "old": old_accessible, "new": new_accessible
                }
```

### Constitutive Relation Changes

For constitutive subtheories, differences in grounding and essence relations are tracked:

```python
def _calculate_constitutive_differences(self, new_structure, previous_structure):
    """Detect changes in grounding and essence relations.""" 
    differences = {"grounding": {}, "essence": {}}
    
    # Check grounding relation changes
    for prop1 in propositions:
        for prop2 in propositions:
            if prop1 != prop2:
                old_grounds = bool(previous_model.eval(semantics.grounds(prop1, prop2)))
                new_grounds = bool(new_model.eval(semantics.grounds(prop1, prop2)))
                
                if old_grounds != new_grounds:
                    differences["grounding"][f"{prop1} d {prop2}"] = {
                        "old": old_grounds, "new": new_grounds
                    }
```

## Constraint Generation

### Basic Difference Constraints

The iterator creates constraints ensuring new models differ semantically from previous ones:

```python
def _create_difference_constraint(self, previous_models):
    """Create constraints requiring semantic differences."""
    model_constraints = []
    
    for prev_model in previous_models:
        differences = []
        
        # Verification/falsification differences
        for state in all_states:
            for letter in sentence_letters:
                atom = letter.sentence_letter
                prev_verifies = prev_model.eval(semantics.verify(state, atom))
                prev_falsifies = prev_model.eval(semantics.falsify(state, atom))
                
                differences.extend([
                    semantics.verify(state, atom) != prev_verifies,
                    semantics.falsify(state, atom) != prev_falsifies
                ])
        
        # World structure differences
        for state in all_states:
            prev_world = prev_model.eval(semantics.is_world(state))
            differences.append(semantics.is_world(state) != prev_world)
        
        # Possibility differences  
        for state in all_states:
            prev_possible = prev_model.eval(semantics.is_possible(state))
            differences.append(semantics.is_possible(state) != prev_possible)
```

### Smart Constraint Ordering

The Logos iterator implements prioritized constraint generation for better performance:

```python
def _get_constraint_generators(self):
    """Return constraint generators in priority order."""
    generators = [
        ("world_structure", self._generate_world_constraints),
        ("verification", self._generate_verification_constraints),
        ("part_relations", self._generate_part_constraints),
    ]
    
    # Add subtheory-specific generators
    if self._has_modal_operators():
        generators.append(("modal_relations", self._generate_modal_constraints))
    if self._has_constitutive_operators():
        generators.append(("constitutive_relations", self._generate_constitutive_constraints))
        
    return generators
```

### Isomorphism Breaking

When models are structurally isomorphic, stronger constraints force meaningful differences:

```python
def _create_non_isomorphic_constraint(self, z3_model):
    """Break structural symmetries between models."""
    try:
        constraints = []
        
        # Force specific world count differences
        world_count = sum(1 for s in all_states if bool(z3_model.eval(semantics.is_world(s))))
        if world_count > 1:
            # Require different number of worlds
            world_constraints = [semantics.is_world(s) for s in all_states]
            constraints.append(z3.Sum(world_constraints) != world_count)
        
        # Force asymmetric verification patterns
        if len(sentence_letters) >= 2:
            letter1, letter2 = sentence_letters[:2]
            state = all_states[0]
            constraints.append(
                semantics.verify(state, letter1) != semantics.verify(state, letter2)
            )
        
        return z3.Or(*constraints) if constraints else None
    except:
        return None
```

## Subtheory-Specific Features

### Counterfactual Iteration

For counterfactual examples, the iterator focuses on similarity ordering and selection function differences:

```python
# Counterfactual-specific difference detection
def _calculate_counterfactual_differences(self, new_structure, previous_structure):
    """Detect changes in counterfactual evaluation patterns."""
    differences = {"counterfactuals": {}}
    
    # Test counterfactual operators from the premises/conclusions
    for cf_formula in self._extract_counterfactuals():
        antecedent, consequent = cf_formula.antecedent, cf_formula.consequent
        
        for world in world_states:
            old_cf_true = bool(previous_model.eval(
                semantics.counterfactual(world, antecedent, consequent)
            ))
            new_cf_true = bool(new_model.eval(
                semantics.counterfactual(world, antecedent, consequent)  
            ))
            
            if old_cf_true != new_cf_true:
                differences["counterfactuals"][f"{antecedent} ¡’ {consequent} at {world}"] = {
                    "old": old_cf_true, "new": new_cf_true
                }
```

### Modal Iteration

Modal subtheories track accessibility relation changes:

```python
def _calculate_modal_differences(self, new_structure, previous_structure):
    """Focus on modal accessibility and necessity/possibility patterns."""
    differences = {"modal": {"accessibility": {}, "necessity": {}}}
    
    # Accessibility changes
    world_states = [s for s in all_states if semantics.is_world(s)]
    for w1 in world_states:
        for w2 in world_states:
            old_acc = bool(previous_model.eval(semantics.accessible(w1, w2)))
            new_acc = bool(new_model.eval(semantics.accessible(w1, w2)))
            if old_acc != new_acc:
                differences["modal"]["accessibility"][f"{w1} ’ {w2}"] = {
                    "old": old_acc, "new": new_acc
                }
    
    # Necessity pattern changes for sentence letters
    for world in world_states:
        for letter in sentence_letters:
            old_nec = bool(previous_model.eval(semantics.necessary(world, letter)))
            new_nec = bool(new_model.eval(semantics.necessary(world, letter)))
            if old_nec != new_nec:
                differences["modal"]["necessity"][f"¡{letter} at {world}"] = {
                    "old": old_nec, "new": new_nec
                }
```

## Example Output Analysis

### Typical Iteration Session

```bash
$ ./dev_cli.py logos/subtheories/counterfactual/examples.py
```

**Model 1 Output:**
```
MODEL 1/3
========================================
EXAMPLE CF_CM_1: there is a countermodel.

State Space:
  ¡ (empty state)
  a (atomic state)  
  b (atomic state)
  a.b (fusion state)
  
Worlds: {a.b} (1 possible world)

Verification:
  ¡ verifies: ¬A
  a verifies: A  
  b verifies: nothing
  a.b verifies: A

Counterfactual Evaluation:
  A ¡’ C: True at a.b
  (A ' B) ¡’ C: False at a.b   Counterexample found
```

**Progress During Iteration:**
```
Finding 3 models: [ˆˆˆˆˆˆˆˆˆˆ‘‘‘‘‘‘‘‘‘‘] 1/3 (checked 1) 0.2s
Finding 3 models: [ˆˆˆˆˆˆˆˆˆˆ‘‘‘‘‘‘‘‘‘‘] 1/3 (checked 3) 0.8s  
Finding 3 models: [ˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆ‘‘‘‘] 2/3 (checked 4) 1.1s
Finding 3 models: [ˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆ] 3/3 (checked 6) 1.7s
Successfully found all 3 requested models
```

**Model 2 Differences:**
```
=== DIFFERENCES FROM PREVIOUS MODEL ===

Verification Changes:
  ¡ verifies A: False ’ True
  a verifies ¬A: True ’ False
  
Structural Properties:
  Worlds: 1 ’ 2
  Added worlds: [¡]
  
Counterfactual Changes:
  A ¡’ C at ¡: True ’ False
  (A ' B) ¡’ C at ¡: False ’ True
```

**Model 3 Differences:**  
```
=== DIFFERENCES FROM PREVIOUS MODEL ===

Structural Properties:
  Worlds: 2 ’ 1
  Removed worlds: [¡]
  Added worlds: [b.c]
  
Verification Changes:
  b.c verifies B: False ’ True
  b.c verifies C: False ’ True
  
Part-Whole Changes:
  c ‘ b.c: False ’ True
  
Modal Changes:
  ¡{A ¡’ C} at b.c: True ’ False
```

## Performance Tuning

### Optimizing for Large State Spaces

```python
# For N > 4, use focused constraints
settings = {
    'N': 6,
    'iterate': 3,
    
    # Performance tuning
    'iteration_solver_timeout': 15000,  # 15 second solver timeout
    'iteration_timeout': 3.0,          # 3 second isomorphism timeout
    'max_invalid_attempts': 2,         # Fewer invalid attempts
    'escape_attempts': 5,              # More escape attempts for complex space
}
```

### Subtheory-Specific Optimization

```python
# For counterfactual subtheory (computationally intensive)
counterfactual_settings = {
    'N': 4,                            # Keep state space manageable
    'iterate': 3,                      # Reasonable model count
    'contingent': True,                # Required for meaningful counterfactuals
    'non_null': True,                  # Ensure witness functions exist
    'max_time': 2,                     # Extended base timeout
    'iteration_solver_timeout': 12000, # Extended solver timeout
}

# For modal subtheory (lighter computational load)  
modal_settings = {
    'N': 5,                            # Larger state space acceptable
    'iterate': 5,                      # More models feasible
    'max_time': 1,                     # Standard timeout sufficient
    'iteration_solver_timeout': 6000,  # Standard solver timeout
}
```

## Debugging and Analysis

### Debug Output Interpretation

```python
# Access detailed iteration information
iterator = example._iterator
for message in iterator.debug_messages:
    if message.startswith('[ITERATION]'):
        print(message)

# Typical debug sequence:
# [ITERATION] Searching for model 2/3...
# [ITERATION] Found distinct model 2/3 in 0.8s
# [ITERATION] Searching for model 3/3... 
# [ITERATION] Found isomorphic model #3 - will try different constraints
# [ITERATION] Found distinct model 3/3 in 1.2s
```

### Common Issues and Solutions

**Issue: "Too many consecutive invalid models"**
- **Cause**: Constraints generating models with no possible worlds
- **Solution**: Review world-generation constraints, ensure non_empty: True

**Issue: "Exhausted escape attempts for isomorphic models"**  
- **Cause**: Iterator stuck finding structurally identical models
- **Solution**: Strengthen non-isomorphic constraints, reduce model count

**Issue: Slow iteration performance**
- **Cause**: Large state space (N > 5) or complex counterfactual reasoning
- **Solution**: Reduce N, increase solver timeout, use focused constraints

### Model Analysis Tools

```python
# Analyze model diversity
def analyze_model_diversity(models):
    world_counts = [len([s for s in m.all_states if m.semantics.is_world(s)]) 
                   for m in models]
    verification_patterns = []
    
    for model in models:
        pattern = {}
        for state in model.all_states:
            for letter in model.sentence_letters:
                if model.z3_model.eval(model.semantics.verify(state, letter.sentence_letter)):
                    pattern[f"{state}¨{letter}"] = True
        verification_patterns.append(pattern)
    
    print(f"World count diversity: {set(world_counts)}")
    print(f"Unique verification patterns: {len(set(str(p) for p in verification_patterns))}")

# Usage after iteration
models = iterate_example(example, max_iterations=5)
analyze_model_diversity(models)
```

## Integration with Logos Notebooks

The Logos theory provides Jupyter notebooks that demonstrate iteration in action:

```python
# In logos/notebooks/
from model_checker.theory_lib.logos import iterate_example

# Interactive exploration with widgets
from model_checker.jupyter import ModelExplorer
explorer = ModelExplorer()
explorer.display()  # Shows iteration controls

# Direct iteration in notebooks
example = BuildExample("notebook_example", logos_theory, ...)  
models = iterate_example(example, max_iterations=3)

# Rich display of differences
for i, model in enumerate(models[1:], 2):
    print(f"=== Model {i} Differences ===") 
    iterator.display_differences(models[i-2], model)
```

This comprehensive iteration system makes the Logos theory's rich hyperintensional structure accessible for detailed semantic exploration and analysis.