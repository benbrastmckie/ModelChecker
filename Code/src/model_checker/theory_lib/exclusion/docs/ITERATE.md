# Exclusion Theory Model Iteration

This documentation explains how model iteration works specifically within the Exclusion theory, including its witness-aware semantics, exclusion relation handling, and practical usage patterns for unilateral negation.

## Overview

The Exclusion theory implements a witness-aware semantic framework built on unilateral negation, extending the Logos hyperintensional foundation with exclusion relations and coherence patterns. The ExclusionModelIterator leverages these exclusion-specific structures to find multiple distinct models that differ in exclusion relations, witness structures, and coherence patterns.

### Exclusion-Specific Distinctness

Unlike classical logic or even basic hyperintensional theories, Exclusion theory models can differ across several exclusion-specific dimensions:

1. **Exclusion Relations**: Which states exclude each other through incompatibility
2. **Witness Structures**: How witness predicates are assigned and constrained  
3. **Coherence Patterns**: Which states maintain coherence relationships
4. **Verification/Falsification**: Similar to Logos but with unilateral negation semantics
5. **Conflict Detection**: States that exhibit conflicting properties
6. **World Structure**: Inherited from Logos with exclusion-aware constraints

## Architecture

The ExclusionModelIterator extends LogosModelIterator with exclusion-specific implementations:

```python
class ExclusionModelIterator(LogosModelIterator):
    """Model iterator for exclusion theory with witness-aware semantics."""
    
    # Core exclusion difference detection
    def _calculate_differences(self, new_structure, previous_structure)
    def _calculate_verification_differences(self, new_structure, previous_structure)
    def _calculate_witness_differences(self, new_structure, previous_structure)  
    def _calculate_exclusion_differences(self, new_structure, previous_structure)
    
    # Exclusion-specific constraint generation
    def _create_difference_constraint(self, previous_models)
    def _create_witness_constraints(self, previous_models)
```

### Integration with Exclusion Theory Semantics

The iterator automatically works with exclusion theory's semantic primitives:

- **Verification**: Uses `semantics.verify(state, atom)` with unilateral negation
- **Exclusion Relations**: Uses `semantics.excludes(s1, s2)` for state incompatibility
- **Witness Registry**: Integrates with the witness predicate registry system
- **Coherence Checking**: Validates coherence patterns across model variations

## Usage

### Basic Example Configuration

```python
# In exclusion/examples.py
EX_CM_21_settings = {
    'N': 3,                    # 3 atomic propositions for manageable state space
    'possible': False,         # Disable possible state constraints
    'contingent': False,       # Use non-contingent propositions
    'non_empty': False,        # Allow empty witness sets
    'non_null': False,         # Allow null witness assignments
    'disjoint': False,         # Allow overlapping states
    'fusion_closure': False,   # Disable fusion closure
    'max_time': 5,             # Extended timeout for exclusion reasoning
    'iterate': 2,              # Find 2 distinct models
    'expectation': True,       # Expect countermodels
}

EX_CM_21_example = [
    ['A'],                     # Premises  
    ['B'],                     # Conclusions
    EX_CM_21_settings
]
```

### Advanced Configuration

```python
# For complex exclusion examples with witness constraints
settings = {
    'N': 4,                                # Larger state space for diversity
    'possible': False,                     # Focus on exclusion rather than possibility
    'contingent': False,                   # Non-contingent for cleaner exclusions
    'non_empty': True,                     # Ensure some witness assignments exist
    'non_null': True,                      # Require witness functions
    'iterate': 4,                          # Search for 4 models
    
    # Iteration-specific tuning for exclusion theory
    'max_invalid_attempts': 4,             # More tolerance for invalid models
    'iteration_attempts': 6,               # More isomorphism attempts for complex exclusions
    'escape_attempts': 5,                  # More escape attempts for exclusion constraints
    'iteration_timeout': 2.5,              # Extended isomorphism checking for exclusions
    'iteration_solver_timeout': 10000,     # Longer solver timeout for complex exclusion reasoning
}
```

### Programmatic Usage

```python
from model_checker.theory_lib.exclusion import iterate_example
from model_checker import BuildExample, get_theory

# Create an exclusion theory example
exclusion_theory = get_theory('exclusion')
example = BuildExample(
    "exclusion_example",
    exclusion_theory,
    premises=['A'],
    conclusions=['B'],
    settings={'N': 3, 'possible': False}
)

# Find multiple models with different exclusion patterns
models = iterate_example(example, max_iterations=3)

print(f"Found {len(models)} distinct exclusion models:")
for i, model in enumerate(models, 1):
    print(f"\n=== Model {i} ===")
    model.print_model()  # Shows exclusion relations and coherence patterns
    
    # Access exclusion-specific information
    exclusion_pairs = []
    for s1 in model.all_states:
        for s2 in model.all_states:
            if s1 != s2 and model.z3_model.eval(model.semantics.excludes(s1, s2)):
                exclusion_pairs.append((s1, s2))
    print(f"Exclusion relations: {len(exclusion_pairs)}")
```

## Semantic Difference Detection

### Exclusion Relation Changes

The most distinctive form of difference in exclusion theory involves changes in which states exclude each other:

```python
def _calculate_exclusion_differences(self, new_structure, previous_structure):
    """Calculate differences in exclusion relations."""
    exclusion_diffs = {}
    
    # Check exclusion changes between states
    for s1 in new_structure.all_states:
        for s2 in new_structure.all_states:
            if s1 == s2:
                continue
            
            old_excludes = previous_model.eval(semantics.excludes(s1, s2))
            new_excludes = new_model.eval(semantics.excludes(s1, s2))
            
            if bool(old_excludes) != bool(new_excludes):
                s1_str = bitvec_to_substates(s1, new_structure.N)
                s2_str = bitvec_to_substates(s2, new_structure.N)
                key = f"{s1_str} excludes {s2_str}"
                
                exclusion_diffs[key] = {
                    "old": bool(old_excludes),
                    "new": bool(new_excludes)
                }
```

**Example Output:**
```
Exclusion Changes:
  a.b excludes a.b: False ’ True
  ¡ excludes a.c: True ’ False
  b.c excludes ¡: False ’ True
```

### Verification Changes with Unilateral Negation

Exclusion theory uses unilateral negation, affecting how verification patterns differ:

```python
def _calculate_verification_differences(self, new_structure, previous_structure):
    """Calculate differences in verification between models."""
    verification_diffs = {}
    
    # Check each state/letter combination
    for state in new_structure.all_states:
        for letter in new_structure.sentence_letters:
            atom = letter.sentence_letter
            
            old_verify = previous_model.eval(semantics.verify(state, atom))
            new_verify = new_model.eval(semantics.verify(state, atom))
            
            if bool(old_verify) != bool(new_verify):
                state_str = bitvec_to_substates(state, new_structure.N)
                atom_str = letter.proposition
                key = f"{state_str} verifies {atom_str}"
                
                verification_diffs[key] = {
                    "old": bool(old_verify), 
                    "new": bool(new_verify)
                }
```

**Example Output:**
```
Verification Changes:
  ¡ verifies A: True ’ False
  a.b verifies B: False ’ True
  
Note: Exclusion theory uses unilateral negation - states either verify or remain neutral
```

### Witness Structure Changes

Exclusion theory handles witness predicates through a registry system:

```python
def _calculate_witness_differences(self, new_structure, previous_structure):
    """Calculate differences in witness assignments between models."""
    witness_diffs = {
        "changed_witnesses": {},
        "witness_counts": {
            "old": 0,
            "new": 0
        }
    }
    
    # Witness predicates in exclusion theory are handled through 
    # the witness registry system rather than direct semantic functions
    # Future enhancement: integrate with witness registry for detailed comparison
    
    return witness_diffs
```

## Constraint Generation

### Exclusion-Specific Difference Constraints

The iterator creates constraints ensuring new models differ in exclusion relations:

```python
def _create_difference_constraint(self, previous_models):
    """Create constraints that include witness diversity."""
    semantics = self.build_example.model_structure.semantics
    all_states = self.build_example.model_structure.all_states
    sentence_letters = self.build_example.model_structure.sentence_letters
    
    model_constraints = []
    
    for prev_model in previous_models:
        differences = []
        
        # Require different verification for at least one state/letter pair
        for state in all_states:
            for letter in sentence_letters:
                atom = letter.sentence_letter
                prev_verify = prev_model.eval(semantics.verify(state, atom))
                differences.append(semantics.verify(state, atom) != prev_verify)
        
        # Add exclusion relation differences between states
        for s1 in all_states[:min(3, len(all_states))]:
            for s2 in all_states[:min(3, len(all_states))]:
                if s1 == s2:
                    continue
                
                prev_excludes = prev_model.eval(semantics.excludes(s1, s2))
                differences.append(semantics.excludes(s1, s2) != prev_excludes)
        
        # Add witness-specific constraints (future enhancement)
        witness_constraints = self._create_witness_constraints([prev_model])
        if witness_constraints:
            differences.extend(witness_constraints)
        
        # Require at least one difference
        if differences:
            model_constraints.append(z3.Or(*differences))
    
    return z3.And(*model_constraints) if model_constraints else z3.BoolVal(True)
```

### Witness Constraint Integration

```python
def _create_witness_constraints(self, previous_models):
    """Create constraints to ensure witness diversity."""
    # Currently returns empty list since witness predicates are handled
    # differently in exclusion theory through the witness registry
    # Future enhancement: integrate with witness registry constraints
    return []
```

## Exclusion Theory-Specific Features

### Coherence Pattern Analysis

Exclusion theory models maintain coherence relationships that can vary between iterations:

```python
# Coherence-specific analysis (conceptual - not yet implemented)
def _analyze_coherence_patterns(self, model_structure):
    """Analyze coherence patterns in exclusion model."""
    coherence_info = {}
    
    # Identify coherent state clusters
    coherent_clusters = []
    for state in model_structure.all_states:
        if model_structure.z3_model.eval(model_structure.semantics.is_coherent(state)):
            coherent_clusters.append(state)
    
    coherence_info["coherent_states"] = len(coherent_clusters)
    coherence_info["incoherent_states"] = len(model_structure.all_states) - len(coherent_clusters)
    
    return coherence_info
```

### Self-Exclusion Detection

A unique feature of exclusion theory is self-exclusion where states can exclude themselves:

```python
def _detect_self_exclusions(self, model_structure):
    """Detect states that exclude themselves."""
    self_excluding_states = []
    
    for state in model_structure.all_states:
        if model_structure.z3_model.eval(model_structure.semantics.excludes(state, state)):
            self_excluding_states.append(state)
    
    return self_excluding_states
```

## Example Output Analysis

### Typical Iteration Session

```bash
$ ./dev_cli.py exclusion/examples.py
```

**Model 1 Output:**
```
MODEL 1/2
========================================
EXAMPLE EX_CM_21: there is a countermodel.

State Space:
  ¡ (empty state)
  a (atomic state)
  b (atomic state)
  a.b (fusion state)
  
Worlds: {a.b} (1 possible world)

Verification:
  ¡ verifies: nothing (neutral)
  a verifies: A
  b verifies: nothing (neutral)
  a.b verifies: A

Exclusion Relations:
  No exclusions in this model

Counterexample: A does not imply B at world a.b
```

**Progress During Iteration:**
```
Finding 2 models: [ˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆ] 1/2 (checked 1) 0.3s
Finding 2 models: [ˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆ] 1/2 (checked 3) 0.9s
Finding 2 models: [ˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆˆ] 2/2 (checked 4) 1.2s
Successfully found all 2 requested models
```

**Model 2 Differences:**
```
=== DIFFERENCES FROM PREVIOUS MODEL ===

Exclusion Changes:
  a.b excludes a.b: False ’ True

Verification Changes:
  ¡ verifies A: False ’ True
  a verifies A: True ’ False
  
Structural Properties:
  Worlds: 1 ’ 2
  Added worlds: [¡]
  Self-exclusions: Added [a.b excludes a.b]
```

## Performance Tuning

### Optimizing for Exclusion Reasoning

```python
# For complex exclusion patterns
exclusion_settings = {
    'N': 3,                            # Keep manageable for exclusion complexity
    'iterate': 3,                      # Reasonable model count
    'possible': False,                 # Focus on exclusions rather than possibility
    'non_empty': True,                 # Ensure meaningful witness structures
    'max_time': 5,                     # Extended timeout for exclusion reasoning
    'iteration_solver_timeout': 10000, # Extended solver timeout
    'iteration_timeout': 2.5,          # Longer isomorphism checking
}

# For witness-intensive examples
witness_settings = {
    'N': 4,                            # Larger space for witness diversity
    'iterate': 2,                      # Fewer models due to complexity
    'non_null': True,                  # Require witness functions
    'non_empty': True,                 # Ensure witness assignments exist
    'max_time': 8,                     # Much longer timeout
    'iteration_solver_timeout': 15000, # Very extended solver timeout
}
```

### Exclusion-Specific Optimization

```python
# For models with many exclusion relations
dense_exclusion_settings = {
    'N': 3,                            # Smaller space to manage exclusion complexity
    'iterate': 2,                      # Conservative model count
    'disjoint': False,                 # Allow complex overlapping patterns
    'fusion_closure': False,           # Reduce constraint complexity
    'iteration_attempts': 8,           # More attempts for exclusion isomorphism
    'escape_attempts': 6,              # More escape attempts
}
```

## Debugging and Analysis

### Debug Output Interpretation

```python
# Access detailed exclusion iteration information
iterator = example._iterator
for message in iterator.debug_messages:
    if 'exclusion' in message.lower():
        print(message)

# Typical exclusion debug sequence:
# [ITERATION] Searching for exclusion model 2/2...
# [EXCLUSION] Found different exclusion pattern - a.b now excludes itself
# [ITERATION] Found distinct exclusion model 2/2 in 1.2s
```

### Common Issues and Solutions

**Issue: "Models only differ in trivial exclusions"**
- **Cause**: Iterator finding models where exclusions don't affect verification
- **Solution**: Strengthen verification constraints, use witness constraints

**Issue: "Self-exclusion causing invalid models"**
- **Cause**: States excluding themselves making worlds impossible
- **Solution**: Add coherence constraints, review non_empty settings

**Issue: Slow exclusion iteration performance**
- **Cause**: Exclusion relations create complex constraint interactions
- **Solution**: Reduce N, limit exclusion pairs checked, increase timeouts

### Exclusion Analysis Tools

```python
# Analyze exclusion model diversity
def analyze_exclusion_diversity(models):
    exclusion_counts = []
    self_exclusion_counts = []
    
    for model in models:
        exclusion_count = 0
        self_exclusion_count = 0
        
        for s1 in model.all_states:
            for s2 in model.all_states:
                if model.z3_model.eval(model.semantics.excludes(s1, s2)):
                    exclusion_count += 1
                    if s1 == s2:
                        self_exclusion_count += 1
        
        exclusion_counts.append(exclusion_count)
        self_exclusion_counts.append(self_exclusion_count)
    
    print(f"Exclusion relation diversity: {set(exclusion_counts)}")
    print(f"Self-exclusion diversity: {set(self_exclusion_counts)}")
    print(f"Models with self-exclusions: {sum(1 for c in self_exclusion_counts if c > 0)}")

# Usage after iteration
models = iterate_example(example, max_iterations=4)
analyze_exclusion_diversity(models)
```

### Witness Registry Integration

```python
# Access witness registry information (future enhancement)
def analyze_witness_patterns(model):
    """Analyze witness predicate patterns in exclusion models."""
    # This would integrate with the witness registry system
    # to provide detailed witness assignment analysis
    pass
```

## Integration with Exclusion Notebooks

The Exclusion theory provides Jupyter notebooks demonstrating iteration:

```python
# In exclusion/notebooks/
from model_checker.theory_lib.exclusion import iterate_example

# Interactive exploration with exclusion-specific widgets
from model_checker.jupyter import ModelExplorer
explorer = ModelExplorer()
explorer.display()  # Shows exclusion-aware iteration controls

# Direct iteration in notebooks with exclusion focus
example = BuildExample("notebook_exclusion", exclusion_theory, 
                      premises=['A'], conclusions=['B'],
                      settings={'N': 3, 'possible': False})
models = iterate_example(example, max_iterations=3)

# Rich display of exclusion differences
for i, model in enumerate(models[1:], 2):
    print(f"=== Model {i} Exclusion Analysis ===")
    iterator.display_differences(models[i-2], model)
    
    # Show exclusion-specific information
    exclusions = [(s1, s2) for s1 in model.all_states 
                           for s2 in model.all_states
                           if model.z3_model.eval(model.semantics.excludes(s1, s2))]
    print(f"Exclusion relations: {len(exclusions)}")
```

## Future Enhancements

### Witness Registry Integration

The current implementation has placeholders for deeper witness registry integration:

```python
# Planned enhancement: witness constraint generation
def _create_witness_constraints(self, previous_models):
    """Enhanced witness constraints using registry system."""
    # Future: integrate with witness registry to create constraints
    # that ensure witness predicate diversity across models
    return []
```

### Coherence Pattern Analysis

```python
# Planned enhancement: coherence-aware iteration
def _calculate_coherence_differences(self, new_structure, previous_structure):
    """Calculate differences in coherence patterns."""
    # Future: analyze coherence relationships and ensure
    # iterations explore different coherence configurations
    pass
```

This comprehensive iteration system makes the Exclusion theory's witness-aware semantics and exclusion relations accessible for detailed semantic exploration, building on the robust foundation provided by the Logos theory iterator while adding exclusion-specific capabilities.