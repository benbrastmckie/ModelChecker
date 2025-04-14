# Model Display Improvements for Iteration

This document outlines the implementation plan for improving the display of differences between consecutive models during iteration, with a focus on modularity and theory-specific extensibility.

## Current Implementation Analysis

Currently, when iterating through multiple models, differences are calculated in `_calculate_differences` within `iterate.py` and stored as:
```python
differences = {
    "sentence_letters": {},
    "semantic_functions": {},
    "model_structure": {}
}
```

However, the display of these differences has several limitations:
- No consistent color formatting matching the main display
- Basic structure that doesn't highlight the most important changes
- No direct connection to how the state space itself has changed
- Proposition changes are shown with internal representations rather than formatted like other parts of the output
- **Most critically:** The difference logic is not appropriately customized for each theory's specific semantic primitives

## Architecture Principles

To ensure a truly modular and theory-specific implementation:

1. **Theory-Driven Difference Detection**:
   - Each theory should define what constitutes a meaningful difference based on its semantic primitives
   - The bimodal theory might track changes in times, world-time pairs, and accessibility across times
   - The default theory might track changes in possible states, worlds, and part-whole relationships

2. **Separation of Concerns**:
   - `iterate.py` should provide a framework for difference detection but defer to theory-specific methods
   - Each theory's `ModelStructure` class should implement its own difference detection logic
   - Display of differences should be handled by each theory's own display methods

3. **Extension Mechanism**:
   - Define protocol methods that theories can implement to participate in difference detection
   - Provide fallback implementations for theories that don't implement custom difference detection

4. **Consistent Interfaces**:
   - All theories should implement the same method signatures for difference detection and display
   - Difference data structures can vary by theory but should follow consistent patterns

## Implementation Plan

### 1. Theory-Specific Difference Detection Protocol

First, define a protocol in `iterate.py` that delegates difference detection to the theory:

```python
def _calculate_differences(self, new_structure, previous_structure):
    """Calculate differences between two model structures.
    
    This method delegates to theory-specific difference detection by:
    1. First delegating to the theory's calculate_model_differences method if available
    2. Falling back to basic sentence letter and function comparison if not
    
    Args:
        new_structure: The new model structure
        previous_structure: The previous model structure to compare against
        
    Returns:
        dict: Structured differences between the models, with content specific to the theory
    """
    # Initialize an empty differences structure
    differences = {}
    
    # First, try to delegate to theory-specific difference detection
    if hasattr(new_structure, 'calculate_model_differences'):
        try:
            # Call the theory's own difference detection method
            theory_differences = new_structure.calculate_model_differences(previous_structure)
            if theory_differences:
                differences.update(theory_differences)
        except Exception as e:
            logger.warning(f"Error in theory-specific difference detection: {e}")
    
    # If no theory-specific differences detected, fall back to basic comparison
    if not differences:
        differences = self._calculate_basic_differences(new_structure, previous_structure)
    
    # Store the differences with the new structure
    new_structure.model_differences = differences
    
    # Store a reference to the previous structure for display purposes
    new_structure.previous_structure = previous_structure
    
    return differences

def _calculate_basic_differences(self, new_structure, previous_structure):
    """Fallback method to calculate basic differences when theory-specific detection is not available.
    
    This provides a minimal difference detection focused on sentence letters and Z3 functions,
    without any theory-specific semantic interpretation.
    
    Args:
        new_structure: The new model structure
        previous_structure: The previous model structure to compare against
        
    Returns:
        dict: Basic differences between the models
    """
    # Get Z3 models
    new_model = new_structure.z3_model
    previous_model = previous_structure.z3_model
    
    # Initialize basic differences structure
    differences = {
        "sentence_letters": {},
        "semantic_functions": {}
    }
    
    # Compare sentence letter valuations (common to all theories)
    for letter in self.build_example.model_constraints.sentence_letters:
        try:
            prev_value = previous_model.eval(letter, model_completion=True)
            new_value = new_model.eval(letter, model_completion=True)
            
            if str(prev_value) != str(new_value):
                differences["sentence_letters"][str(letter)] = {
                    "old": prev_value,
                    "new": new_value
                }
        except z3.Z3Exception:
            pass
    
    # Compare semantic function interpretations (common to all theories)
    semantics = new_structure.semantics
    for attr_name in dir(semantics):
        if attr_name.startswith('_'):
            continue
            
        attr = getattr(semantics, attr_name)
        if not isinstance(attr, z3.FuncDeclRef):
            continue
            
        arity = attr.arity()
        if arity == 0:
            continue
        
        # For unary and binary functions, check specific values
        if arity <= 2:
            n_worlds = getattr(new_structure, 'num_worlds', 5)  # Default to 5 if not available
            
            func_diffs = {}
            for inputs in self._generate_input_combinations(arity, n_worlds):
                try:
                    args = [z3.IntVal(i) for i in inputs]
                    prev_value = previous_model.eval(attr(*args), model_completion=True)
                    new_value = new_model.eval(attr(*args), model_completion=True)
                    
                    if str(prev_value) != str(new_value):
                        func_diffs[str(inputs)] = {
                            "old": prev_value,
                            "new": new_value
                        }
                except z3.Z3Exception:
                    pass
            
            if func_diffs:
                differences["semantic_functions"][attr_name] = func_diffs
    
    return differences
```

### 2. Theory-Specific Difference Methods in ModelStructure

Add a method to `ModelDefaults` in `model.py` that all theories can override:

```python
def calculate_model_differences(self, previous_structure):
    """Calculate theory-specific differences between this model and a previous one.
    
    This method identifies semantic differences that are meaningful in this theory's
    context. The default implementation returns None, indicating that the basic
    difference calculation should be used instead.
    
    Each theory should override this method to detect differences in its specific
    semantic primitives, such as worlds, times, accessibility relations, etc.
    
    Args:
        previous_structure: The previous model structure to compare against
        
    Returns:
        dict: Theory-specific differences between the models, or None to use basic detection
    """
    # Default implementation returns None, meaning use basic difference detection
    return None
```

### 3. Default Theory Implementation

Implement theory-specific difference detection for the default theory in `default/semantic.py`:

```python
def calculate_model_differences(self, previous_structure):
    """Calculate theory-specific differences between this model and a previous one.
    
    For the default theory, this detects differences in:
    - Possible states
    - World states
    - Part-whole relationships
    - Compatibility relations
    - Verification and falsification of atomic propositions
    
    Args:
        previous_structure: The previous model structure to compare against
        
    Returns:
        dict: Default theory-specific differences
    """
    if not hasattr(previous_structure, 'z3_model') or previous_structure.z3_model is None:
        return None
        
    # Initialize differences structure with default theory's specific categories
    differences = {
        "sentence_letters": {},  # Changed propositions
        "worlds": {             # Changes in world states
            "added": [],
            "removed": []
        },
        "possible_states": {    # Changes in possible states
            "added": [],
            "removed": []
        },
        "parthood": {},         # Changes in part-whole relationships
        "compatibility": {}     # Changes in state compatibility
    }
    
    # Get Z3 models
    new_model = self.z3_model
    prev_model = previous_structure.z3_model
    
    # Compare possible states
    try:
        prev_possible = set(getattr(previous_structure, 'z3_possible_states', []))
        new_possible = set(getattr(self, 'z3_possible_states', []))
        
        added_possible = new_possible - prev_possible
        removed_possible = prev_possible - new_possible
        
        if added_possible:
            differences["possible_states"]["added"] = list(added_possible)
        if removed_possible:
            differences["possible_states"]["removed"] = list(removed_possible)
        
        # Compare world states
        prev_worlds = set(getattr(previous_structure, 'z3_world_states', []))
        new_worlds = set(getattr(self, 'z3_world_states', []))
        
        added_worlds = new_worlds - prev_worlds
        removed_worlds = prev_worlds - new_worlds
        
        if added_worlds:
            differences["worlds"]["added"] = list(added_worlds)
        if removed_worlds:
            differences["worlds"]["removed"] = list(removed_worlds)
            
        # Check for part-whole relationship changes (specific to default theory)
        if hasattr(self.semantics, 'is_part_of'):
            parthood_changes = {}
            # Sample a subset of state pairs to check for parthood changes
            for x in self.z3_possible_states[:10]:  # Limit to avoid too much computation
                for y in self.z3_possible_states[:10]:
                    if x == y:
                        continue
                    try:
                        old_parthood = bool(prev_model.evaluate(self.semantics.is_part_of(x, y)))
                        new_parthood = bool(new_model.evaluate(self.semantics.is_part_of(x, y)))
                        
                        if old_parthood != new_parthood:
                            key = f"{bitvec_to_substates(x, self.semantics.N)}, {bitvec_to_substates(y, self.semantics.N)}"
                            parthood_changes[key] = {
                                "old": old_parthood,
                                "new": new_parthood
                            }
                    except Exception:
                        pass
            
            if parthood_changes:
                differences["parthood"] = parthood_changes
                
        # Check for compatibility changes (specific to default theory)
        if hasattr(self.semantics, 'compatible'):
            compatibility_changes = {}
            # Sample a subset of state pairs to check for compatibility changes
            for x in self.z3_possible_states[:10]:  # Limit to avoid too much computation
                for y in self.z3_possible_states[:10]:
                    if x == y:
                        continue
                    try:
                        old_compatible = bool(prev_model.evaluate(self.semantics.compatible(x, y)))
                        new_compatible = bool(new_model.evaluate(self.semantics.compatible(x, y)))
                        
                        if old_compatible != new_compatible:
                            key = f"{bitvec_to_substates(x, self.semantics.N)}, {bitvec_to_substates(y, self.semantics.N)}"
                            compatibility_changes[key] = {
                                "old": old_compatible,
                                "new": new_compatible
                            }
                    except Exception:
                        pass
            
            if compatibility_changes:
                differences["compatibility"] = compatibility_changes
    except Exception as e:
        # Log but continue with other difference detection
        print(f"Error comparing state differences: {e}")
    
    # Compare sentence letter valuations with default theory's semantics
    letter_differences = self._calculate_proposition_differences(previous_structure)
    if letter_differences:
        differences["sentence_letters"] = letter_differences
    
    # If no meaningful differences found, return None to signal fallback to basic detection
    if (not differences["sentence_letters"] and
        not differences["worlds"]["added"] and not differences["worlds"]["removed"] and
        not differences["possible_states"]["added"] and not differences["possible_states"]["removed"] and
        not differences.get("parthood") and not differences.get("compatibility")):
        return None
        
    return differences

def _calculate_proposition_differences(self, previous_structure):
    """Calculate differences in proposition valuations between models.
    
    This is a helper method for calculate_model_differences that specifically
    focuses on changes in how atomic propositions are verified and falsified.
    
    Args:
        previous_structure: The previous model structure
        
    Returns:
        dict: Mapping from proposition names to differences in verifiers/falsifiers
    """
    letter_diffs = {}
    
    for letter in self.model_constraints.sentence_letters:
        # Get current verifiers and falsifiers
        current_verifiers, current_falsifiers = self._get_verifier_falsifier_states(letter)
        
        # Get previous verifiers and falsifiers
        prev_verifiers, prev_falsifiers = previous_structure._get_verifier_falsifier_states(letter)
        
        # Check if there are differences
        if current_verifiers != prev_verifiers or current_falsifiers != prev_falsifiers:
            letter_diffs[str(letter)] = {
                "verifiers": {
                    "old": prev_verifiers,
                    "new": current_verifiers,
                    "added": current_verifiers - prev_verifiers,
                    "removed": prev_verifiers - current_verifiers
                },
                "falsifiers": {
                    "old": prev_falsifiers,
                    "new": current_falsifiers,
                    "added": current_falsifiers - prev_falsifiers,
                    "removed": prev_falsifiers - current_falsifiers
                }
            }
    
    return letter_diffs
```

### 4. Theory-Specific Difference Display

Implement theory-specific display for the default theory in `default/semantic.py`:

```python
def print_model_differences(self, output=sys.stdout):
    """Print the differences between this model and the previous one using default theory's semantics.
    
    This method displays the specific changes between models using the default theory's
    concepts of states, worlds, part-whole relationships, and verifier/falsifier sets.
    
    Args:
        output (file, optional): Output stream to write to. Defaults to sys.stdout.
    """
    from model_checker.utils import bitvec_to_substates, pretty_set_print
    
    if not hasattr(self, 'model_differences') or not self.model_differences:
        print("No previous model to compare with.", file=output)
        return
    
    # Print header
    print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)
    
    # Print world and state changes
    self._print_state_changes(output)
    
    # Print proposition changes 
    self._print_proposition_differences(output)
    
    # Print relation changes specific to default theory
    self._print_relation_differences(output)
    
    # Print structural metrics
    self._print_structural_metrics(output)

def _print_state_changes(self, output=sys.stdout):
    """Print changes to the state space using default theory's format and colors."""
    diffs = self.model_differences
    
    # Print world changes
    worlds = diffs.get("worlds", {})
    if worlds.get("added") or worlds.get("removed"):
        print("World Changes:", file=output)
        
        # Added worlds with world coloring
        for world in worlds.get("added", []):
            state_repr = bitvec_to_substates(world, self.semantics.N)
            print(f"  + {self.COLORS['world']}{state_repr} (world){self.RESET}", file=output)
            
        # Removed worlds with world coloring
        for world in worlds.get("removed", []):
            state_repr = bitvec_to_substates(world, self.semantics.N)
            print(f"  - {self.COLORS['world']}{state_repr} (world){self.RESET}", file=output)
    
    # Print possible state changes
    possible = diffs.get("possible_states", {})
    if possible.get("added") or possible.get("removed"):
        print("\nPossible State Changes:", file=output)
        
        # Added possible states with possible coloring
        for state in possible.get("added", []):
            state_repr = bitvec_to_substates(state, self.semantics.N)
            print(f"  + {self.COLORS['possible']}{state_repr}{self.RESET}", file=output)
            
        # Removed possible states
        for state in possible.get("removed", []):
            state_repr = bitvec_to_substates(state, self.semantics.N)
            print(f"  - {self.COLORS['possible']}{state_repr}{self.RESET}", file=output)

def _print_proposition_differences(self, output=sys.stdout):
    """Print changes to proposition valuations using default theory's format."""
    letters = self.model_differences.get("sentence_letters", {})
    if not letters:
        return
    
    print("\nProposition Changes:", file=output)
    for letter_str, changes in letters.items():
        # Get a user-friendly name for the letter
        friendly_name = self._get_friendly_letter_name(letter_str)
        print(f"  {friendly_name}:", file=output)
        
        # Print verifier changes
        if "verifiers" in changes:
            ver_changes = changes["verifiers"]
            print(f"    Verifiers: {pretty_set_print(ver_changes['new'])}", file=output)
            
            if ver_changes.get("added"):
                print(f"      + {self.COLORS['possible']}{pretty_set_print(ver_changes['added'])}{self.RESET}", file=output)
            if ver_changes.get("removed"):
                print(f"      - {self.COLORS['possible']}{pretty_set_print(ver_changes['removed'])}{self.RESET}", file=output)
        
        # Print falsifier changes
        if "falsifiers" in changes:
            fal_changes = changes["falsifiers"]
            print(f"    Falsifiers: {pretty_set_print(fal_changes['new'])}", file=output)
            
            if fal_changes.get("added"):
                print(f"      + {self.COLORS['possible']}{pretty_set_print(fal_changes['added'])}{self.RESET}", file=output)
            if fal_changes.get("removed"):
                print(f"      - {self.COLORS['possible']}{pretty_set_print(fal_changes['removed'])}{self.RESET}", file=output)

def _print_relation_differences(self, output=sys.stdout):
    """Print changes to relations specific to the default theory."""
    diffs = self.model_differences
    
    # Print part-whole relationship changes
    if diffs.get("parthood"):
        print("\nPart-Whole Relationship Changes:", file=output)
        for pair, change in diffs["parthood"].items():
            status = "now part of" if change["new"] else "no longer part of"
            print(f"  {pair}: {status}", file=output)
    
    # Print compatibility relationship changes
    if diffs.get("compatibility"):
        print("\nCompatibility Relationship Changes:", file=output)
        for pair, change in diffs["compatibility"].items():
            status = "now compatible" if change["new"] else "no longer compatible"
            print(f"  {pair}: {status}", file=output)

def _print_structural_metrics(self, output=sys.stdout):
    """Print structural metrics for the model."""
    print("\nStructural Properties:", file=output)
    print(f"  Worlds: {len(self.z3_world_states)}", file=output)
    
    # Add graph-theoretic properties if available
    if hasattr(self, 'model_graph'):
        try:
            graph = self.model_graph.graph
            
            # Degree distributions
            in_degrees = sorted(d for _, d in graph.in_degree())
            out_degrees = sorted(d for _, d in graph.out_degree())
            print(f"  In-degree distribution: {in_degrees}", file=output)
            print(f"  Out-degree distribution: {out_degrees}", file=output)
            
            # Connected components
            import networkx as nx
            components = nx.number_connected_components(graph.to_undirected())
            print(f"  connected_components: {components}", file=output)
        except Exception:
            pass
```

### 5. Bimodal Theory Example Implementation

As an example of how a different theory would implement this protocol, here's what the bimodal theory might do in `bimodal/semantic.py`:

```python
def calculate_model_differences(self, previous_structure):
    """Calculate theory-specific differences between this model and a previous one.
    
    For the bimodal theory, this detects differences in:
    - Times and worlds
    - Temporal accessibility
    - World accessibility
    - World-time pairs
    - Verification at specific world-time pairs
    
    Args:
        previous_structure: The previous model structure to compare against
        
    Returns:
        dict: Bimodal theory-specific differences
    """
    if not hasattr(previous_structure, 'z3_model') or previous_structure.z3_model is None:
        return None
        
    # Initialize differences structure with bimodal theory's specific categories
    differences = {
        "sentence_letters": {},  # Changed propositions
        "worlds": {             # Changes in worlds
            "added": [],
            "removed": []
        },
        "times": {              # Changes in times (bimodal-specific)
            "added": [],
            "removed": []
        },
        "world_time_pairs": {   # Changes in world-time pairs (bimodal-specific)
            "added": [],
            "removed": []
        },
        "world_accessibility": {},  # Changes in world accessibility (bimodal-specific)
        "time_accessibility": {}    # Changes in time accessibility (bimodal-specific)
    }
    
    # Get Z3 models
    new_model = self.z3_model
    prev_model = previous_structure.z3_model
    
    # Compare worlds (specific to bimodal)
    if hasattr(self, 'z3_worlds') and hasattr(previous_structure, 'z3_worlds'):
        new_worlds = set(self.z3_worlds)
        prev_worlds = set(previous_structure.z3_worlds)
        
        added_worlds = new_worlds - prev_worlds
        removed_worlds = prev_worlds - new_worlds
        
        if added_worlds:
            differences["worlds"]["added"] = list(added_worlds)
        if removed_worlds:
            differences["worlds"]["removed"] = list(removed_worlds)
    
    # Compare times (specific to bimodal)
    if hasattr(self, 'z3_times') and hasattr(previous_structure, 'z3_times'):
        new_times = set(self.z3_times)
        prev_times = set(previous_structure.z3_times)
        
        added_times = new_times - prev_times
        removed_times = prev_times - new_times
        
        if added_times:
            differences["times"]["added"] = list(added_times)
        if removed_times:
            differences["times"]["removed"] = list(removed_times)
    
    # Compare world-time pairs (specific to bimodal)
    if hasattr(self, 'main_world_time_pairs') and hasattr(previous_structure, 'main_world_time_pairs'):
        new_pairs = set(tuple(p) for p in self.main_world_time_pairs)
        prev_pairs = set(tuple(p) for p in previous_structure.main_world_time_pairs)
        
        added_pairs = new_pairs - prev_pairs
        removed_pairs = prev_pairs - new_pairs
        
        if added_pairs:
            differences["world_time_pairs"]["added"] = list(added_pairs)
        if removed_pairs:
            differences["world_time_pairs"]["removed"] = list(removed_pairs)
    
    # Check world accessibility changes (specific to bimodal)
    if hasattr(self.semantics, 'W_R'):
        w_access_changes = {}
        for w1 in self.z3_worlds[:5]:  # Limit to avoid excessive computation
            for w2 in self.z3_worlds[:5]:
                if w1 == w2:
                    continue
                try:
                    old_access = bool(prev_model.evaluate(self.semantics.W_R(w1, w2)))
                    new_access = bool(new_model.evaluate(self.semantics.W_R(w1, w2)))
                    
                    if old_access != new_access:
                        key = f"W{w1}, W{w2}"
                        w_access_changes[key] = {
                            "old": old_access,
                            "new": new_access
                        }
                except Exception:
                    pass
        
        if w_access_changes:
            differences["world_accessibility"] = w_access_changes
    
    # Check time accessibility changes (specific to bimodal)
    if hasattr(self.semantics, 'T_R'):
        t_access_changes = {}
        for t1 in self.z3_times[:5]:  # Limit to avoid excessive computation
            for t2 in self.z3_times[:5]:
                if t1 == t2:
                    continue
                try:
                    old_access = bool(prev_model.evaluate(self.semantics.T_R(t1, t2)))
                    new_access = bool(new_model.evaluate(self.semantics.T_R(t1, t2)))
                    
                    if old_access != new_access:
                        key = f"T{t1}, T{t2}"
                        t_access_changes[key] = {
                            "old": old_access,
                            "new": new_access
                        }
                except Exception:
                    pass
        
        if t_access_changes:
            differences["time_accessibility"] = t_access_changes
    
    # Check for proposition differences (using bimodal's semantics)
    letter_diffs = self._calculate_bimodal_proposition_differences(previous_structure)
    if letter_diffs:
        differences["sentence_letters"] = letter_diffs
    
    # If no meaningful differences found, return None to signal fallback to basic detection
    if all(not v or (isinstance(v, dict) and not any(v.values())) 
           for v in differences.values()):
        return None
    
    return differences

def print_model_differences(self, output=sys.stdout):
    """Print the differences between this model and the previous one using bimodal theory's semantics.
    
    This method displays the specific changes between models using the bimodal theory's
    concepts of times, worlds, world-time pairs, and accessibility relations.
    
    Args:
        output (file, optional): Output stream to write to. Defaults to sys.stdout.
    """
    if not hasattr(self, 'model_differences') or not self.model_differences:
        print("No previous model to compare with.", file=output)
        return
    
    print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)
    
    # Print bimodal-specific differences
    differences = self.model_differences
    
    # Print world changes
    if differences.get("worlds"):
        print("World Changes:", file=output)
        for world in differences["worlds"].get("added", []):
            print(f"  + Added world: W{world}", file=output)
        for world in differences["worlds"].get("removed", []):
            print(f"  - Removed world: W{world}", file=output)
    
    # Print time changes (bimodal-specific)
    if differences.get("times"):
        print("\nTime Changes:", file=output)
        for time in differences["times"].get("added", []):
            print(f"  + Added time: T{time}", file=output)
        for time in differences["times"].get("removed", []):
            print(f"  - Removed time: T{time}", file=output)
    
    # Print world-time pair changes (bimodal-specific)
    if differences.get("world_time_pairs"):
        print("\nWorld-Time Pair Changes:", file=output)
        for pair in differences["world_time_pairs"].get("added", []):
            print(f"  + Added pair: (W{pair[0]}, T{pair[1]})", file=output)
        for pair in differences["world_time_pairs"].get("removed", []):
            print(f"  - Removed pair: (W{pair[0]}, T{pair[1]})", file=output)
    
    # Print world accessibility changes (bimodal-specific)
    if differences.get("world_accessibility"):
        print("\nWorld Accessibility Changes:", file=output)
        for pair, change in differences["world_accessibility"].items():
            status = "now accessible" if change["new"] else "no longer accessible"
            print(f"  {pair}: {status}", file=output)
    
    # Print time accessibility changes (bimodal-specific)
    if differences.get("time_accessibility"):
        print("\nTime Accessibility Changes:", file=output)
        for pair, change in differences["time_accessibility"].items():
            status = "now accessible" if change["new"] else "no longer accessible"
            print(f"  {pair}: {status}", file=output)
    
    # Print proposition changes 
    if differences.get("sentence_letters"):
        self._print_bimodal_proposition_differences(differences["sentence_letters"], output)
    
    # Print structural metrics
    print("\nStructural Properties:", file=output)
    print(f"  Worlds: {len(getattr(self, 'z3_worlds', []))}", file=output)
    print(f"  Times: {len(getattr(self, 'z3_times', []))}", file=output)
    print(f"  World-Time Pairs: {len(getattr(self, 'main_world_time_pairs', []))}", file=output)
```

### 6. Integration with Iteration Flow

Update the `iterate` method in `ModelIterator` to pass previous model structure for difference calculation:

```python
# In ModelIterator.iterate:
# After finding a new distinct model:
differences = self._calculate_differences(new_structure, self.model_structures[-1])
new_structure.model_differences = differences

# Add the new model and structure to our results
self.found_models.append(new_model)
self.model_structures.append(new_structure)
self.current_iteration += 1
```

## Benefits of This Approach

1. **Theory-Driven**: Each theory defines what differences are meaningful in its semantic context
2. **Customizable Display**: Display formatting matches each theory's conventions
3. **Fallback Mechanism**: Basic difference detection works for theories that don't implement custom logic
4. **Easy Extension**: New theories only need to implement the protocol methods to participate
5. **Clear Separation**: Difference calculation is separate from display formatting

## Implementation Notes

1. **Theory-specific methods** should focus on their unique semantics:
   - Default theory: states, worlds, part-whole relations
   - Bimodal theory: times, worlds, temporal access
   - Exclusion theory: exclusion relations, exclusion sets
   - Imposition theory: imposition relations

2. **Difference calculation** should be:
   - Efficient (avoid checking every possible relation)
   - Robust (handle missing data gracefully)
   - Meaningful (focus on semantically significant changes)

3. **Display methods** should:
   - Use the theory's existing color scheme
   - Match the theory's existing state representation
   - Highlight the most important changes first

4. **Protocol methods** should have:
   - Clear documentation of expected behavior
   - Consistent signatures across theories
   - Graceful handling of errors