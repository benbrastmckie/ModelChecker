"""Bimodal theory specific model iteration implementation.

This module provides the BimodalModelIterator implementation which handles:
1. Detecting differences between models using bimodal theory semantics
2. Creating constraints to differentiate models with bimodal theory primitives
3. Checking model isomorphism for bimodal theory models
"""

import z3
import sys
import logging

from model_checker.iterate.core import BaseModelIterator
from model_checker.utils import bitvec_to_worldstate, pretty_set_print

# Configure logging
logger = logging.getLogger(__name__)
if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter('[BIMODAL-ITERATE] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.WARNING)


class BimodalModelIterator(BaseModelIterator):
    """Model iterator for the bimodal theory.
    
    This class extends CoreModelIterator with bimodal theory-specific
    implementations of the abstract methods required for model iteration.
    It provides specialized difference detection, constraint generation,
    and visualization for bimodal theory models.
    
    The bimodal theory uses:
    - World histories (arrays mapping time → world state)
    - World states represented as bit vectors
    - Truth conditions for atomic propositions
    - Task transitions between consecutive world states
    - Modal accessibility across different world histories
    """
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate differences between two bimodal theory model structures.
        
        For bimodal theory, this focuses on:
        - Changes in world histories (time-state mappings)
        - Changes in truth conditions for sentence letters
        - Changes in task transitions between world states
        - Changes in time intervals for worlds
        - Changes in time-shift relations between worlds
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Structured differences between the models
        """
        # Try to use the theory-specific detect_model_differences method on the structure
        if hasattr(new_structure, 'detect_model_differences'):
            try:
                differences = new_structure.detect_model_differences(previous_structure)
                if differences:
                    return differences
            except Exception as e:
                pass
        
        # Fall back to our own implementation
        differences = self._calculate_bimodal_differences(new_structure, previous_structure)
        
        return differences
    
    def _calculate_bimodal_differences(self, new_structure, previous_structure):
        """Bimodal theory specific implementation of difference detection.
        
        This is more sophisticated than the base _calculate_basic_differences method
        as it understands bimodal theory semantics like world histories, times,
        and task transitions.
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Dictionary of differences with bimodal theory semantics
        """
        # Get Z3 models
        new_model = new_structure.z3_model
        previous_model = previous_structure.z3_model
        
        # Initialize bimodal theory-specific differences structure
        differences = {
            "world_histories": {},
            "truth_conditions": {},
            "task_relations": {},
            "time_intervals": {},
            "time_shifts": {}
        }
        
        # 1. Compare world histories (time-state mappings)
        old_histories = getattr(previous_structure, "world_histories", {})
        new_histories = getattr(new_structure, "world_histories", {})
        
        all_world_ids = set(old_histories.keys()).union(set(new_histories.keys()))
        
        for world_id in all_world_ids:
            # If the world exists in both models
            if world_id in old_histories and world_id in new_histories:
                old_history = old_histories[world_id]
                new_history = new_histories[world_id]
                
                # Find added/removed/changed time points
                all_times = set(old_history.keys()).union(set(new_history.keys()))
                
                history_diffs = {}
                for time in all_times:
                    # If time exists in both
                    if time in old_history and time in new_history:
                        old_state = old_history[time]
                        new_state = new_history[time]
                        
                        # If state changed
                        if old_state != new_state:
                            history_diffs[time] = {
                                "old": old_state,
                                "new": new_state
                            }
                    # If time added
                    elif time in new_history:
                        history_diffs[time] = {
                            "old": None,
                            "new": new_history[time]
                        }
                    # If time removed
                    elif time in old_history:
                        history_diffs[time] = {
                            "old": old_history[time],
                            "new": None
                        }
                
                # Only add if there are differences
                if history_diffs:
                    differences["world_histories"][world_id] = history_diffs
            
            # If world added
            elif world_id in new_histories:
                differences["world_histories"][world_id] = {
                    "added": True,
                    "history": new_histories[world_id]
                }
            
            # If world removed
            elif world_id in old_histories:
                differences["world_histories"][world_id] = {
                    "removed": True,
                    "history": old_histories[world_id]
                }
        
        # 2. Compare truth conditions for sentence letters
        semantics = new_structure.semantics
        
        # Get all world states (unique across all world histories)
        all_states = set()
        for history in new_histories.values():
            all_states.update(set(history.values()))
        for history in old_histories.values():
            all_states.update(set(history.values()))
        
        # For each sentence letter and world state
        for letter in new_structure.sentence_letters:
            letter_diffs = {}
            
            for state in all_states:
                try:
                    # Try to convert state to BitVec if it's a string representation
                    state_bitvec = state
                    if isinstance(state, str) and not state.startswith("<"):
                        # Parse the state string representation to get a BitVec
                        # This assumes the state is in a bitvec format like "a,b,c"
                        if hasattr(semantics, 'state_str_to_bitvec'):
                            state_bitvec = semantics.state_str_to_bitvec(state)
                    
                    # Compare truth conditions
                    old_value = False
                    new_value = False
                    
                    try:
                        old_value = bool(previous_model.eval(
                            semantics.truth_condition(state_bitvec, letter), 
                            model_completion=True
                        ))
                    except:
                        pass
                    
                    try:
                        new_value = bool(new_model.eval(
                            semantics.truth_condition(state_bitvec, letter), 
                            model_completion=True
                        ))
                    except:
                        pass
                    
                    # If truth condition changed
                    if old_value != new_value:
                        letter_diffs[str(state)] = {
                            "old": old_value,
                            "new": new_value
                        }
                except Exception as e:
                    # Skip problematic states
                    pass
            
            # Only add if there are differences
            if letter_diffs:
                differences["truth_conditions"][str(letter)] = letter_diffs
        
        # 3. Compare task relations between world states
        if hasattr(semantics, 'task'):
            task_diffs = {}
            
            # For each pair of world states
            for state1 in all_states:
                for state2 in all_states:
                    try:
                        # Compare task relations
                        old_value = False
                        new_value = False
                        
                        try:
                            old_value = bool(previous_model.eval(
                                semantics.task(state1, state2), 
                                model_completion=True
                            ))
                        except:
                            pass
                        
                        try:
                            new_value = bool(new_model.eval(
                                semantics.task(state1, state2), 
                                model_completion=True
                            ))
                        except:
                            pass
                        
                        # If task relation changed
                        if old_value != new_value:
                            task_diffs[f"{state1}->{state2}"] = {
                                "old": old_value,
                                "new": new_value
                            }
                    except Exception as e:
                        # Skip problematic states
                        pass
            
            # Only add if there are differences
            if task_diffs:
                differences["task_relations"] = task_diffs
        
        # 4. Compare time intervals for worlds
        old_intervals = getattr(previous_structure.semantics, 'world_time_intervals', {})
        new_intervals = getattr(new_structure.semantics, 'world_time_intervals', {})
        
        interval_diffs = {}
        
        for world_id in all_world_ids:
            # If the world exists in both models
            if world_id in old_intervals and world_id in new_intervals:
                old_interval = old_intervals[world_id]
                new_interval = new_intervals[world_id]
                
                # If interval changed
                if old_interval != new_interval:
                    interval_diffs[world_id] = {
                        "old": old_interval,
                        "new": new_interval
                    }
            # If world added
            elif world_id in new_intervals:
                interval_diffs[world_id] = {
                    "old": None,
                    "new": new_intervals[world_id]
                }
            # If world removed
            elif world_id in old_intervals:
                interval_diffs[world_id] = {
                    "old": old_intervals[world_id],
                    "new": None
                }
        
        # Only add if there are differences
        if interval_diffs:
            differences["time_intervals"] = interval_diffs
        
        # 5. Compare time-shift relations between worlds
        old_shifts = getattr(previous_structure, 'time_shift_relations', {})
        new_shifts = getattr(new_structure, 'time_shift_relations', {})
        
        shift_diffs = {}
        
        for world_id in all_world_ids:
            # If the world exists in both models
            if world_id in old_shifts and world_id in new_shifts:
                old_shifts_for_world = old_shifts[world_id]
                new_shifts_for_world = new_shifts[world_id]
                
                # Find all shifts used by either model
                all_shifts = set(old_shifts_for_world.keys()).union(set(new_shifts_for_world.keys()))
                
                world_shift_diffs = {}
                for shift in all_shifts:
                    # If shift exists in both
                    if shift in old_shifts_for_world and shift in new_shifts_for_world:
                        old_target = old_shifts_for_world[shift]
                        new_target = new_shifts_for_world[shift]
                        
                        # If target changed
                        if old_target != new_target:
                            world_shift_diffs[shift] = {
                                "old": old_target,
                                "new": new_target
                            }
                    # If shift added
                    elif shift in new_shifts_for_world:
                        world_shift_diffs[shift] = {
                            "old": None,
                            "new": new_shifts_for_world[shift]
                        }
                    # If shift removed
                    elif shift in old_shifts_for_world:
                        world_shift_diffs[shift] = {
                            "old": old_shifts_for_world[shift],
                            "new": None
                        }
                
                # Only add if there are differences
                if world_shift_diffs:
                    shift_diffs[world_id] = world_shift_diffs
            
            # If world added
            elif world_id in new_shifts:
                shift_diffs[world_id] = {
                    "added": True,
                    "shifts": new_shifts[world_id]
                }
            
            # If world removed
            elif world_id in old_shifts:
                shift_diffs[world_id] = {
                    "removed": True,
                    "shifts": old_shifts[world_id]
                }
        
        # Only add if there are differences
        if shift_diffs:
            differences["time_shifts"] = shift_diffs
        
        return differences
    
    def display_model_differences(self, model_structure, output=sys.stdout):
        """Format differences for display using bimodal theory semantics.
        
        Args:
            model_structure: The model structure with differences
            output: Output stream for writing output
        """
        if not hasattr(model_structure, 'model_differences') or not model_structure.model_differences:
            return
            
        differences = model_structure.model_differences
        
        print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)
        
        # 1. Print world history changes
        if 'world_histories' in differences and differences['world_histories']:
            print("World History Changes:", file=output)
            
            for world_id, changes in differences['world_histories'].items():
                if isinstance(changes, dict) and changes.get('added', False):
                    # New world added
                    print(f"  + World W_{world_id} added", file=output)
                    history = changes.get('history', {})
                    
                    time_states = []
                    for time, state in sorted(history.items()):
                        time_states.append(f"({time}:{state})")
                    
                    if time_states:
                        print(f"    History: {' -> '.join(time_states)}", file=output)
                
                elif isinstance(changes, dict) and changes.get('removed', False):
                    # World removed
                    print(f"  - World W_{world_id} removed", file=output)
                
                else:
                    # World changed
                    print(f"  World W_{world_id} changed:", file=output)
                    
                    for time, change in sorted(changes.items()):
                        old_state = change.get('old')
                        new_state = change.get('new')
                        
                        if old_state is None:
                            # Time point added
                            print(f"    + Time {time}: {new_state}", file=output)
                        elif new_state is None:
                            # Time point removed
                            print(f"    - Time {time}: {old_state}", file=output)
                        else:
                            # State changed at this time
                            print(f"    Time {time}: {old_state} -> {new_state}", file=output)
        
        # 2. Print truth condition changes
        if 'truth_conditions' in differences and differences['truth_conditions']:
            print("\nTruth Condition Changes:", file=output)
            
            for letter, changes in differences['truth_conditions'].items():
                # Get the right letter name
                letter_name = letter
                if hasattr(model_structure, '_get_friendly_letter_name'):
                    try:
                        letter_name = model_structure._get_friendly_letter_name(letter)
                    except:
                        pass
                
                print(f"  Letter {letter_name}:", file=output)
                
                for state, change in changes.items():
                    old_value = change.get('old', False)
                    new_value = change.get('new', False)
                    
                    print(f"    State {state}: {old_value} -> {new_value}", file=output)
        
        # 3. Print task relation changes
        if 'task_relations' in differences and differences['task_relations']:
            print("\nTask Relation Changes:", file=output)
            
            for transition, change in differences['task_relations'].items():
                old_value = change.get('old', False)
                new_value = change.get('new', False)
                
                status = "added" if new_value and not old_value else "removed" if old_value and not new_value else "changed"
                print(f"  Task {transition}: {status}", file=output)
        
        # 4. Print time interval changes
        if 'time_intervals' in differences and differences['time_intervals']:
            print("\nTime Interval Changes:", file=output)
            
            for world_id, change in differences['time_intervals'].items():
                old_interval = change.get('old')
                new_interval = change.get('new')
                
                if old_interval is None:
                    print(f"  + World W_{world_id} interval: {new_interval}", file=output)
                elif new_interval is None:
                    print(f"  - World W_{world_id} interval: {old_interval}", file=output)
                else:
                    print(f"  World W_{world_id} interval: {old_interval} -> {new_interval}", file=output)
        
        # 5. Print time shift relation changes
        if 'time_shifts' in differences and differences['time_shifts']:
            print("\nTime Shift Relation Changes:", file=output)
            
            for world_id, changes in differences['time_shifts'].items():
                if isinstance(changes, dict) and changes.get('added', False):
                    # New world added
                    print(f"  + Time shifts for World W_{world_id} added", file=output)
                    shifts = changes.get('shifts', {})
                    
                    for shift, target in sorted(shifts.items()):
                        print(f"    Shift {shift}: -> W_{target}", file=output)
                
                elif isinstance(changes, dict) and changes.get('removed', False):
                    # World removed
                    print(f"  - Time shifts for World W_{world_id} removed", file=output)
                
                else:
                    # Shifts changed
                    print(f"  Time shifts for World W_{world_id} changed:", file=output)
                    
                    for shift, change in sorted(changes.items()):
                        old_target = change.get('old')
                        new_target = change.get('new')
                        
                        if old_target is None:
                            # Shift added
                            print(f"    + Shift {shift}: -> W_{new_target}", file=output)
                        elif new_target is None:
                            # Shift removed
                            print(f"    - Shift {shift}: -> W_{old_target}", file=output)
                        else:
                            # Target changed
                            print(f"    Shift {shift}: W_{old_target} -> W_{new_target}", file=output)

    
    def _create_difference_constraint(self, previous_models):
        """Create constraints requiring difference from previous models.
        
        For bimodal theory, focuses on world histories and truth values.
        
        Args:
            previous_models: List of Z3 models found so far
            
        Returns:
            Z3 constraint requiring structural difference
        """
        constraints = []
        semantics = self.build_example.model_constraints.semantics
        
        for prev_model in previous_models:
            model_constraints = []
            
            # World history constraints - different time-world mappings
            for w in range(semantics.W):
                for t in range(semantics.T):
                    prev_world_at_t = prev_model.eval(
                        semantics.world_history[w][t],
                        model_completion=True
                    )
                    model_constraints.append(
                        semantics.world_history[w][t] != prev_world_at_t
                    )
            
            # Truth value constraints
            syntax = self.build_example.example_syntax
            if hasattr(syntax, 'sentence_letters'):
                for letter_obj in syntax.sentence_letters:
                    if hasattr(letter_obj, 'sentence_letter'):
                        atom = letter_obj.sentence_letter
                        
                        # Check truth at each world history
                        for w in range(semantics.W):
                            prev_truth = prev_model.eval(
                                semantics.truth_condition(w, atom),
                                model_completion=True
                            )
                            model_constraints.append(
                                semantics.truth_condition(w, atom) != prev_truth
                            )
            
            if model_constraints:
                constraints.append(z3.Or(*model_constraints[:20]))  # Limit constraints
        
        return z3.And(*constraints) if constraints else z3.BoolVal(True)
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Create constraint preventing isomorphic models."""
        # For now, simple implementation
        return z3.BoolVal(True)
        
    def _create_stronger_constraint(self, isomorphic_model):
        """Create constraint for finding stronger models."""
        # For now, simple implementation
        return z3.BoolVal(True)
    
    def iterate_generator(self):
        """Override to add theory-specific differences to bimodal theory models.
        
        This method extends the base iterator's generator to merge bimodal-specific
        differences (world histories, truth conditions, task relations, time intervals,
        time shifts) with the generic differences calculated by the base iterator.
        
        Yields:
            Model structures with both generic and theory-specific differences
        """
        for model in super().iterate_generator():
            # Calculate theory-specific differences if we have a previous model
            if len(self.model_structures) >= 2:
                theory_diffs = self._calculate_bimodal_differences(
                    model, self.model_structures[-2]
                )
                
                # Merge theory-specific differences with existing generic ones
                if hasattr(model, 'model_differences') and model.model_differences:
                    model.model_differences.update(theory_diffs)
                else:
                    model.model_differences = theory_diffs
            
            yield model


# Wrapper function for use in theory examples
def iterate_example(example, max_iterations=None):
    """Find multiple models for a bimodal theory example.
    
    This function creates a BimodalModelIterator for the given example
    and uses it to find up to max_iterations distinct models.
    
    Args:
        example: A BuildExample instance with a bimodal theory model
        max_iterations: Maximum number of models to find (optional)
        
    Returns:
        list: List of distinct model structures
    """
    # Create the iterator with the example
    iterator = BimodalModelIterator(example)
    
    # Set max iterations if provided
    if max_iterations is not None:
        iterator.max_iterations = max_iterations
    
    # Perform iteration
    return iterator.iterate()