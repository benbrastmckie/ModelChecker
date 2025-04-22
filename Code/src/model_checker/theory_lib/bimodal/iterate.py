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
    
    This class extends BaseModelIterator with bimodal theory-specific
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
    
    def _create_difference_constraint(self, previous_models):
        """Create bimodal theory-specific constraints to differentiate models.
        
        This focuses on the key relationships in bimodal theory:
        - Truth conditions for sentence letters
        - Task transitions between world states
        - World intervals and time points
        - World history states at specific times
        
        Args:
            previous_models: List of Z3 models to differ from
            
        Returns:
            z3.ExprRef: Z3 constraint requiring difference from previous models
        """
        pass
        
        # Get key structures from build_example
        model_structure = self.build_example.model_structure
        semantics = model_structure.semantics
        
        # For each previous model, create a constraint requiring at least one difference
        model_diff_constraints = []
        
        for prev_model in previous_models:
            # Focus on key bimodal functions
            diff_components = []
            
            # 1. Differences in truth conditions
            for letter in model_structure.sentence_letters:
                for i in range(2**semantics.N):
                    # Create a bitvector for each possible world state
                    state = z3.BitVecVal(i, semantics.N)
                    try:
                        prev_value = prev_model.eval(semantics.truth_condition(state, letter), model_completion=True)
                        diff_components.append(semantics.truth_condition(state, letter) != prev_value)
                    except Exception:
                        pass
            
            # 2. Differences in task transitions
            if hasattr(semantics, 'task'):
                for i in range(2**semantics.N):
                    for j in range(2**semantics.N):
                        state1 = z3.BitVecVal(i, semantics.N)
                        state2 = z3.BitVecVal(j, semantics.N)
                        try:
                            prev_value = prev_model.eval(semantics.task(state1, state2), model_completion=True)
                            diff_components.append(semantics.task(state1, state2) != prev_value)
                        except Exception:
                            pass
            
            # 3. Differences in world intervals
            if hasattr(semantics, 'world_interval_start') and hasattr(semantics, 'world_interval_end'):
                max_world_id = getattr(semantics, 'max_world_id', 10)  # Use a reasonable default if not defined
                for world_id in range(max_world_id):
                    try:
                        # Check if world exists in the previous model
                        if z3.is_true(prev_model.eval(semantics.is_world(world_id), model_completion=True)):
                            prev_start = prev_model.eval(semantics.world_interval_start(world_id), model_completion=True)
                            prev_end = prev_model.eval(semantics.world_interval_end(world_id), model_completion=True)
                            
                            # Force different interval
                            start_diff = semantics.world_interval_start(world_id) != prev_start
                            end_diff = semantics.world_interval_end(world_id) != prev_end
                            diff_components.append(z3.Or(start_diff, end_diff))
                    except Exception:
                        pass
            
            # 4. Differences in world function (world histories)
            if hasattr(semantics, 'world_function'):
                max_world_id = getattr(semantics, 'max_world_id', 10)
                M = semantics.M
                for world_id in range(max_world_id):
                    for time in range(-M + 1, M):
                        try:
                            # Check if world exists and time is within its interval in the previous model
                            if z3.is_true(prev_model.eval(semantics.is_world(world_id), model_completion=True)):
                                # Check if time is in the valid interval
                                time_in_interval = z3.And(
                                    time >= prev_model.eval(semantics.world_interval_start(world_id), model_completion=True),
                                    time <= prev_model.eval(semantics.world_interval_end(world_id), model_completion=True)
                                )
                                
                                if z3.is_true(prev_model.eval(time_in_interval, model_completion=True)):
                                    # Get previous state at this world and time
                                    prev_world_array = prev_model.eval(semantics.world_function(world_id), model_completion=True)
                                    prev_state = prev_model.eval(z3.Select(prev_world_array, time), model_completion=True)
                                    
                                    # Force different state
                                    curr_state = z3.Select(semantics.world_function(world_id), z3.IntVal(time))
                                    diff_components.append(curr_state != prev_state)
                        except Exception:
                            pass
            
            # The new model must be different in at least one way
            if diff_components:
                model_diff_constraints.append(z3.Or(diff_components))
        
        # The new model must be different from ALL previous models
        if model_diff_constraints:
            return z3.And(model_diff_constraints)
        else:
            raise RuntimeError("Could not create any difference constraints for bimodal theory")
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Create constraints that force structural differences for bimodal theory.
        
        For bimodal theory models, this focuses on:
        - Different patterns of world histories
        - Different numbers of worlds and time intervals
        - Different task relation patterns
        
        Args:
            z3_model: The Z3 model to differ from
        
        Returns:
            z3.ExprRef: Z3 constraint expression or None if creation fails
        """
        # Get model structure
        model_structure = self.build_example.model_structure
        semantics = model_structure.semantics
        
        # Create constraints to force structural differences
        constraints = []
        
        # 1. Try to force a different number of worlds
        try:
            # Count current worlds
            max_world_id = getattr(semantics, 'max_world_id', 10)
            current_worlds = 0
            
            for i in range(max_world_id):
                try:
                    if z3.is_true(z3_model.eval(semantics.is_world(i), model_completion=True)):
                        current_worlds += 1
                except:
                    pass
            
            # Force either more or fewer worlds if possible
            world_count = z3.Sum([z3.If(semantics.is_world(i), 1, 0) for i in range(max_world_id)])
            
            if current_worlds > 1:
                constraints.append(world_count < current_worlds)
            
            if current_worlds < max_world_id - 1:
                constraints.append(world_count > current_worlds)
                
        except Exception as e:
            pass
        
        # 2. Try to force different world intervals
        try:
            max_world_id = getattr(semantics, 'max_world_id', 10)
            M = semantics.M
            
            for world_id in range(max_world_id):
                try:
                    # Check if this world exists in the model
                    if z3.is_true(z3_model.eval(semantics.is_world(world_id), model_completion=True)):
                        # Get current interval
                        start_time = z3_model.eval(semantics.world_interval_start(world_id), model_completion=True).as_long()
                        end_time = z3_model.eval(semantics.world_interval_end(world_id), model_completion=True).as_long()
                        
                        # Force different start or end time
                        if start_time > -M + 1:
                            constraints.append(semantics.world_interval_start(world_id) < start_time)
                        
                        if start_time < 0:
                            constraints.append(semantics.world_interval_start(world_id) > start_time)
                            
                        if end_time < M - 1:
                            constraints.append(semantics.world_interval_end(world_id) > end_time)
                            
                        if end_time > 0:
                            constraints.append(semantics.world_interval_end(world_id) < end_time)
                except:
                    pass
        except Exception as e:
            logger.debug(f"Error creating interval constraint: {e}")
        
        # 3. Try to force different truth conditions for sentence letters
        try:
            # Get current truth condition pattern
            truth_count = 0
            states_to_check = min(8, 2**semantics.N)  # Limit number of states to check
            
            for letter in model_structure.sentence_letters:
                for i in range(states_to_check):
                    state = z3.BitVecVal(i, semantics.N)
                    try:
                        if z3.is_true(z3_model.eval(semantics.truth_condition(state, letter), model_completion=True)):
                            truth_count += 1
                    except:
                        pass
            
            # Force significantly different truth count
            total_tc_count = z3.Sum([
                z3.If(semantics.truth_condition(z3.BitVecVal(i, semantics.N), letter), 1, 0)
                for letter in model_structure.sentence_letters
                for i in range(states_to_check)
            ])
            
            if truth_count > states_to_check * len(model_structure.sentence_letters) // 2:
                # If many trues, force mostly false
                constraints.append(total_tc_count < truth_count // 2)
            else:
                # If few trues, force mostly true
                max_count = states_to_check * len(model_structure.sentence_letters)
                constraints.append(total_tc_count > max_count - truth_count // 2)
        except Exception as e:
            logger.debug(f"Error creating truth condition constraint: {e}")
        
        # 4. Try to force different task relations
        if hasattr(semantics, 'task'):
            try:
                # Count current task relations
                task_count = 0
                states_to_check = min(4, 2**semantics.N)  # Limit for performance
                
                for i in range(states_to_check):
                    for j in range(states_to_check):
                        state1 = z3.BitVecVal(i, semantics.N)
                        state2 = z3.BitVecVal(j, semantics.N)
                        try:
                            if z3.is_true(z3_model.eval(semantics.task(state1, state2), model_completion=True)):
                                task_count += 1
                        except:
                            pass
                
                # Force significantly different task count
                task_tc_count = z3.Sum([
                    z3.If(semantics.task(z3.BitVecVal(i, semantics.N), z3.BitVecVal(j, semantics.N)), 1, 0)
                    for i in range(states_to_check)
                    for j in range(states_to_check)
                ])
                
                max_task_count = states_to_check * states_to_check
                
                if task_count > max_task_count // 2:
                    # If many tasks, force few
                    constraints.append(task_tc_count < task_count // 2)
                else:
                    # If few tasks, force many
                    constraints.append(task_tc_count > max_task_count - task_count // 2)
            except Exception as e:
                logger.debug(f"Error creating task constraint: {e}")
        
        # Return the combined constraint if any constraints were created
        if constraints:
            return z3.Or(constraints)
        
        return None
    
    def _create_stronger_constraint(self, isomorphic_model):
        """Create stronger constraints to escape isomorphic models for bimodal theory.
        
        This creates more dramatic constraints when multiple consecutive
        isomorphic models have been found.
        
        Args:
            isomorphic_model: The Z3 model that was isomorphic
        
        Returns:
            z3.ExprRef: Stronger constraint or None if creation fails
        """
        # Get model structure and semantics
        model_structure = self.build_example.model_structure
        semantics = model_structure.semantics
        
        # The approach varies depending on the escape attempt
        escape_attempt = getattr(self, 'escape_attempts', 1)
        
        # Create constraints that force major structural changes
        constraints = []
        
        # 1. Force dramatically different number of worlds
        try:
            # Count current worlds
            max_world_id = getattr(semantics, 'max_world_id', 10)
            current_worlds = 0
            
            for i in range(max_world_id):
                try:
                    if z3.is_true(isomorphic_model.eval(semantics.is_world(i), model_completion=True)):
                        current_worlds += 1
                except:
                    pass
            
            # World count expression
            world_count = z3.Sum([z3.If(semantics.is_world(i), 1, 0) for i in range(max_world_id)])
            
            # Force minimal or maximal number of worlds
            if escape_attempt == 1:
                # First attempt: force significantly different world count
                if current_worlds > max_world_id // 2:
                    # If many worlds, force minimal (1-2 worlds)
                    constraints.append(world_count <= 2)
                else:
                    # If few worlds, force many (near max)
                    constraints.append(world_count >= max_world_id - 2)
            else:
                # Later attempts: extreme values
                constraints.append(world_count == 1)  # Minimal
                constraints.append(world_count == max_world_id)  # Maximal
                
                # Also try mirroring all intervals
                for world_id in range(max_world_id):
                    try:
                        # Check if this world exists in the model
                        if z3.is_true(isomorphic_model.eval(semantics.is_world(world_id), model_completion=True)):
                            # Get current interval
                            start_time = isomorphic_model.eval(semantics.world_interval_start(world_id), model_completion=True)
                            end_time = isomorphic_model.eval(semantics.world_interval_end(world_id), model_completion=True)
                            
                            # Force mirrored interval (negative becomes positive and vice versa)
                            mirror_constraint = z3.And(
                                semantics.world_interval_start(world_id) == -end_time,
                                semantics.world_interval_end(world_id) == -start_time
                            )
                            constraints.append(mirror_constraint)
                    except:
                        pass
        except Exception as e:
            logger.debug(f"Error creating world count constraint: {e}")
        
        # 2. Force completely different world intervals
        try:
            M = semantics.M
            max_world_id = getattr(semantics, 'max_world_id', 10)
            
            if escape_attempt == 1:
                # First attempt: shift all intervals
                shift_all_forward = []
                shift_all_backward = []
                
                for world_id in range(max_world_id):
                    try:
                        # Check if this world exists in the model
                        if z3.is_true(isomorphic_model.eval(semantics.is_world(world_id), model_completion=True)):
                            # Get current interval
                            start_time = isomorphic_model.eval(semantics.world_interval_start(world_id), model_completion=True)
                            end_time = isomorphic_model.eval(semantics.world_interval_end(world_id), model_completion=True)
                            
                            # Force shifted interval
                            if start_time.as_long() > -M + 2:  # Room to shift backward
                                shift_all_backward.append(
                                    z3.And(
                                        semantics.world_interval_start(world_id) == start_time - 1,
                                        semantics.world_interval_end(world_id) == end_time - 1
                                    )
                                )
                                
                            if end_time.as_long() < M - 2:  # Room to shift forward
                                shift_all_forward.append(
                                    z3.And(
                                        semantics.world_interval_start(world_id) == start_time + 1,
                                        semantics.world_interval_end(world_id) == end_time + 1
                                    )
                                )
                    except:
                        pass
                
                if shift_all_forward:
                    constraints.append(z3.And(shift_all_forward))
                    
                if shift_all_backward:
                    constraints.append(z3.And(shift_all_backward))
            else:
                # Later attempts: extreme intervals
                for world_id in range(max_world_id):
                    try:
                        # Force intervals at extremes of the time range
                        earliest_interval = z3.And(
                            semantics.world_interval_start(world_id) == z3.IntVal(-M + 1),
                            semantics.world_interval_end(world_id) == z3.IntVal(0)
                        )
                        latest_interval = z3.And(
                            semantics.world_interval_start(world_id) == z3.IntVal(0),
                            semantics.world_interval_end(world_id) == z3.IntVal(M - 1)
                        )
                        
                        constraints.append(earliest_interval)
                        constraints.append(latest_interval)
                    except:
                        pass
        except Exception as e:
            logger.debug(f"Error creating interval constraint: {e}")
        
        # 3. Force dramatically different truth conditions
        try:
            # Attempt to flip all truth conditions
            states_to_check = min(8, 2**semantics.N)  # Limit number of states to check
            
            flip_constraints = []
            for letter in model_structure.sentence_letters:
                letter_flip = []
                for i in range(states_to_check):
                    state = z3.BitVecVal(i, semantics.N)
                    try:
                        prev_value = isomorphic_model.eval(semantics.truth_condition(state, letter), model_completion=True)
                        letter_flip.append(semantics.truth_condition(state, letter) != prev_value)
                    except:
                        pass
                
                # Flip all or most truth values for this letter
                if letter_flip:
                    flip_constraints.append(z3.And(letter_flip))
            
            # Add constraints to flip truth conditions for either all letters or each letter individually
            if flip_constraints:
                if len(flip_constraints) > 1:
                    # Either flip all letters or flip each letter individually
                    constraints.append(z3.And(flip_constraints))  # Flip all
                    for flip in flip_constraints:
                        constraints.append(flip)  # Flip individual letters
                else:
                    constraints.append(flip_constraints[0])
        except Exception as e:
            logger.debug(f"Error creating truth condition constraint: {e}")
        
        # 4. Force dramatically different task relations
        if hasattr(semantics, 'task'):
            try:
                # Try to flip task relations
                states_to_check = min(4, 2**semantics.N)  # Limit for performance
                
                task_flips = []
                for i in range(states_to_check):
                    for j in range(states_to_check):
                        state1 = z3.BitVecVal(i, semantics.N)
                        state2 = z3.BitVecVal(j, semantics.N)
                        try:
                            prev_value = isomorphic_model.eval(semantics.task(state1, state2), model_completion=True)
                            task_flips.append(semantics.task(state1, state2) != prev_value)
                        except:
                            pass
                
                if task_flips:
                    constraints.append(z3.And(task_flips))
            except Exception as e:
                logger.debug(f"Error creating task constraint: {e}")
        
        # Return the combined constraint if any constraints were created
        if constraints:
            return z3.Or(constraints)
        
        return None
    
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