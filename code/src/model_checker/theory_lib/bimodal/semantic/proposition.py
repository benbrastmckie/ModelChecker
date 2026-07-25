"""Proposition implementation for the bimodal theory.

This module contains BimodalProposition, representing propositional content
(verifiers/falsifiers-free bilateral truth value) at world-time evaluation
points in the bimodal semantic framework.
"""

import time
from typing import cast

from model_checker import z3_shim as z3

from model_checker.solver import is_true
from model_checker.models.proposition import PropositionDefaults
from model_checker.utils import ForAll, Exists, bitvec_to_worldstate, pretty_set_print


class BimodalProposition(PropositionDefaults):
    """Defines the proposition assigned to the sentences of the language.
    
    This class represents propositions in bimodal logic, handling the evaluation
    of sentences at worlds and times, and computing their extensions across
    the entire model structure.
    
    Attributes:
        sentence: The sentence this proposition represents
        model_structure: The BimodalStructure containing worlds and times
        eval_world_id: The world_id to evaluate at
        eval_time: The time point to evaluate at
        extension: Dictionary mapping world_ids to (true_times, false_times) pairs
        truth_set: Set of world states where the proposition is true
        false_set: Set of world states where the proposition is false
    """

    def __init__(self, sentence, model_structure, eval_world='main', eval_time='now'):
        """Initialize a BimodalProposition with a sentence and model structure.
        
        Args:
            sentence (Sentence): The sentence this proposition represents
            model_structure (BimodalStructure): The model structure
            eval_world (str or int): The world ID to evaluate at; 
                                    'main' uses the main world ID (0),
                                    an int is treated as a world ID
            eval_time (str or int): The time to evaluate at; 
                                   'now' uses the current time
        """
        super().__init__(sentence, model_structure)

        self.z3_model = self.model_structure.z3_model
        self.M = self.model_structure.semantics.M
        
        # Set the evaluation world ID
        if eval_world == 'main':
            # Use the main world (0)
            self.eval_world = self.model_structure.main_world
        elif isinstance(eval_world, int):
            self.eval_world = eval_world
        else:
            # Handle legacy case where a world array might be passed
            # This should not happen with the new API, but just in case
            raise ValueError("eval_world must be 'main' or an integer world_id")
            
        # Set the evaluation time
        self.eval_time = self.model_structure.main_time if eval_time == 'now' else eval_time
        
        # Calculate the extension (truth/falsity at each world and time)
        self.extension = self.find_extension()
        
        # TODO: adapt find_truth_condition in operators.py to use eval_point
        # Extract world states sets for use in representation
        self.truth_set, self.false_set = self._find_proposition_at(self.eval_time)

    def __eq__(self, other):
        return (
            self.extension == other.extension
            and self.name == other.name
        )

    def __repr__(self):
        return f"< {pretty_set_print(self.truth_set)}, {pretty_set_print(self.false_set)} >"

    def proposition_constraints(self, sentence_letter):
        """Returns Z3 constraints for a sentence letter based on user settings.
        
        Generates classical constraints and optional constraints (non-null, contingent, 
        and disjoint) depending on the user settings.
        
        Args:
            sentence_letter: The sentence letter to generate constraints for
        
        Returns:
            list: Z3 constraints for the sentence letter
        """
        semantics = self.semantics

        def get_contingent_constraints():
            """The contingent constraints require that a sentence letter is true
            at some world state and false at some world state."""
            true_contingent_state = z3.BitVec("true_contingent_state", semantics.N)
            false_contingent_state = z3.BitVec("false_contingent_state", semantics.N)
            possibly_true = Exists(
                [true_contingent_state],
                semantics.truth_condition(true_contingent_state, sentence_letter)
            )
            possibly_false = Exists(
                [false_contingent_state],
                cast(z3.BoolRef, z3.Not(semantics.truth_condition(false_contingent_state, sentence_letter)))
            )
            return [possibly_true, possibly_false]

        def get_disjoint_constraints():
            """The disjoint_constraints ensure that no two sentence letters can
            be true at the same world state."""
            disjoint_state = z3.BitVec("disjoint_state", semantics.N)
            disjoint_constraints = []
            for other_letter in self.sentence_letters:
                if other_letter is not sentence_letter:
                    other_is_disjoint = ForAll(
                        disjoint_state,
                        cast(z3.BoolRef, z3.Or(
                            z3.Not(semantics.truth_condition(disjoint_state, sentence_letter)),
                            z3.Not(semantics.truth_condition(disjoint_state, other_letter))
                        ))
                    )
                    disjoint_constraints.append(other_is_disjoint)
            return disjoint_constraints

        # Collect constraints
        constraints = []
        if self.settings['contingent']:
            constraints.extend(get_contingent_constraints())
        if self.settings['disjoint']:
            constraints.extend(get_disjoint_constraints())
        return constraints

    def find_extension(self):
        """Computes the truth/falsity extension of this proposition across worlds and times.
        
        For atomic sentences, this method evaluates truth values at all time points in each
        world to build the extension dictionary. For complex sentences, it delegates to the
        appropriate operator's find_truth_condition method.
        
        Returns:
            dict: A dictionary mapping world_ids to pairs of (true_times, false_times) lists
        """
        arguments = self.arguments or ()
        
        if self.sentence_letter is not None:
            extension = {}
            
            # Iterate through all world_ids in the model structure
            for world_id in self.model_structure.world_arrays.keys():
                # Collect truth and falsity times
                true_times = []
                false_times = []
                
                # Use the world time intervals from the semantics
                if world_id in self.model_structure.semantics.world_time_intervals:
                    start_time, end_time = self.model_structure.semantics.world_time_intervals[world_id]
                    times_to_check = range(start_time, end_time + 1)
                else:
                    # If no interval information is available, let error propagate
                    times_to_check = self.model_structure.all_times
                
                for time in times_to_check:
                    # Pass the world_id directly to the true_at method
                    # Allow Z3 exceptions to propagate naturally - fail fast
                    truth_expr = self.model_structure.semantics.true_at(
                        self.sentence, {"world" : world_id, "time" : time}
                    )
                    evaluated_expr = self.z3_model.evaluate(truth_expr)
                    if is_true(evaluated_expr):
                        true_times.append(time)
                    else:
                        false_times.append(time)
                
                # Store the extension for this world_id
                extension[world_id] = (true_times, false_times)
                
            return extension
            
        elif self.operator is not None:
            # For complex sentences, delegate to the operator's find_truth_condition method
            # Create an eval_point dictionary to pass world and time consistently
            eval_point = {"world": self.eval_world, "time": self.eval_time}
            return self.operator.find_truth_condition(*arguments, eval_point)
            
        raise ValueError(f"There is no proposition for {self}.")

    def truth_value_at(self, eval_world, eval_time):
        """Checks if the proposition is true at the given world and time.
        
        Args:
            eval_world (int): The world ID to evaluate at
            eval_time (int): The time point to evaluate at
            
        Returns:
            bool: True if the proposition is true at the specified world and time
            
        Raises:
            KeyError: If eval_world is not a valid world ID in the extension
        """
        # Check if we have a valid extension
        if not hasattr(self, 'extension') or not self.extension:
            # If there's no extension, we can't evaluate truth
            pass
            return False
            
        # Check if the requested world_id exists in the extension
        if eval_world not in self.extension:
            pass
            # Return a default value when the world doesn't exist in the extension
            return False
            
        # Get the truth/falsity data for this world_id
        true_times, false_times = self.extension[eval_world]
        
        true_in_eval_world = eval_time in true_times
        false_in_eval_world = eval_time in false_times
        
        if true_in_eval_world and false_in_eval_world:
            # Both true and false (shouldn't happen in a well-formed model)
            # TODO: make print world_history instead
            try:
                world_array = self.model_structure.get_world_array(eval_world)
                eval_state = self.z3_model.evaluate(world_array[eval_time])
                pass
            except Exception as e:
                pass
                
        return true_in_eval_world

    def _find_proposition_at(self, eval_time):
        """Find the proposition's extension at a specific evaluation point.
        
        This method determines which world states make the proposition true and false
        at the specified evaluation time by examining the proposition's extension
        across all worlds.
        
        Args:
            eval_point (dict): Dictionary containing evaluation information with keys:
                - time (int): The time point at which to evaluate
                - world (int): The world ID (not used in this method since we collect
                             states from all worlds at the given time)
                
        Returns:
            str: A string representation of the proposition's extension at the evaluation
                 point in the format "< truth_states, false_states >" where:
                 - truth_states: Set of world states where proposition is true at eval_time
                 - false_states: Set of world states where proposition is false at eval_time
        """
        # Initialize sets to collect world states where proposition is true/false
        truth_states = set()
        false_states = set()

        # Examine each world's extension at the evaluation time
        for world_id, (true_times, false_times) in self.extension.items():
            # Get the world history containing time->state mappings
            world_history = self.model_structure.world_histories[world_id]

            # If eval_time is in true_times, add the corresponding state to truth_states
            if eval_time in true_times:
                state = world_history[eval_time]
                truth_states.add(state)
                
            # If eval_time is in false_times, add the corresponding state to false_states
            if eval_time in false_times:
                state = world_history[eval_time]
                false_states.add(state)
                
        # Return proposition's extension at eval_time
        return truth_states, false_states

    # TODO: make print from operator truth_condition
    def print_proposition(self, eval_point, indent_num, use_colors):
        """Print the proposition and it's truth value at the evaluation point.
        
        Requires eval_point to contain:
        - world: Integer ID of the world to evaluate at
        - time: Time point to evaluate at
        """
        # Extract evaluation point info
        world_id = eval_point["world"]  # Expected to be an integer
        eval_time = eval_point["time"]
        
        # Get truth value
        truth_value = self.truth_value_at(world_id, eval_time)
        
        # Get world state representation
        world_state_repr = "∅"  # Default placeholder
        
        # Try to get from world histories first (preferred path)
        if world_id in self.model_structure.world_histories:
            world_history = self.model_structure.world_histories[world_id]
            if eval_time in world_history:
                world_state_repr = world_history[eval_time]
        
        # If not in histories, try from arrays using safe_select
        elif world_id in self.model_structure.world_arrays:
            world_array = self.model_structure.world_arrays[world_id]
            
            try:
                # Use safe_select to handle both ArrayRef and QuantifierRef
                world_state = self.model_structure.semantics.safe_select(
                    self.z3_model, world_array, eval_time)
                world_state_repr = bitvec_to_worldstate(world_state)
            except (TypeError, z3.Z3Exception) as e:
                # Set a clear error representation
                world_state_repr = f"<error:{str(e)}>"
            
        # Set colors
        RESET, FULL, PART = self.set_colors(
            self.name,
            indent_num,
            truth_value,
            world_state_repr,
            use_colors
        )

        # Print the proposition
        print(
            f"{'  ' * indent_num}{FULL}|{self.name}| = {self}{RESET}"
            f"  {PART}({truth_value} in W_{world_id} at time {eval_time}){RESET}"
        )

