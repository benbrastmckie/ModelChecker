import sys
import time
import z3

# Try installed package imports first
try:
    from model_checker.model import (
        SemanticDefaults,
        PropositionDefaults,
        ModelDefaults,
    )
    from model_checker.utils import (
        ForAll,
        Exists,
        bitvec_to_substates,
        int_to_binary,
        pretty_set_print,
    )
    from model_checker import syntactic
except ImportError:
    # Fall back to local imports for development
    from src.model_checker.model import (
        SemanticDefaults,
        PropositionDefaults,
        ModelDefaults,
    )
    from src.model_checker.utils import (
        ForAll,
        Exists,
        bitvec_to_substates,
        int_to_binary,
        pretty_set_print,
    )
    from src.model_checker import syntactic



##############################################################################
######################### SEMANTICS AND PROPOSITIONS #########################
##############################################################################

class BimodalSemantics(SemanticDefaults):
    """Defines the semantic model for bimodal logic, including primitive relations,
    frame constraints for task transitions between world states, and evaluation
    of truth conditions."""

    DEFAULT_EXAMPLE_SETTINGS = {
        # Number of world_states
        'N': 3,
        # Whether sentence_letters are assigned to contingent propositions
        'contingent': False,
        # Whether sentence_letters are assigned to distinct world_states
        'disjoint': False,
        # Maximum time Z3 is permitted to look for a model
        'max_time': 1,
        # Whether a model is expected or not (used for unit testing)
        'expectation': True,
    }

    def __init__(self, settings):

        # Initialize the superclass to set defaults
        super().__init__(settings)

        # Initialize always true/false worlds, updated in the model_structure
        self.all_true = {}
        self.all_false = {}

        # Initialize sorts, primitives, and frame_constraints
        self.define_sorts()
        self.define_primitives()
        self.frame_constraints = self.build_frame_constraints()
        self.define_invalidity()

    def define_sorts(self):
        """Define the Z3 sorts used in the bimodal logic model.

        Create three sorts:
        - WorldStateSort: BitVecSort for representing world states as bitvectors
        - TimeSort: IntSort for representing time points
        - WorldIdSort: IntSort for mapping world IDs to world arrays
        """
        self.WorldStateSort = z3.BitVecSort(self.N)
        self.TimeSort = z3.IntSort()
        self.WorldIdSort = z3.IntSort()


    def define_primitives(self):
        """Define the Z3 primitive functions and relations used in the bimodal logic model.
        
        This method initializes:
        - task: A binary relation between world states representing task transitions
        - world_function: A mapping from world IDs to world arrays (time -> world state)
        - truth_condition: A function assigning truth values to atomic propositions at world states
        - main_world: The primary world array used for evaluation (world_function applied to ID 0)
        - main_time: The time point at which sentences are evaluated
        - main_point: Dictionary containing the main world and time for evaluation
        """
        self.task = z3.Function(
            "Task",
            self.WorldStateSort,
            self.WorldStateSort,
            z3.BoolSort()
        )

        self.world_function = z3.Function(
            'world_function', 
            self.WorldIdSort,  # Input: world ID 
            z3.ArraySort(self.TimeSort, self.WorldStateSort)  # Output: world_array
        )

        self.truth_condition = z3.Function(
            "truth_condition",
            self.WorldStateSort,
            syntactic.AtomSort,
            z3.BoolSort()
        )

        self.main_world = 0  # Main world ID is 0

        self.main_time = z3.Int('main_time')

        self.main_point = {
            "world": self.main_world,  # Store world ID, not array
            "time": self.main_time,
        }

    def build_frame_constraints(self):
        """Build the frame constraints for the bimodal logic model.

        This method constructs the fundamental constraints that define the behavior of the model:
        1. Time constraints - Ensures main_time is within valid range
        2. Truth value constraints - Each atomic sentence must have a definite truth value at each world state
        3. Lawful transitions - World function must respect task relation between consecutive states
        4. Task restriction - Task relation only holds between consecutive states in some world line
        5. Reachability - Every world state must be reachable through world_function

        Returns:
            list: A list of Z3 constraints that define the frame conditions for the model
        """
        time_constraints = self.time_exists(self.main_time)

        world_state = z3.BitVec('world_state', self.N)
        atom = z3.Const('atom_interpretation', syntactic.AtomSort)
        definite_truth = z3.ForAll(
            [world_state, atom],
            z3.Or(
                self.truth_condition(world_state, atom),
                z3.Not(self.truth_condition(world_state, atom))
            )
        )

        lawful_world_id = z3.Int('lawful_world_id')
        lawful_time = z3.Int('lawful_time')
        lawful = z3.ForAll(
            [lawful_world_id, lawful_time],
            z3.Implies(
                z3.And(
                    self.world_exists(lawful_world_id, lawful_time),
                    self.time_exists(lawful_time, -1),
                ),
                self.task(
                    z3.Select(self.world_function(lawful_world_id), lawful_time),
                    z3.Select(self.world_function(lawful_world_id), lawful_time + 1)
                )
            )
        )
        
        some_state = z3.BitVec('task_restrict_some_state', self.N)
        next_state = z3.BitVec('task_restrict_next_state', self.N)
        task_world_id = z3.Int('task_world_id')
        task_time = z3.Int('task_time')
        task_restriction = z3.ForAll(
            [some_state, next_state],
            z3.Implies(
                self.task(some_state, next_state),
                z3.Exists(
                    [task_world_id, task_time],
                    z3.And(
                        self.world_exists(task_world_id, task_time),
                        self.time_exists(task_time, -1),
                        some_state == z3.Select(self.world_function(task_world_id), task_time),
                        next_state == z3.Select(self.world_function(task_world_id), task_time + 1)
                    )
                )
            )
        )

        reachable_world_id = z3.Int('reachable_world_id')
        reachable_time = z3.Int('reachable_time')
        reachable_state = z3.BitVec('reachable_state', self.N)
        reachable = z3.ForAll(
            [reachable_state],
            z3.Exists(
                [reachable_world_id, reachable_time],
                z3.And(
                    self.world_exists(reachable_world_id, reachable_time),
                    self.time_exists(reachable_time),
                    z3.Select(self.world_function(reachable_world_id), reachable_time) == reachable_state
                )
            )
        )

        return [
            time_constraints,
            definite_truth,
            lawful,
            task_restriction,
            reachable,
        ]

    def define_invalidity(self):
        """Define the behavior for premises and conclusions in invalidity checks.

        This method sets up two lambda functions that specify how premises and conclusions 
        should be evaluated when checking for invalidity:

        - premise_behavior: Evaluates whether a premise is true at the main world and time
        - conclusion_behavior: Evaluates whether a conclusion is false at the main world and time

        These behaviors are used to find counterexamples that demonstrate invalidity of arguments
        by showing a case where all premises are true but the conclusion is false.
        """
        self.premise_behavior = lambda premise: self.true_at(premise, self.main_world, self.main_time)
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_world, self.main_time)

        ### SCRAP ###

        # world_id_constraint,
        # world_id_range,
        # abundant_worlds,
        # two_worlds_exist,

        # Store valid world-arrays after model is found
        # self.valid_world_arrays = []

        # # Calculate number of possible functions from times [0,M) to world states
        # # For each time point, we have 2^N possible world states
        # # Total number of possible functions = (2^N)^M where M is the interval length
        # max_world_id = z3.IntVal(pow(2 ** self.N, self.M))
        # # Add constraint to restrict world IDs to valid range
        # world_id = z3.Int('world_id_constraint')
        # world_id_range = z3.ForAll(
        #     world_id,
        #     z3.Implies(
        #         # If world_id is used in world_function
        #         z3.Select(self.world_function(world_id), 0) == z3.Select(self.world_function(world_id), 0),
        #         # Then it must be in valid range
        #         z3.And(
        #             world_id >= 0,
        #             world_id < max_world_id
        #         )
        #     )
        # )

        # # Add constraint that world IDs must be non-negative
        # positive_world_id = z3.Int('positive_world_id')
        # world_id_constraint = z3.ForAll(
        #     positive_world_id,
        #     z3.Implies(
        #         z3.Select(self.world_function(positive_world_id), 0) == z3.Select(self.world_function(positive_world_id), 0),
        #         positive_world_id >= 0
        #     )
        # )

        # # For each world and time offset, there exists a time-shifted world
        # abundant_world_id = z3.Int('abundant_world_id')
        # pos_shifted_world_id = z3.Int('pos_shifted_world_id')
        # neg_shifted_world_id = z3.Int('neg_shifted_world_id')
        # offset_time = z3.Int('offset_time')
        # base_time = z3.Int('base_time')
        # abundant_worlds = z3.ForAll(
        #     [abundant_world_id, offset_time],  # For each world and time offset
        #     z3.Implies(
        #         z3.And(
        #             offset_time > 0,
        #             offset_time < self.M
        #         ),
        #         z3.Exists(
        #             [pos_shifted_world_id, neg_shifted_world_id],  # There exists another world
        #             z3.ForAll(
        #                 [atom, base_time],  # For each atom and time
        #                 z3.And(
        #                     # Truth conditions match between worlds with positive time offset
        #                     self.truth_condition(
        #                         z3.Select(self.world_function(abundant_world_id), base_time),
        #                         atom
        #                     ) ==
        #                     self.truth_condition(
        #                         z3.Select(self.world_function(pos_shifted_world_id), base_time + offset_time),
        #                         atom
        #                     ),
        #                     # Truth conditions match between worlds with negative time offset
        #                     self.truth_condition(
        #                         z3.Select(self.world_function(abundant_world_id), base_time),
        #                         atom
        #                     ) ==
        #                     self.truth_condition(
        #                         z3.Select(self.world_function(neg_shifted_world_id), base_time - offset_time),
        #                         atom
        #                     )
        #                 )
        #             )
        #         )
        #     )
        # )

        # # Add lawful transitions constraint that applies to any world array
        # lawful_world_id = z3.Int('lawful_world_id')
        # lawful_time = z3.Int('lawful_time')
        # lawful = z3.ForAll(
        #     [lawful_world_id, lawful_time],  # Pass world ID and time variables
        #     z3.Implies(
        #         z3.And(
        #             lawful_world_id >= 0,  # Valid world ID
        #             lawful_time >= 0, lawful_time < self.M - 1  # Valid time
        #         ),
        #         self.task(
        #             z3.Select(self.world_function(lawful_world_id), lawful_time),
        #             z3.Select(self.world_function(lawful_world_id), lawful_time + 1)
        #         )
        #     )
        # )

        # # Ensure we have at least two distinct worlds
        # world_0 = self.world_function(0)
        # world_1 = self.world_function(1)
        # two_worlds_exist = z3.And(
        #     z3.Select(world_0, 0) == z3.Select(world_0, 0),  # world_0 exists
        #     z3.Select(world_1, 0) == z3.Select(world_1, 0),  # world_1 exists
        #     # Allow worlds to differ in truth values
        #     z3.Exists([atom],
        #         z3.Or(
        #             z3.And(
        #                 self.truth_condition(z3.Select(world_0, 0), atom),
        #                 z3.Not(self.truth_condition(z3.Select(world_1, 0), atom))
        #             ),
        #             z3.And(
        #                 z3.Not(self.truth_condition(z3.Select(world_0, 0), atom)),
        #                 self.truth_condition(z3.Select(world_1, 0), atom)
        #             )
        #         )
        #     )
        # )
        
    def true_at(self, sentence, eval_world, eval_time):
        """Returns a Z3 formula that is satisfied when the sentence is true at the given world at eval_time.

        Args:
            sentence: The sentence to evaluate
            eval_world: The world ID (integer) at which to evaluate the sentence
            eval_time: The time point at which to evaluate the sentence
            
        Returns:
            Z3 formula that is satisfied when sentence is true at eval_world at eval_time
        """
        # Get the world array from the world ID
        world_array = self.world_function(eval_world)
        
        sentence_letter = sentence.sentence_letter  # store sentence letter

        # base case
        if sentence_letter is not None:
            eval_world_state = z3.Select(world_array, eval_time)
            return self.truth_condition(eval_world_state, sentence_letter)

        # recursive case
        operator = sentence.operator  # store operator
        arguments = sentence.arguments or () # store arguments
        return operator.true_at(*arguments, eval_world, eval_time) # apply semantics

    def false_at(self, sentence, eval_world, eval_time):
        """Returns a Z3 formula that is satisfied when the sentence is false at eval_world at eval_time.

        Args:
            sentence: The sentence to evaluate
            eval_world: The world ID at which to evaluate the sentence
            eval_time: The time point at which to evaluate the sentence
            
        Returns:
            Z3 formula that is satisfied when sentence is false at eval_world at eval_time
        """
        return z3.Not(self.true_at(sentence, eval_world, eval_time))

    def world_exists(self, world_id, time=None):
        """Checks existence of a world array in the model's state space.

        The state space size is determined by:
        - Each world state is a bitvector of length N (2^N possible states)
        - Each world maps M time points to states ((2^N)^M possible functions)
        - Total unique world arrays = 2^(N*M)

        Args:
            world_id: World identifier to check
            time: Optional time point. If None, checks existence at any valid time

        Returns:
            Z3 formula satisfied when the world exists, checking:
            1. World state is a valid bitvector (implicit Z3 check)
            2. State transitions follow task relation (frame constraints)
            3. World ID maps to an actual model world
        """
        max_world_number = pow(2 ** self.N, 2 * self.M)
        world_valid = z3.And(world_id >= 0, world_id < max_world_number)
        
        if time is None:
            any_time = z3.Int('world_exists_time')
            world_state = z3.Select(self.world_function(world_id), any_time)
            return z3.And(
                world_valid,
                z3.Exists(
                    any_time,
                    world_state == world_state
                )
            )
        else:
            world_state = z3.Select(self.world_function(world_id), time)
            return z3.And(
                world_valid,
                world_state == world_state
            )

    def time_exists(self, time, offset=0):
        """Check if a time is within the valid range.
        
        Args:
            time: The time point to check
            offset: Optional offset to allow for boundary conditions
            
        Returns:
            Z3 formula satisfied when the time exists
        """
        return z3.And(time >= 0, time < self.M + offset)
    
    def is_valid_time_for_world(self, world_id, time):
        """Check if a time is valid for a specific world ID.
        
        Currently, all worlds have the same time interval [0, M).
        
        Args:
            world_id: The world ID to check
            time: The time point to check
            
        Returns:
            Z3 formula satisfied when the time is valid for the world
        """
        # First, ensure the world exists
        world_exists = self.world_exists(world_id, time)
        
        # Then check if the time is within the valid range
        time_valid = self.time_exists(time)
        
        return z3.And(world_exists, time_valid)

    def extract_model_elements(self, z3_model):
        """Extract all model elements from a found model with improved organization.
        
        Args:
            z3_model: The Z3 model to extract elements from
            
        Returns:
            Tuple containing:
            1. Dictionary mapping world keys to their time-state mappings
               {world_key: {time: bitvector_state}}
            2. Dictionary containing main world mapping {time: bitvector_state}
            3. Dictionary of all unique world arrays {world_key: array}
            4. Dictionary of time shift relations between worlds (not implemented yet)
        """
        # First identify all valid world IDs
        all_worlds = self._extract_valid_world_ids(z3_model)
        
        # Extract world arrays for each valid world ID
        world_arrays = self._extract_world_arrays(z3_model, all_worlds)
        
        # Extract time intervals for each world
        world_time_intervals = self._extract_time_intervals(z3_model, all_worlds)
        
        # Extract time-state mappings for each world ID
        world_histories = self._extract_world_histories(z3_model, all_worlds, world_arrays, world_time_intervals)
        
        # Extract time shift relations between worlds
        time_shift_relations = self._extract_time_shift_relations(z3_model, all_worlds, world_histories)
        
        # Identify main world history
        main_world_array = z3_model.evaluate(self.world_function(self.main_world))
        main_world_history = {}
        
        # Find which world key corresponds to the main world
        found_main_world = False
        for world_key, world_array in world_arrays.items():
            if self._arrays_equal(z3_model, world_array, main_world_array):
                main_world_history = world_histories[world_key].copy()
                found_main_world = True
                break
                
        # If we didn't find a matching world, use the world_key that ends with "00"
        # since that's conventionally the main world
        if not found_main_world:
            for world_key, history in world_histories.items():
                if world_key.endswith("00"):
                    main_world_history = history.copy()
                    break
                    
        # Last resort: use the first world history if we still haven't found one
        if not main_world_history and world_histories:
            first_key = next(iter(world_histories))
            main_world_history = world_histories[first_key].copy()
        
        return world_histories, main_world_history, world_arrays, time_shift_relations
    
    def _arrays_equal(self, z3_model, array1, array2):
        """Check if two arrays are equal by comparing their values at all time points."""
        for t in range(self.M):
            val1 = z3_model.evaluate(z3.Select(array1, t))
            val2 = z3_model.evaluate(z3.Select(array2, t))
            # Use Z3's equality check and evaluate the result to get a concrete boolean
            equality = z3_model.evaluate(val1 == val2)
            if z3.is_false(equality):
                return False
        return True
    
    def _extract_valid_world_ids(self, z3_model):
        """Identify all valid world IDs in the model.
        
        Args:
            z3_model: The Z3 model to extract world IDs from
            
        Returns:
            list: List of valid world IDs found in the model
        """
        valid_world_ids = []
        max_world_id = 10  # Start with a reasonable limit
        
        # Always include the main world ID (0)
        valid_world_ids.append(0)
        
        # Try world IDs starting from 1 up to max_world_id (0 already included)
        for world_id in range(1, max_world_id):
            try:
                # Check if this world ID is used in the model
                world_array = z3_model.evaluate(self.world_function(world_id))
                # Check if the world array actually contains valid values
                test_value = z3_model.evaluate(z3.Select(world_array, 0))
                if test_value is not None:
                    if world_id not in valid_world_ids:
                        valid_world_ids.append(world_id)
            except Exception as e:
                # If evaluation fails, this world ID doesn't exist
                continue
                
        # Ensure we have at least the main world
        if not valid_world_ids:
            valid_world_ids.append(0)
                
        return valid_world_ids
    
    def _extract_world_arrays(self, z3_model, valid_world_ids):
        """Extract world arrays for each valid world ID.
        
        Args:
            z3_model: The Z3 model to extract world arrays from
            valid_world_ids: List of valid world IDs to extract arrays for
            
        Returns:
            dict: Mapping from world keys to world arrays
        """
        world_arrays = {}
        
        # Extract existing world arrays for valid world IDs
        for world_id in valid_world_ids:
            try:
                world_key = f'world_function_{world_id:02d}'
                world_array = z3_model.evaluate(self.world_function(world_id))
                # Verify the array is valid by checking a value
                _ = z3_model.evaluate(z3.Select(world_array, 0))
                world_arrays[world_key] = world_array
            except Exception as e:
                # Skip this world ID if there's any issue evaluating it
                continue
        
        # If we have no valid world arrays, create a default one for the main world
        if not world_arrays and valid_world_ids:
            try:
                main_id = 0  # Use 0 as the main world ID
                world_key = f'world_function_{main_id:02d}'
                default_state = z3.BitVecVal(0, self.N)  # Use 0 as the default state
                default_array = self._create_world_array(z3_model, default_state, main_id)
                world_arrays[world_key] = default_array
            except Exception as e:
                # If this fails, we're in trouble, but at least we tried
                pass
        
        # Only generate additional worlds if we need to and already have some valid ones
        if len(world_arrays) > 0 and len(world_arrays) < 2:
            try:
                # Generate additional world arrays from all possible initial states
                world_count = len(world_arrays)
                seen_sigs = set()
                
                # Collect signatures of existing arrays
                for array in world_arrays.values():
                    try:
                        sig = self._get_array_signature(z3_model, array)
                        seen_sigs.add(sig)
                    except:
                        continue
                
                # Only try a limited number of additional states to avoid excessive generation
                max_additional = min(2**self.N, 4)  # Limit to 4 additional worlds
                for state_val in range(max_additional):
                    try:
                        initial_state = z3.BitVecVal(state_val, self.N)
                        world_array = self._create_world_array(z3_model, initial_state, world_count)
                        sig = self._get_array_signature(z3_model, world_array)
                        
                        if sig not in seen_sigs:
                            seen_sigs.add(sig)
                            key = f'world_function_{world_count:02d}'
                            world_arrays[key] = world_array
                            world_count += 1
                            
                            # Stop after generating one additional world
                            if world_count > len(valid_world_ids) + 1:
                                break
                    except:
                        continue
            except Exception as e:
                # If additional world generation fails, continue with what we have
                pass
        
        return world_arrays
    
    def _extract_time_intervals(self, z3_model, valid_world_ids):
        """Extract valid time intervals for each world.
        
        Currently, all worlds use the same time interval [0, M).
        
        Args:
            z3_model: The Z3 model
            valid_world_ids: List of valid world IDs
            
        Returns:
            dict: Mapping from world IDs to their valid time intervals
        """
        # For now, all worlds have the same time interval
        intervals = {}
        for world_id in valid_world_ids:
            intervals[world_id] = (0, self.M)
        return intervals
    
    def _extract_world_histories(self, z3_model, valid_world_ids, world_arrays, time_intervals):
        """Extract time-state mappings for each world ID.
        
        Args:
            z3_model: The Z3 model
            valid_world_ids: List of valid world IDs
            world_arrays: Dictionary of world arrays
            time_intervals: Dictionary of time intervals for each world
            
        Returns:
            dict: Mapping from world keys to dictionaries of time-state mappings
        """
        world_histories = {}
        
        # Process all world arrays to create mappings
        for world_key, world_array in world_arrays.items():
            time_states = {}
            try:
                for time in range(self.M):
                    try:
                        # Evaluate the state at this time point
                        state = z3_model.evaluate(z3.Select(world_array, time))
                        # Convert to a readable state representation
                        if state is not None:
                            state_val = bitvec_to_substates(state, self.N)
                            time_states[time] = state_val
                        else:
                            # Use a default value if evaluation returns None
                            time_states[time] = frozenset([])
                    except Exception as e:
                        # If there's an error for this time point, use a default value
                        time_states[time] = frozenset([])
                
                # Only add to histories if we have at least one valid time point
                if time_states:
                    world_histories[world_key] = time_states
            except Exception as e:
                # Skip this world if there's an overall exception
                continue
                
        # Make sure we have at least one history
        if not world_histories and world_arrays:
            # Try to create a minimal history for the first world
            first_key = next(iter(world_arrays.keys()))
            default_history = {t: frozenset([]) for t in range(self.M)}
            world_histories[first_key] = default_history
        
        return world_histories
    
    def _extract_time_shift_relations(self, z3_model, valid_world_ids, world_histories):
        """Extract time shift relations between worlds.
        
        This is a placeholder for future implementation.
        
        Args:
            z3_model: The Z3 model
            valid_world_ids: List of valid world IDs
            world_histories: Dictionary of world histories
            
        Returns:
            dict: Mapping representing time shift relations (empty for now)
        """
        # Placeholder for future implementation
        return {}
    
    def _get_array_signature(self, z3_model, world_array):
        """Generate a unique signature for a world array based on its state sequence.
        
        Args:
            z3_model: The Z3 model
            world_array: The world array to generate a signature for
            
        Returns:
            tuple: A tuple representing the signature of the world array
        """
        signature = []
        for t in range(self.M):
            try:
                # Get the state value at time t
                state_value = z3_model.evaluate(z3.Select(world_array, t))
                # Convert to string representation
                state_str = str(state_value)
                signature.append(state_str)
            except Exception as e:
                # If there's an error, use a placeholder value
                signature.append(f"error_{t}")
                
        return tuple(signature)
    
    def _create_world_array(self, z3_model, initial_state, world_id):
        """Create a new world array starting with the given state and following task relation.
        
        Args:
            z3_model: The Z3 model
            initial_state: The initial state for the world array
            world_id: The world ID to use for the array
            
        Returns:
            Z3 array: A new world array with states following the task relation
        """
        array = z3.Array(f'world_function_{world_id:02d}', self.TimeSort, self.WorldStateSort)
        array = z3.Store(array, 0, initial_state)
        
        # Fill remaining states following task relation
        current_state = initial_state
        for t in range(1, self.M):
            found_next = False
            for next_val in range(2**self.N):
                next_state = z3.BitVecVal(next_val, self.N)
                if z3.is_true(z3_model.evaluate(self.task(current_state, next_state))):
                    array = z3.Store(array, t, next_state)
                    current_state = next_state
                    found_next = True
                    break
            if not found_next:
                # If no valid next state found, use current state
                array = z3.Store(array, t, current_state)
        return array
    
    # For backward compatibility, provide the old method name
    def extract_model_worlds(self, z3_model):
        """Legacy method that calls extract_model_elements and returns the expected tuple.
        
        Args:
            z3_model: The Z3 model to extract worlds from
            
        Returns:
            Tuple containing world_mappings, main_world_mapping, all_worlds
        """
        world_mappings, main_world_mapping, all_worlds, _ = self.extract_model_elements(z3_model)
        return world_mappings, main_world_mapping, all_worlds


class BimodalProposition(PropositionDefaults):
    """Defines the proposition assigned to the sentences of the language.
    all user has to keep for their own class is super().__init__ and super().__poster_init__
    in the __init__ method.
    """

    def __init__(self, sentence, model_structure, eval_world='main', eval_time='now'):
        """Initialize a BimodalProposition.
        
        Args:
            sentence: The sentence to evaluate
            model_structure: The model structure to evaluate the sentence in
            eval_world: The world ID (integer) at which to evaluate the sentence, or 'main'
            eval_time: The time point at which to evaluate the sentence, or 'now'
        """
        super().__init__(sentence, model_structure)

        self.z3_model = self.model_structure.z3_model
        self.eval_world = self.main_point["world"] if eval_world == 'main' else eval_world
        self.eval_time = self.main_point["time"] if eval_time == 'now' else eval_time
        self.extension = self.find_extension()
        self.truth_set, self.false_set = self.extract_world_states()

    def __eq__(self, other):
        return (
            self.extension == other.extension
            and self.name == other.name
        )

    def __repr__(self):
        z3_model = self.model_structure.z3_model
        
        # Handle truth set
        truth_worlds = set()
        for world_state in self.truth_set:
            if hasattr(world_state, 'as_ast'):  # If it's a Z3 BitVec
                evaluated_bit = z3_model.evaluate(world_state)
                truth_worlds.add(bitvec_to_substates(evaluated_bit, self.N))
            else:  # If it's already evaluated
                print(f"BIT {world_state} TYPE {type(world_state)}")
                truth_worlds.add(bitvec_to_substates(world_state, self.N))
                
        # Handle false set
        false_worlds = set()
        for world_state in self.false_set:  # Note: Changed from truth_set to false_set
            if hasattr(world_state, 'as_ast'):  # If it's a Z3 BitVec
                evaluated_bit = z3_model.evaluate(world_state)
                false_worlds.add(bitvec_to_substates(evaluated_bit, self.N))
            else:  # If it's already evaluated
                print(f"BIT {world_state} TYPE {type(world_state)}")
                false_worlds.add(bitvec_to_substates(world_state, self.N))
                
        return f"< {pretty_set_print(truth_worlds)}, {pretty_set_print(false_worlds)} >"

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
            x, y = z3.BitVecs("prop_cont_x prop_cont_y", semantics.N)
            possibly_true = Exists(
                x,
                semantics.true_at(x, sentence_letter)
            )
            possibly_false = Exists(
                y,
                semantics.false_at(y, sentence_letter)
            )
            return [possibly_true, possibly_false]

        def get_disjoint_constraints():
            """The disjoint_constraints ensure that no two sentence letters can
            be true at the same world state."""
            x = z3.BitVec("prop_dj_x", semantics.N)
            disjoint_constraints = []
            for other_letter in self.sentence_letters:
                if other_letter is not sentence_letter:
                    other_disjoint_atom = ForAll(
                        x,
                        z3.Or(
                            semantics.false_at(x, sentence_letter),
                            semantics.false_at(x, other_letter)
                        )
                    )
                    disjoint_constraints.append(other_disjoint_atom)
            return disjoint_constraints

        # Collect constraints
        constraints = []
        if self.settings['contingent']:
            constraints.extend(get_contingent_constraints())
        if self.settings['disjoint']:
            constraints.extend(get_disjoint_constraints())
        return constraints

    def find_extension(self):
        """Find the extension of the proposition.
        
        Returns:
            A dictionary mapping world arrays to pairs of lists of time points where the
            proposition is true and false, respectively.
        """
        arguments = self.arguments or ()
        all_worlds = self.model_structure.all_worlds
        all_times = self.model_structure.all_times
        if self.sentence_letter is not None:
            world_dictionary = {}
            for world_key, world_array in all_worlds.items():
                true_times = []
                false_times = []
                try:
                    # Extract numeric world ID from the key (e.g., "world_function_00" -> 0)
                    # We try multiple approaches to get a valid world ID
                    if '_' in world_key and world_key.split('_')[-1].isdigit():
                        # Parse from world_function_XX format
                        world_id = int(world_key.split('_')[-1])
                    else:
                        # Default to 0 if we can't parse
                        world_id = 0
                        
                    for time in all_times:
                        try:
                            truth_expr = self.model_structure.semantics.true_at(self.sentence, world_id, time)
                            evaluated_expr = self.z3_model.evaluate(truth_expr)
                            if z3.is_true(evaluated_expr):
                                true_times.append(time)
                            else: false_times.append(time)
                        except Exception as e:
                            # Skip this time point if there's an error
                            continue
                except Exception as e:
                    # If we can't process this world, try a fallback approach
                    for time in all_times:
                        # Default to false for all times in case of error
                        false_times.append(time)
                        
                world_dictionary[world_array] = (true_times, false_times)
            return world_dictionary
        if self.operator is not None:
            return self.operator.find_truth_condition(*arguments, self.eval_world, self.eval_time)
        raise ValueError(f"There is no proposition for {self}.")

    def extract_world_states(self) -> tuple[set, set]:
        """Extract sets of world states where the proposition is true and false.
        
        Processes the proposition's temporal profiles for each world array to determine
        the set of world states where the proposition is true and where it is false.
        
        Returns:
            tuple[set, set]: A pair of sets containing:
                - First set: World states where the proposition is true
                - Second set: World states where the proposition is false
        """
        # Extract states where proposition is true using set comprehension
        truth_states = {
            world_array[time]
            for world_array, (true_times, _) in self.extension.items()
            for time in true_times
        }
        # Extract states where proposition is false using set comprehension
        false_states = {
            world_array[time]
            for world_array, (_, false_times) in self.extension.items()
            for time in false_times
        }
        return truth_states, false_states

    def truth_value_at(self, eval_world, eval_time):
        """Checks if the proposition is true at the given world and time.
        
        Args:
            eval_world: The world ID or world array at which to evaluate
            eval_time: The time point at which to evaluate
            
        Returns:
            bool: True if the proposition is true at eval_world and eval_time
        """
        # If we're given a world ID, convert it to a world array
        if isinstance(eval_world, int):
            world_array = self.model_structure.get_world_array(eval_world)
        else:
            world_array = eval_world
            
        true_times, false_times = self.extension[world_array]
        true_in_eval_world = eval_time in true_times
        false_in_eval_world = eval_time in false_times
        if true_in_eval_world == false_in_eval_world:
            eval_state = world_array[eval_time]
            print( # NOTE: a warning is preferable to raising an error
                f"WARNING: the world {bitvec_to_substates(eval_state, self.N)} makes "
                f"{self} both true and false."
            )
        return true_in_eval_world

    def print_proposition(self, eval_point, indent_num, use_colors):
        """Print the proposition and it's truth value at the evaluation point."""
        
        if self.z3_model is None:
            print(f"{'  ' * indent_num}Cannot evaluate proposition - no valid model found")
            return

        # Get the world ID/array, time value, and world_state
        eval_time = eval_point["time"]
        eval_world = eval_point["world"]

        if eval_world is None:
            print(f"{'  ' * indent_num}Cannot evaluate proposition - no evaluation world available")
            return

        if eval_time is None:
            print(f"{'  ' * indent_num}Cannot evaluate proposition - no evaluation time available")
            return
        
        # Get the world array if we're given a world ID
        if isinstance(eval_world, int):
            world_array = self.model_structure.get_world_array(eval_world)
        else:
            world_array = eval_world
            
        truth_value = self.truth_value_at(eval_world, eval_time)
        world_state = self.z3_model.evaluate(z3.Select(world_array, eval_time))

        world_state_repr = bitvec_to_substates(world_state, self.N)
        RESET, FULL, PART = self.set_colors(
            self.name,
            indent_num,
            truth_value,
            world_state_repr,
            use_colors
        )
        print(
            f"{'  ' * indent_num}{FULL}|{self.name}| = {self}{RESET}"
            f"  {PART}({truth_value} in {world_state_repr}){RESET}"
        )


# TODO: print time series
class BimodalStructure(ModelDefaults):

    def __init__(self, model_constraints, max_time=1):
        # Initialize parent class first
        super().__init__(model_constraints, max_time)

        # Get main point
        self.main_world = self.main_point["world"]
        self.main_time = self.main_point["time"]
        self.M = self.semantics.M
        self.all_times = range(0, self.M)

        # Initialize Z3 model values
        self.z3_main_world = None
        self.z3_main_time = None
        self.z3_main_world_state = None
        self.world_mappings = None  # Will store all world states after model is found

        # Only evaluate if we have a valid model
        if self.z3_model_status and self.z3_model is not None:
            # Get the main world array and time
            main_world_array = self.z3_model.evaluate(self.semantics.world_function(self.main_world))
            self.z3_main_world = main_world_array
            self.z3_main_time = self.z3_model.evaluate(self.main_time)
            
            # Extract all world mappings from the model
            self.world_mappings, self.main_world_mapping, self.all_worlds = self.semantics.extract_model_worlds(self.z3_model)
            
            if self.z3_main_world is not None and self.z3_main_time is not None:
                # Evaluate the world state of the main_world at the main_time
                self.z3_main_world_state = self.z3_model.evaluate(z3.Select(self.z3_main_world, self.z3_main_time))
            
            for world_array in self.all_worlds.values():
                self.semantics.all_true[world_array] = (list(self.all_times), [])
                self.semantics.all_false[world_array] = ([], list(self.all_times))
    
    def get_world_array(self, world_id):
        """Get the world array for a given world ID.
        
        Args:
            world_id: The world ID to get the array for
            
        Returns:
            The world array for the given world ID
            
        Raises:
            ValueError: If the world ID does not exist in the model
        """
        if self.z3_model is None:
            raise ValueError("Cannot get world array when z3_model is None")
            
        # Try to get the world array from the all_worlds dictionary
        for key, world_array in self.all_worlds.items():
            if key.endswith(f"{world_id:02d}"):
                return world_array
        
        # If not found, evaluate it from the world function
        try:
            return self.z3_model.evaluate(self.semantics.world_function(world_id))
        except Exception as e:
            raise ValueError(f"World ID {world_id} does not exist in the model: {e}")
    
    def get_world_history(self, world_id):
        """Get the world history for a given world ID.
        
        Args:
            world_id: The world ID to get the history for
            
        Returns:
            The world history (mapping from times to states) for the given world ID
            
        Raises:
            ValueError: If the world ID does not exist in the model
        """
        if self.world_mappings is None:
            raise ValueError("Cannot get world history when world_mappings is None")
            
        # Try to get the world history from the world_mappings dictionary
        for key, history in self.world_mappings.items():
            if key.endswith(f"{world_id:02d}"):
                return history
                
        raise ValueError(f"World ID {world_id} does not exist in the model")


    # def find_truth_condition(self, sentence):
    #     """Find the temporal extension of a sentence across all worlds in the model.
    #
    #     For each world array in the model, determines the times at which the given sentence
    #     is true in that world, creating a mapping from worlds to their temporal profiles.
    #
    #     Args:
    #         sentence: The sentence whose extension is to be found
    #
    #     Returns:
    #         dict: A mapping from world arrays to lists of time points where the sentence is true,
    #              or None if no valid model exists. The structure is:
    #              {world_array: [t1, t2, ...]} where each time is a time point where the 
    #              sentence is true in that world
    #     """
    #     if self.z3_model is None or self.world_mappings is None:
    #         return None
    #     world_dictionary = {}
    #     for world_array in self.all_worlds.values():
    #         temporal_profile = []
    #         inverse_profile = []
    #         for time in self.all_times:
    #             truth_expr = self.semantics.true_at(sentence, world_array, time)
    #             evaluated_expr = self.z3_model.evaluate(truth_expr)
    #             if z3.is_true(evaluated_expr):
    #                 temporal_profile.append(time)
    #             else: inverse_profile.append(time)
    #         world_dictionary[world_array] = (temporal_profile, inverse_profile)
    #     return world_dictionary

    def print_evaluation(self, output=sys.__stdout__):
        """print the evaluation world and all sentences letters that true/false
        in that world"""
        if self.z3_model is None:
            raise ValueError(f"Cannot print_evaluation when z3_model is None.")

        BLUE = ""
        RESET = ""
        if output is sys.__stdout__:
            BLUE = "\033[34m"
            RESET = "\033[0m"
        if self.z3_main_world_state is None:
            print("No evaluation world state available - no valid model found\n", file=output)
            return

        main_world = self.z3_main_world
        main_world_mapping = self.main_world_mapping

        # Create the sequence of states connected by arrows
        state_sequence = []
        for time in sorted(main_world_mapping.keys()):
            state_sequence.append(str(main_world_mapping[time]))
        # Join states with arrows and print
        world_line = " ==> ".join(state_sequence)

        eval_time = self.z3_main_time
        eval_world_state = self.z3_main_world_state
        print(
            f"\nEvaluation Point:\n"
            + f"  {BLUE}World: {world_line}{RESET}\n"
            + f"  {BLUE}Time: {eval_time}{RESET}\n"
            + f"  {BLUE}World State: {bitvec_to_substates(eval_world_state, self.N)}{RESET}\n",
            file=output,
        )

    def print_worlds_and_times(self, output=sys.__stdout__):
        """Print all fusions of atomic states in the model."""

        def binary_bitvector(bit):
            return (
                bit.sexpr()
                if self.N % 4 != 0
                else int_to_binary(int(bit.sexpr()[2:], 16), self.N)
            )
        
        def format_state(bin_rep, state, color, label=""):
            """Helper function to format and print a state."""
            label_str = f" ({label})" if label else ""
            use_colors = output is sys.__stdout__
            if use_colors:
                print(f"  {self.WHITE}{bin_rep} = {color}{state}{label_str}{self.RESET}", file=output)
            else:
                print(f"  {bin_rep} = {state}{label_str}", file=output)

        # Print formatted state space
        print("Possible Worlds:", file=output)
        if self.z3_model is None or self.world_mappings is None:
            raise ValueError("Can't print possible worlds without a z3_model.")
        for world_array, time_states in self.world_mappings.items():

            # Create the sequence of states connected by arrows
            state_sequence = []
            for time in sorted(time_states.keys()):
                state_sequence.append(str(time_states[time]))
                
            # Join states with arrows and print
            world_line = " ==> ".join(state_sequence)
            print(f"  {world_array}: {world_line}", file=output)

    def print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__):
        """prints states, sentence letters evaluated at the designated world and
        recursively prints each sentence and its parts"""
        model_status = self.z3_model_status
        self.print_info(model_status, default_settings, example_name, theory_name, output)
        if model_status:
            self.print_worlds_and_times(output)
            self.print_evaluation(output)
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4) 
                print(f"Total Run Time: {total_time} seconds\n", file=output)
                print(f"{'='*40}", file=output)
            return

    def print_to(self, default_settings, example_name, theory_name, print_constraints=None, output=sys.__stdout__):
        """append all elements of the model to the file provided
        
        Args:
            print_constraints: Whether to print constraints. Defaults to value in settings.
            output: Output stream to print to. Defaults to sys.stdout.
        """
        if print_constraints is None:
            print_constraints = self.settings["print_constraints"]
        if self.timeout:
            print(f"TIMEOUT: {self.timeout}")
            print(f"No model for example {example_name} found before timeout.", file=output)
            print(f"Try increasing max_time > {self.max_time}.\n", file=output)
            return
        self.print_all(default_settings, example_name, theory_name, output)
        if print_constraints and self.unsat_core is not None:
            self.print_grouped_constraints(output)

    def save_to(self, example_name, theory_name, include_constraints, output):
        """append all elements of the model to the file provided"""
        constraints = self.model_constraints.all_constraints
        self.print_all(example_name, theory_name, output)
        self.build_test_file(output)
        if include_constraints:
            print("# Satisfiable constraints", file=output)
            print(f"all_constraints = {constraints}", file=output)
