import sys
import time
import z3

# Try local imports first (for development)
try:
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
except ImportError:
    # Fall back to installed package imports
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

        self.main_world = self.world_function(0)

        self.main_time = z3.Int('main_time')

        self.main_point = {
            "world": self.main_world,
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
        """Returns a Z3 formula that is satisfied when the sentence is true at eval_world at eval_time.

        Args:
            sentence: The sentence to evaluate
            eval_world: The world state array or single world state at which to evaluate the sentence
            eval_time: The time point at which to evaluate the sentence
            
        Returns:
            Z3 formula that is satisfied when sentence is true at eval_world at eval_time
        """

        sentence_letter = sentence.sentence_letter  # store sentence letter

        # base case
        if sentence_letter is not None:
            eval_world_state = z3.Select(eval_world, eval_time)
            return self.truth_condition(eval_world_state, sentence_letter)

        # recursive case
        operator = sentence.operator  # store operator
        arguments = sentence.arguments or () # store arguments
        return operator.true_at(*arguments, eval_world, eval_time) # apply semantics

    def false_at(self, sentence, eval_world, eval_time):
        """Returns a Z3 formula that is satisfied when the sentence is false at eval_world at eval_time.

        Args:
            sentence: The sentence to evaluate
            eval_world: The world state array at which to evaluate the sentence
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
        """Check if a world array exists for the given world ID."""
        return z3.And(time >= 0, time < self.M + offset)

    def extract_model_worlds(self, z3_model):
        """Extract all world states from a found model by examining model declarations
        and recovering all worlds that satisfy the task relation.
        
        Args:
            z3_model: The Z3 model to extract worlds from
            
        Returns:
            Tuple containing:
            1. Dictionary mapping world arrays to their time-state mappings
               {world_array: {time: bitvector_state}}
            2. Dictionary containing main world mapping {time: bitvector_state}
            3. Dictionary of all unique world arrays {world_key: array}
        """
        main_world_mapping = {}
        world_mappings = {}
        all_worlds = {}
        seen_sigs = set()
        world_count = 0

        def get_array_signature(world_array):
            """Generate a unique signature for a world array based on its state sequence"""
            return tuple(str(z3_model.eval(z3.Select(world_array, t))) 
                       for t in range(self.M))

        def create_world_array(initial_state, world_id):
            """Create a new world array starting with the given state and following task relation"""
            array = z3.Array(f'world_function_{world_id:02d}', self.TimeSort, self.WorldStateSort)
            array = z3.Store(array, 0, initial_state)
            
            # Fill remaining states following task relation
            current_state = initial_state
            for t in range(1, self.M):
                found_next = False
                for next_val in range(2**self.N):
                    next_state = z3.BitVecVal(next_val, self.N)
                    if z3.is_true(z3_model.eval(self.task(current_state, next_state))):
                        array = z3.Store(array, t, next_state)
                        current_state = next_state
                        found_next = True
                        break
                if not found_next:
                    # If no valid next state found, use current state
                    array = z3.Store(array, t, current_state)
            return array

        # First, get the main world and add it
        main_world_array = z3_model.eval(self.main_world)
        main_sig = get_array_signature(main_world_array)
        seen_sigs.add(main_sig)
        all_worlds['world_function_00'] = main_world_array
        world_count += 1

        # Examine model declarations to find all world arrays
        for decl in z3_model.decls():
            if decl.name().startswith('world_function_'):
                array = z3_model.get_interp(decl)
                if array is not None:
                    sig = get_array_signature(array)
                    if sig not in seen_sigs:
                        seen_sigs.add(sig)
                        key = f'world_function_{world_count:02d}'
                        all_worlds[key] = array
                        world_count += 1

        # Generate additional worlds from all possible initial states
        for state_val in range(2**self.N):
            initial_state = z3.BitVecVal(state_val, self.N)
            world_array = create_world_array(initial_state, world_count)
            sig = get_array_signature(world_array)
            
            if sig not in seen_sigs:
                seen_sigs.add(sig)
                key = f'world_function_{world_count:02d}'
                all_worlds[key] = world_array
                world_count += 1

        # Process all world arrays to create mappings
        for world_key, world_array in all_worlds.items():
            time_states = {}
            for time in range(self.M):
                state = z3_model.eval(z3.Select(world_array, time))
                state_val = bitvec_to_substates(state, self.N)
                time_states[time] = state_val
            world_mappings[world_key] = time_states

            # If this is the main world, create its mapping
            if get_array_signature(world_array) == main_sig:
                main_world_mapping = time_states.copy()

        return world_mappings, main_world_mapping, all_worlds


class BimodalProposition(PropositionDefaults):
    """Defines the proposition assigned to the sentences of the language.
    all user has to keep for their own class is super().__init__ and super().__poster_init__
    in the __init__ method.
    """

    def __init__(self, sentence, model_structure, eval_world='main', eval_time='now'):

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
        """takes self, returns the V, F tuple
        used in find_verifiers_and_falsifiers"""
        arguments = self.arguments or ()
        all_arrays = self.model_structure.all_worlds.values()
        all_times = self.model_structure.all_times
        if self.sentence_letter is not None:
            world_dictionary = {}
            for world_array in all_arrays:
                true_times = []
                false_times = []
                for time in all_times:
                    truth_expr = self.model_structure.semantics.true_at(self.sentence, world_array, time)
                    evaluated_expr = self.z3_model.evaluate(truth_expr)
                    if z3.is_true(evaluated_expr):
                        true_times.append(time)
                    else: false_times.append(time)
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
        """Checks if there is a verifier or falsifier in world and not both."""
        true_times, false_times = self.extension[eval_world]
        true_in_eval_world = eval_time in true_times
        false_in_eval_world = eval_time in false_times
        if true_in_eval_world == false_in_eval_world:
            eval_state = eval_world[eval_time]
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

        # Get the world, time value, and world_state
        eval_time = eval_point["time"]
        eval_world = eval_point["world"]

        if eval_world is None:
            print(f"{'  ' * indent_num}Cannot evaluate proposition - no evaluation world available")
            return

        if eval_time is None:
            print(f"{'  ' * indent_num}Cannot evaluate proposition - no evaluation time available")
            return
        
        truth_value = self.truth_value_at(eval_world, eval_time)
        world_state = self.z3_model.evaluate(eval_world[eval_time])

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
            # Evaluate the main world array and time
            # TODO: avoid storing z3_main_world and z3_main_time?
            self.z3_main_world = self.z3_model.evaluate(self.main_world)
            self.z3_main_time = self.z3_model.evaluate(self.main_time)
            self.main_point["world"] = self.z3_main_world
            self.main_point["time"] = self.z3_main_time
            # Extract all world mappings from the model
            self.world_mappings, self.main_world_mapping, self.all_worlds = self.semantics.extract_model_worlds(self.z3_model)
            if self.z3_main_world is not None and self.z3_main_time is not None:
                # Evaluate the world state of the main_world at the main_time
                self.z3_main_world_state = self.z3_model.evaluate(z3.Select(self.z3_main_world, self.z3_main_time))
            for world_array in self.all_worlds:
                self.semantics.all_true[world_array] = (list(self.all_times), [])
                self.semantics.all_false[world_array] = ([], list(self.all_times))


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
