import sys
import time
import z3

# Standard imports
from model_checker.model import (
    SemanticDefaults,
    PropositionDefaults,
    ModelDefaults,
)
from model_checker.utils import (
    ForAll,
    Exists,
    bitvec_to_worldstate,
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
        'N': 2,
        # Number of times
        'M': 2,
        # Whether sentence_letters are assigned to contingent propositions
        'contingent': False,
        # Whether sentence_letters are assigned to distinct world_states
        'disjoint': False,
        # Maximum time Z3 is permitted to look for a model
        'max_time': 1,
        # Whether a model is expected or not (used for unit testing)
        'expectation': True,
    }
    
    # Bimodal-specific general settings defaults
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "maximize": False,
        "align_vertically": True,
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
        self.premise_behavior, self.conclusion_behavior = self.define_invalidity()

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
        
        In bimodal logic we distinguish between:
        - World States: Instantaneous configurations of the system (e.g., {a, b, c})
        - World Histories: Temporally extended sequences of states that follow lawful transitions
        
        This method initializes:
        - task: A binary relation between world states representing transitions between states
        - world_function: A mapping from world IDs to world histories (arrays mapping time -> world state)
        - truth_condition: A function assigning truth values to atomic propositions at instantaneous world states
        - main_world: The primary world history used for evaluation (world_function applied to ID 0)
        - main_time: The time point at which sentences are evaluated
        - main_point: Dictionary containing the main world history and evaluation time
        - is_world: A boolean function indicating whether a world_id maps to a valid world history
        """
        # Define the task relation between world states
        self.task = z3.Function(
            "Task",
            self.WorldStateSort,
            self.WorldStateSort,
            z3.BoolSort()
        )

        # Mapping from world IDs to world histories (arrays from time to state)
        self.world_function = z3.Function(
            'world_function', 
            self.WorldIdSort,  # Input: world ID 
            z3.ArraySort(self.TimeSort, self.WorldStateSort)  # Output: world history
        )

        # Function to determine if a world_id maps to a valid world history
        self.is_world = z3.Function(
            'is_world',
            self.WorldIdSort,  # Input: world ID
            z3.BoolSort()      # Output: whether it's a valid world history
        )

        # Set a reasonable limit on world IDs for efficiency
        self.max_world_id = self.M * (2 ** (self.M * self.N))  # Number of possible world histories
        
        # Truth condition for atomic propositions at world states
        self.truth_condition = z3.Function(
            "truth_condition",
            self.WorldStateSort,
            syntactic.AtomSort,
            z3.BoolSort()
        )

        # Define interval tracking functions
        self.world_interval_start = z3.Function(
            'world_interval_start',
            self.WorldIdSort,  # World ID
            self.TimeSort      # Start time of interval
        )
        
        self.world_interval_end = z3.Function(
            'world_interval_end',
            self.WorldIdSort,  # World ID
            self.TimeSort      # End time of interval
        )
        
        # Dictionary to store world time intervals after extraction
        self.world_time_intervals = {}
        
        # Main point of evaluation includes a world ID and time
        self.main_world = 0             # Store world ID, not array reference
        self.main_time = z3.IntVal(0)   # Fix the main time to 0 
        self.main_point = {
            "world": self.main_world,  
            "time": self.main_time,
        } 

    def build_frame_constraints(self):
        """Build the frame constraints for the bimodal logic model.

        This method constructs the fundamental constraints that define the behavior of the model:
        1. Time constraints - Ensures main_time is within valid range
        2. Truth value constraints - Each atomic sentence must have a definite truth value at each instantaneous world state
        3. Lawful transitions - Each world history must follow the task relation between consecutive states
        4. Task restriction - The task relation only holds between consecutive states that appear in some world history
        5. World diversity - Ensures different world histories exist for proper modal evaluation
        6. Valid worlds - Constraints on which world_ids map to valid world histories
        7. World interval constraint - Ensures each world has a valid time interval
        8. Abundance constraint - Ensures necessary time-shifted worlds exist
        9. Systematic world relationship - Explicitly defines relationships between world IDs
        10. Task state minimization - Encourages minimal changes between consecutive world states
        
        The frame constraints ensure that world histories represent lawful evolutions of world states
        over time, following the task relation which specifies valid state transitions.

        Returns:
            list: A list of Z3 constraints that define the frame conditions for the model
        """
        # 1. The main_world must be valid
        valid_main_world = self.is_world(self.main_world)
        
        # 2. The main_time must be valid
        valid_main_time = self.is_valid_time(self.main_time)
        
        # 3. Each sentence letter is true or false (and not both which is unsat)
        world_state = z3.BitVec('world_state', self.N)
        sentence_letter = z3.Const('atom_interpretation', syntactic.AtomSort)
        classical_truth = z3.ForAll(
            [world_state, sentence_letter],
            z3.Or(
                # Either sentence_letter is true in the world_state
                self.truth_condition(world_state, sentence_letter),
                # Or not
                z3.Not(self.truth_condition(world_state, sentence_letter))
            )
        )
        
        # 4. World enumeration starts at 0
        enumerate_world = z3.Int('enumerate_world')
        enumeration_constraint = z3.ForAll(
            [enumerate_world],
            z3.Implies(
                # If enumerate_world is a world
                self.is_world(enumerate_world),
                # Then it's non-negative
                enumerate_world >= 0,
            )
        )
        
        # 5. The worlds form a convex ordering (no gaps)
        # Implements "lazy" world creation by ensuring worlds are created in sequence
        convex_world = z3.Int('convex_world')
        convex_world_ordering = z3.ForAll(
            [convex_world],
            z3.Implies(
                # If both:
                z3.And(
                    # The convex_world is a world
                    self.is_world(convex_world),
                    # And greater than 0
                    convex_world > 0,
                ),
                # Then world_id - 1 must be valid
                self.is_world(convex_world - 1)
            )
        )
        
        # 6. Worlds are lawful (each world state can has task to its successor, if any)
        lawful_world = z3.Int('lawful_world_id')
        lawful_time = z3.Int('lawful_time')
        lawful = z3.ForAll(
            [lawful_world, lawful_time],
            # If for any lawful_world and lawful time
            z3.Implies(
                z3.And(
                    # The lawful_world is a valid world
                    self.is_world(lawful_world),
                    # The lawful_time is in (-M - 1, M - 1), so has a successor
                    self.is_valid_time(lawful_time, -1),  
                    # The lawful_time is in the lawful_world
                    self.is_valid_time_for_world(lawful_world, lawful_time),
                    # The successor of the lawful_time is in the lawful_world
                    self.is_valid_time_for_world(lawful_world, lawful_time + 1),
                ),
                # Then there is a task
                self.task(
                    # From the lawful_world at the lawful_time
                    z3.Select(self.world_function(lawful_world), lawful_time),
                    # To the lawful_world at the successor of the lawful_time
                    z3.Select(self.world_function(lawful_world), lawful_time + 1)
                )
            )
        )
        
        # 7. All valid time-shifted worlds exist
        skolem_abundance = self.skolem_abundance_constraint()
        
        # 8. World interval constraint
        time_interval = self.time_interval_constraint()
        world_interval = self.world_interval_constraint()
        
        # 9. Every valid world is unique
        world_one = z3.Int('world_one')
        world_two = z3.Int('world_two')
        some_time = z3.Int('some_time')
        world_uniqueness = z3.ForAll(
            [world_one, world_two],
            z3.Implies(
                z3.And(
                    self.is_world(world_one),
                    self.is_world(world_two),
                    world_one != world_two
                ),
                # Worlds must differ at some time point that is valid for both
                z3.Exists(
                    [some_time],
                    z3.And(
                        self.is_valid_time(some_time),
                        self.is_valid_time_for_world(world_one, some_time),
                        self.is_valid_time_for_world(world_two, some_time),
                        z3.Select(self.world_function(world_one), some_time) !=
                        z3.Select(self.world_function(world_two), some_time)
                    )
                )
            )
        )

        # 10. Task relation only holds between states in lawful world histories
        some_state = z3.BitVec('task_restrict_some_state', self.N)
        next_state = z3.BitVec('task_restrict_next_state', self.N)
        task_world = z3.Int('task_world')
        time_shifted = z3.Int('time_shifted')
        task_restriction = z3.ForAll(
            [some_state, next_state],
            z3.Implies(
                # If there is a task from some_state to next_state
                self.task(some_state, next_state),
                # Then for some task_world at time_shifted:
                z3.Exists(
                    [task_world, time_shifted],
                    z3.And(
                        # The task_world is a valid world
                        self.is_world(task_world),
                        # The successor or time_shifted is a valid time
                        self.is_valid_time(time_shifted, -1),
                        # Where time_shifted is a time in the task_world,
                        self.is_valid_time_for_world(task_world, time_shifted),
                        # The successor of time_shifted is a time in the task_world
                        self.is_valid_time_for_world(task_world, time_shifted + 1),
                        # The task_world is in some_state at time_shifted
                        some_state == z3.Select(self.world_function(task_world), time_shifted),
                        # And the task_world is in next_state at the successor of time_shifted
                        next_state == z3.Select(self.world_function(task_world), time_shifted + 1)
                    )
                )
            )
        )

        # 11. Task state minimization - Encourages minimal changes between consecutive world states
        task_minimization = self.build_task_minimization_constraint()

        
        return [
            # NOTE: order matters!
            valid_main_world,
            valid_main_time,
            classical_truth,
            enumeration_constraint,
            convex_world_ordering,
            lawful,
            skolem_abundance,
            world_uniqueness,
            time_interval,

            # MAYBE
            # task_restriction,
            # task_minimization,
            # world_interval,
        ]

    def is_valid_time(self, given_time, offset=0):
        """Check if a time point exists in the expanded time domain.
        
        Modified to support an expanded time domain that includes negative values.
        
        Args:
            time: The time point to check
            offset: Optional offset to add to the bounds
            
        Returns:
            Z3 formula that is true if the time point exists
        """
        # Allow times in the range (-M, M)
        return z3.And(given_time > -self.M + offset, given_time < self.M + offset)
        
    def is_valid_time_for_world(self, given_world, given_time):
        """Check if a time is valid for a specific world.
        
        Args:
            world_id: World identifier
            time: Time point to check
            
        Returns:
            Z3 formula that is true if the time is within the world's interval
        """
        return z3.And(
            given_time >= self.world_interval_start(given_world),
            given_time <= self.world_interval_end(given_world)
        )

    def can_shift_forward(self, given_world):
        """Check if a world can be shifted forward by 1 (Z3 expression).
        
        Args:
            world_id: World identifier
            
        Returns:
            Z3 formula that is true if the world can be shifted forward
        """
        # A world can shift forward if its end time + 1 is still within global range
        return self.world_interval_end(given_world) < z3.IntVal(self.M - 1)
    
    def is_shifted_by(self, source_world, shift, target_world):
        """Predicate that target_id is a world shifted from source_id by shift amount.
        
        Args:
            source_id: Source world identifier
            shift: Shift amount
            target_id: Target world identifier
            
        Returns:
            Z3 formula that is true if target is shifted from source by amount
        """
        return z3.And(
            # Target interval must be shifted by the specified amount
            self.world_interval_start(target_world) == self.world_interval_start(source_world) + z3.IntVal(shift),
            self.world_interval_end(target_world) == self.world_interval_end(source_world) + z3.IntVal(shift),
            # World states must match when shifted
            self.matching_states_when_shifted(source_world, shift, target_world)
        )

    def matching_states_when_shifted(self, source_world, shift, target_world):
        """Check if states match when shifted between world arrays.
        
        Args:
            source_id: Source world identifier
            shift: Shift amount
            target_id: Target world identifier
            
        Returns:
            Z3 formula that is true if states match when shifted
        """
        time = z3.Int('shift_check_time')
        source_array = self.world_function(source_world)
        target_array = self.world_function(target_world)
        
        return z3.ForAll(
            [time],
            z3.Implies(
                z3.And(
                    # Time is within source interval
                    z3.And(
                        time >= self.world_interval_start(source_world),
                        time <= self.world_interval_end(source_world)
                    ),
                    # Shifted time is within target interval
                    z3.And(
                        time + z3.IntVal(shift) >= self.world_interval_start(target_world),
                        time + z3.IntVal(shift) <= self.world_interval_end(target_world)
                    )
                ),
                # States must match when shifted
                z3.Select(source_array, time) == z3.Select(target_array, time + z3.IntVal(shift))
            )
        )
    
    def can_shift_backward(self, world_id):
        """Check if a world can be shifted backward by 1 (Z3 expression).
        
        Args:
            world_id: World identifier
            
        Returns:
            Z3 formula that is true if the world can be shifted backward
        """
        # A world can shift backward if its start time - 1 is still within global range
        return self.world_interval_start(world_id) > z3.IntVal(-self.M + 1)
    
    def world_interval_constraint(self):
        """Build constraint ensuring each world has a valid time interval."""
        # Define all valid time intervals
        time_intervals = self.generate_time_intervals(self.M)
        
        # Variable for world being constrained
        interval_world = z3.Int('interval_world')
        
        # Stock of intervals to populate
        interval_options = []

        # For any time interval in time_intervals with start_time and end_time
        for start_time, end_time in time_intervals:
            interval_constraint = z3.And(
                # The interval_world starts at the start_time and ends at the end_time
                self.has_interval(interval_world, start_time, end_time),
                # Constraints to ensure the world array is defined only for this interval
                self.valid_array_domain(interval_world, start_time, end_time)
            )
            interval_options.append(interval_constraint)
        
        # For any interval_world
        world_interval_constraint = z3.ForAll(
            [interval_world],
            z3.Implies(
                # If interval_world is a valid world
                self.is_world(interval_world),
                # Must have exactly one of the valid time intervals in time_intervals
                z3.Or(*interval_options)
            )
        )
        return world_interval_constraint

    def time_interval_constraint(self):
        """Build an optimized constraint ensuring each world has a valid time interval.
        
        This optimized version avoids nested universal quantifiers by directly
        constraining the interval functions to specific values for each world.
        It pre-computes the valid interval options and creates direct constraints
        rather than using nested quantification.
        
        Returns:
            Z3 formula that constrains world intervals to valid values
        """
        # Generate valid time intervals
        time_intervals = self.generate_time_intervals(self.M)
        
        # Variable for world being constrained
        interval_world = z3.Int('interval_world')
        
        # Create direct mapping for interval bounds
        interval_constraints = []
        
        # For each valid world ID, create direct interval constraints
        for world_id in range(self.max_world_id):
            # Create a condition for this specific world ID
            world_condition = (interval_world == world_id)
            
            # Create interval options for this world
            world_interval_options = []
            
            # For any time interval in time_intervals with start_time and end_time
            for i, (start_time, end_time) in enumerate(time_intervals):
                # Create a direct constraint for this interval option
                interval_option = z3.And(
                    self.world_interval_start(world_id) == z3.IntVal(start_time),
                    self.world_interval_end(world_id) == z3.IntVal(end_time)
                )
                world_interval_options.append(interval_option)
            
            # A world must have exactly one of the valid intervals if it exists
            world_constraint = z3.Implies(
                self.is_world(world_id),
                z3.Or(*world_interval_options)
            )
            
            interval_constraints.append(world_constraint)
        
        # Combine all world constraints
        return z3.And(*interval_constraints)

    def has_interval(self, given_world, start_time, end_time):
        """Predicate indicating a world has a specific interval.
        
        Args:
            world_id: World identifier
            start: Start time of interval
            end: End time of interval
            
        Returns:
            Z3 formula that is true if world has the specified interval
        """
        return z3.And(
            # The given_world starts at start_time
            self.world_interval_start(given_world) == z3.IntVal(start_time),
            # The given_world ends at end_time
            self.world_interval_end(given_world) == z3.IntVal(end_time)
        )
    
    def valid_array_domain(self, given_world, start_time, end_time):
        """Ensure world array is defined only for times in its interval.
        
        Args:
            world_id: World identifier
            start: Start time of interval
            end: End time of interval
            
        Returns:
            Z3 formula that ensures array is properly defined for this interval
        """
        other_time = z3.Int('other_time')
        return z3.ForAll(
            [other_time],
            z3.Implies(
                # If other_time is valid in the given_world
                self.is_valid_time_for_world(given_world, other_time),
                # Then other_time is both:
                z3.And(
                    # At or after the start_time
                    z3.IntVal(start_time) <= other_time,
                    # And at or before the end_time
                    other_time <= z3.IntVal(end_time)
                )
            )
        )
    
    def build_abundance_constraint(self):
        """Build constraint ensuring necessary time-shifted worlds exist.
        
        The abundance property ensures that for any world that can be shifted forward
        or backward in time (while staying within valid time bounds), there exists a
        corresponding world that represents that time shift.
        """
        source_world = z3.Int('abundance_source_id')
        forward_world = z3.Int('forward_world')
        backwards_world = z3.Int('backwards_world')
        
        # Each world must have appropriate time-shifted counterparts
        abundance_constraint = z3.ForAll(
            [source_world],
            z3.Implies(
                # If the source_world is a valid world
                self.is_world(source_world),
                # Then both:
                z3.And(
                    # Forwards condition
                    z3.Implies(
                        # If source can shift forward
                        self.can_shift_forward(source_world),
                        # Then some forward-shifted world exists
                        z3.Exists(
                            [forward_world],
                            z3.And(
                                self.is_world(forward_world),
                                self.is_shifted_by(source_world, 1, forward_world)
                            )
                        )
                    ),
                    # Backwards condition
                    z3.Implies(
                        # If source can shift backwards
                        self.can_shift_backward(source_world),
                        # Then some backwards-shifted world exists
                        z3.Exists(
                            [backwards_world],
                            z3.And(
                                self.is_world(backwards_world),
                                self.is_shifted_by(source_world, -1, backwards_world)
                            )
                        )
                    )
                )
            )
        )
        return abundance_constraint

    def skolem_abundance_constraint(self):
        """Build constraint ensuring necessary time-shifted worlds exist using Skolemization.
        
        The abundance property ensures that for any world that can be shifted forward
        or backward in time (while staying within valid time bounds), there exists a
        corresponding world that represents that time shift.
        
        This implementation uses Skolem functions to eliminate nested quantifiers,
        which can improve Z3 performance.
        """
        # Define Skolem functions that directly compute the necessary worlds
        forward_of = z3.Function('forward_of', self.WorldIdSort, self.WorldIdSort)
        backward_of = z3.Function('backward_of', self.WorldIdSort, self.WorldIdSort)
        
        # Variable for world being constrained
        source_world = z3.Int('abundance_source_id')
        
        # Use Skolem functions instead of existential quantifiers
        return z3.ForAll(
            [source_world],
            z3.Implies(
                # If the source_world is a valid world
                self.is_world(source_world),
                # Then both:
                z3.And(
                    # Forwards condition - if source can shift forward
                    z3.Implies(
                        self.can_shift_forward(source_world),
                        z3.And(
                            # The forward_of function must produce a valid world
                            self.is_world(forward_of(source_world)),
                            # The produced world must be properly shifted
                            self.is_shifted_by(source_world, 1, forward_of(source_world))
                        )
                    ),
                    # Backwards condition - if source can shift backwards
                    z3.Implies(
                        self.can_shift_backward(source_world),
                        z3.And(
                            # The backward_of function must produce a valid world
                            self.is_world(backward_of(source_world)),
                            # The produced world must be properly shifted
                            self.is_shifted_by(source_world, -1, backward_of(source_world))
                        )
                    )
                )
            )
        )

    def build_task_minimization_constraint(self):
        """Build constraint encouraging minimal changes between consecutive world states.
        
        This constraint guides Z3 to prefer solutions where consecutive world states
        are identical when possible, reducing unnecessary state changes and potentially
        reducing the search space.
        
        Returns:
            Z3 formula: Constraint encouraging minimal state changes
        """
        world_id = z3.Int('minimal_world')
        time_point = z3.Int('minimal_time')
        
        return z3.ForAll(
            [world_id, time_point],
            z3.Implies(
                z3.And(
                    self.is_world(world_id),
                    self.is_valid_time_for_world(world_id, time_point),
                    self.is_valid_time_for_world(world_id, time_point + 1)
                ),
                # Encourage identical states if possible (soft constraint)
                z3.Select(self.world_function(world_id), time_point) == 
                z3.Select(self.world_function(world_id), time_point + 1)
            )
        )
    
    def define_invalidity(self):
        """Define the behavior for premises and conclusions in invalidity checks.

        This method sets up two lambda functions that specify how premises and conclusions 
        should be evaluated when checking for invalidity:

        - premise_behavior: Evaluates whether a premise is true at the main world and time
        - conclusion_behavior: Evaluates whether a conclusion is false at the main world and time

        These behaviors are used to find counterexamples that demonstrate invalidity of arguments
        by showing a case where all premises are true but the conclusion is false.
        """
        # Use world ID directly instead of the world array
        premise_behavior = lambda premise: self.true_at(premise, self.main_world, self.main_time)
        conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_world, self.main_time)
        return premise_behavior, conclusion_behavior
        
    def verify_model(self, z3_model, premises, conclusions):
        """Verify that premises are true and conclusions are false in the found model.
        
        This method checks whether the model generated by Z3 correctly satisfies the 
        constraints for invalidating an argument - i.e., that all premises are true and
        all conclusions are false at the main evaluation point.
        
        Args:
            z3_model: The Z3 model to verify
            premises: List of premise formulas
            conclusions: List of conclusion formulas
            
        Returns:
            dict: Verification results dictionary with information about whether
                  premises are true and conclusions are false in the model
        """
        verification_results = {
            "premises_verified": True,
            "conclusions_verified": True,
            "errors": []
        }
        
        # Check that all premises are true at the main point
        for premise in premises:
            try:
                premise_expr = self.true_at(premise, self.main_world, self.main_time)
                result = z3_model.eval(premise_expr)
                if not z3.is_true(result):
                    verification_results["premises_verified"] = False
                    verification_results["errors"].append(f"Premise {premise} is not true at main evaluation point")
            except z3.Z3Exception as e:
                verification_results["errors"].append(f"Error evaluating premise {premise}: {e}")
        
        # Check that all conclusions are false at the main point
        for conclusion in conclusions:
            try:
                conclusion_expr = self.false_at(conclusion, self.main_world, self.main_time)
                result = z3_model.eval(conclusion_expr)
                if not z3.is_true(result):
                    verification_results["conclusions_verified"] = False
                    verification_results["errors"].append(f"Conclusion {conclusion} is not false at main evaluation point")
            except z3.Z3Exception as e:
                verification_results["errors"].append(f"Error evaluating conclusion {conclusion}: {e}")
        
        return verification_results

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

    def generate_time_intervals(self, M):
        """Generate all valid time intervals of length M that include time 0.
        
        Args:
            M (int): The length of each interval
            
        Returns:
            list: List of (start_time, end_time) tuples representing intervals
        """
        intervals = []
        for start in range(-M+1, 1):  # Start points from M+1 to 0
            end = start + M - 1       # Each interval has exactly M time points
            intervals.append((start, end))
        return intervals
        
    def is_time_shifted(self, source_world_id, shift_amount, target_world_id):
        """Determines if target_world_id is a time-shifted version of source_world_id by shift_amount.
        
        Args:
            source_world_id: The ID of the source world
            shift_amount: The amount to shift by
            target_world_id: The ID of the target world
            
        Returns:
            Z3 formula that is true if target is a time-shifted version of source
        """
        return self.is_shifted_by(source_world_id, shift_amount, target_world_id)

    def extract_model_elements(self, z3_model):
        """Extract all model elements from a found model with improved organization.
        
        This method extracts world IDs, their arrays, time intervals, and time-shift relations
        from a satisfiable Z3 model.
        
        Args:
            z3_model: The Z3 model to extract elements from
            
        Returns:
            Tuple containing:
            1. Dictionary mapping world_ids to their time-state mappings
               {world_id (int): {time: bitvector_state}}
            2. Dictionary containing main world mapping {time: bitvector_state}
            3. Dictionary mapping world_ids to their world arrays
               {world_id (int): world_array}
            4. Dictionary mapping world_ids to their time-shift relations
               {source_id: {shift: target_id}}
        """
        # First identify all valid world IDs
        all_worlds = self._extract_valid_world_ids(z3_model)
        
        # Extract world arrays for each valid world ID
        world_arrays = self._extract_world_arrays(z3_model, all_worlds)
        
        # Extract time intervals for each world
        world_time_intervals = self._extract_time_intervals(z3_model, all_worlds)
        
        # Extract time-state mappings for each world ID
        world_histories = self._extract_world_histories(z3_model, all_worlds, world_arrays, world_time_intervals)
        
        # Check if we have any valid world histories
        if not world_histories:
            # Create empty dictionaries for a consistent interface
            world_histories = {}
            world_arrays = {}
            time_shift_relations = {}
            # Return empty structures
            return world_histories, {}, world_arrays, {}
        
        # Extract time shift relations between worlds
        time_shift_relations = self._extract_time_shift_relations(z3_model, all_worlds, world_histories)
        
        # Identify main world history
        main_world_history = world_histories.get(self.main_world, {})
        
        return world_histories, main_world_history, world_arrays, time_shift_relations
        
    def _extract_valid_world_ids(self, z3_model):
        """Identifies all valid world IDs in the model.
        
        Args:
            z3_model: The Z3 model to extract from
            
        Returns:
            list: List of valid world IDs
        """
        all_worlds = []
        # Check each potential world_id to see if it corresponds to a valid world history
        for i in range(self.max_world_id):
            try:
                # Get is_world expression
                is_world_expr = self.is_world(i)
                
                # Check if this world_id maps to a valid world history
                is_valid_expr = z3_model.eval(is_world_expr)
                is_valid = z3.is_true(is_valid_expr)
                
                if is_valid:
                    all_worlds.append(i)
            except z3.Z3Exception:
                continue
        
        # Ensure main world (ID 0) is included
        if 0 not in all_worlds:
            all_worlds.append(0)
            
        return all_worlds
    
    def _extract_world_arrays(self, z3_model, all_worlds):
        """Gets arrays for each world ID.
        
        Extracts the array representation for each valid world in the model,
        handling both ArrayRef and QuantifierRef (Lambda) representations.
        
        Args:
            z3_model: The Z3 model to extract from
            worlds: List of valid world IDs
            
        Returns:
            dict: Mapping from world_id to world array
        """
        world_arrays = {}
        
        for world_id in all_worlds:
            try:
                # Extract this valid world history array
                world_array_expr = self.world_function(world_id)
                
                # Evaluate the expression in the model
                world_array = z3_model.eval(world_array_expr)
                
                # Store the array regardless of its representation type
                world_arrays[world_id] = world_array

            # TODO: add print to test
            except z3.Z3Exception:
                # Skip worlds that can't be extracted
                pass
                
        return world_arrays
    
    def _extract_time_intervals(self, z3_model, all_worlds):
        """Extracts valid time intervals for each world.
        
        Args:
            z3_model: The Z3 model to extract from
            worlds: List of valid world IDs
            
        Returns:
            dict: Mapping from world_id to (start_time, end_time) tuple
        """
        # Reset time intervals dictionary
        self.world_time_intervals = {}
        
        for world_id in all_worlds:
            try:
                start_time = z3_model.eval(self.world_interval_start(world_id)).as_long()
                end_time = z3_model.eval(self.world_interval_end(world_id)).as_long()
                self.world_time_intervals[world_id] = (start_time, end_time)
            except z3.Z3Exception:
                # Use default interval if extraction fails
                start_time = -self.M + 1
                end_time = self.M - 1
                self.world_time_intervals[world_id] = (start_time, end_time)
        
        return self.world_time_intervals
    
    # TODO: refactor to make fail-fast
    def safe_select(self, z3_model, world_array, time):
        """Safely select from a world array, handling both ArrayRef and QuantifierRef.
        
        This function allows array access regardless of Z3's internal representation choice
        between concrete arrays (ArrayRef) and Lambda functions (QuantifierRef).
        
        Args:
            z3_model: The Z3 model
            world_array: Either an ArrayRef or QuantifierRef (Lambda)
            time: The time point to select (int or Z3 ArithRef)
            
        Returns:
            The value at the specified time point
            
        Raises:
            TypeError: If world_array is not a valid array type or time is not a valid Z3 integer
            z3.Z3Exception: If evaluation fails
        """
        # Handle time parameter to ensure it's a Z3 integer
        if isinstance(time, int):
            # Simple Python int
            time_val = z3.IntVal(time)
        elif isinstance(time, z3.ArithRef) and time.sort() == z3.IntSort():
            # Already a Z3 Int, use directly
            time_val = time
        elif hasattr(time, 'as_long'):
            # Z3 value with numerical representation, convert to Z3 Int
            # TODO: linter error
            time_val = z3.IntVal(time.as_long())  # type: ignore
        else:
            # Cannot use this time value
            raise TypeError(f"Time parameter must be an integer or Z3 Int, got {type(time)}: {time}")
            
        # Handle different array types
        if isinstance(world_array, z3.ArrayRef):
            # Standard array select
            select_expr = z3.Select(world_array, time_val)
            return z3_model.eval(select_expr)
        elif isinstance(world_array, z3.QuantifierRef):
            # Handle Lambda expression
            if world_array.num_vars() != 1:
                raise TypeError(f"Expected Lambda with 1 variable, got {world_array.num_vars()}")
                
            # Create proper Z3 substitution
            select_expr = z3.substitute(world_array.body(), 
                                      (z3.Var(0, self.TimeSort), time_val))
            return z3_model.eval(select_expr)
        else:
            raise TypeError(f"Cannot select from world array of type {type(world_array)}")

    def _extract_world_histories(self, z3_model, worlds, world_arrays, world_time_intervals):
        """Creates histories (time-state mappings) for each world.
        
        Extracts the state of each world at each time point within its valid interval
        using the safe_select function to handle different array representations.
        
        Args:
            z3_model: The Z3 model to extract from
            worlds: List of valid world IDs
            world_arrays: Dictionary of world arrays
            world_time_intervals: Dictionary of time intervals
            
        Returns:
            dict: Mapping from world_id to time-state mapping
        """
        world_histories = {}
        
        for world_id in worlds:
            # Skip worlds with missing data
            if world_id not in world_arrays or world_id not in world_time_intervals:
                continue
                
            # Get the world array and time interval
            world_array = world_arrays[world_id]
            start_time, end_time = world_time_intervals[world_id]
            
            # Extract states for each time point
            time_states = {}
            
            for time in range(start_time, end_time + 1):
                try:
                    # Create Z3 IntVal for time to ensure proper typing
                    time_val = z3.IntVal(time)
                    state = self.safe_select(z3_model, world_array, time_val)
                    
                    # Convert to state representation using the new alphabetic labeling
                    if hasattr(state, 'sort') and str(state.sort()).startswith('BitVec'):
                        # Use bitvec_to_worldstate instead of bitvec_to_substates
                        state_val = bitvec_to_worldstate(state)
                        time_states[time] = state_val
                    else:
                        # Non-BitVec result
                        time_states[time] = f"<{state}>"
                except (TypeError, z3.Z3Exception) as e:
                    # Try direct Z3 evaluation as a last resort
                    try:
                        if isinstance(world_array, z3.ArrayRef):
                            time_val = z3.IntVal(time)
                            select_expr = z3.Select(world_array, time_val)
                            state = z3_model.eval(select_expr)
                            # Use bitvec_to_worldstate instead of bitvec_to_substates
                            state_val = bitvec_to_worldstate(state)
                            time_states[time] = state_val
                        else:
                            # No recovery possible
                            time_states[time] = f"<error:{str(e)}>"
                    except Exception:
                        # Final fallback - store error
                        time_states[time] = f"<error:{str(e)}>"
            
            # Add history to output
            world_histories[world_id] = time_states
        
        return world_histories
    
    def _extract_time_shift_relations(self, z3_model, worlds, world_histories):
        """Builds shift relations between worlds.
        
        Args:
            z3_model: The Z3 model to extract from
            worlds: List of valid world IDs
            world_histories: Dictionary of time-state mappings
            
        Returns:
            dict: Nested dictionary mapping source_id to {shift: target_id}
        """
        time_shift_relations = {}
        
        for source_id in worlds:
            time_shift_relations[source_id] = {}
            
            # Add self-shift (shift by 0)
            time_shift_relations[source_id][0] = source_id
            
            # Skip if world isn't in histories
            if source_id not in world_histories:
                continue
                
            # Check essential shifts (+1, -1)
            for shift in [1, -1]:
                for target_id in worlds:
                    if source_id != target_id and target_id in world_histories:  # Skip self and invalid targets
                        try:
                            # First check interval compatibility
                            source_start, source_end = self.world_time_intervals[source_id]
                            target_start, target_end = self.world_time_intervals[target_id]
                            
                            # For positive shift, target interval should be shifted up by 1
                            if shift == 1 and target_start == source_start + 1 and target_end == source_end + 1:
                                # Check if states match when shifted
                                is_shifted = True
                                for time in range(source_start, source_end + 1):
                                    if time + shift <= target_end:
                                        source_state = world_histories[source_id].get(time)
                                        target_state = world_histories[target_id].get(time + shift)
                                        if source_state is not None and target_state is not None and source_state != target_state:
                                            is_shifted = False
                                            break
                                
                                if is_shifted:
                                    time_shift_relations[source_id][shift] = target_id
                                    break
                            
                            # For negative shift, target interval should be shifted down by 1
                            elif shift == -1 and target_start == source_start - 1 and target_end == source_end - 1:
                                # Check if states match when shifted
                                is_shifted = True
                                for time in range(source_start, source_end + 1):
                                    if time + shift >= target_start:
                                        source_state = world_histories[source_id].get(time)
                                        target_state = world_histories[target_id].get(time + shift)
                                        if source_state is not None and target_state is not None and source_state != target_state:
                                            is_shifted = False
                                            break
                                
                                if is_shifted:
                                    time_shift_relations[source_id][shift] = target_id
                                    break
                        except Exception as e:
                            print(f"Warning: Error checking time-shift relation for worlds {source_id}->{target_id}: {e}")
        
        if not world_histories:
            print("Warning: No valid world histories found in the model!")
            
        return time_shift_relations


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
        
        # Extract world states sets for use in representation
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
            # If it's already a string representation, use it directly
            if isinstance(world_state, str) and not world_state.startswith('<unknown-'):
                truth_worlds.add(world_state)
            # If it's a Z3 BitVec
            elif hasattr(world_state, 'as_ast'):
                evaluated_bit = z3_model.evaluate(world_state)
                truth_worlds.add(bitvec_to_worldstate(evaluated_bit))
            # If it's any other type
            else:
                try:
                    # Try to convert it to a world state
                    if hasattr(world_state, 'as_long') or isinstance(world_state, int):
                        truth_worlds.add(bitvec_to_worldstate(world_state))
                    else:
                        # Fall back to using the string representation
                        truth_worlds.add(str(world_state))
                except Exception:
                    # If all else fails, use the string representation
                    truth_worlds.add(str(world_state))
                
        # Handle false set
        false_worlds = set()
        for world_state in self.false_set:
            # If it's already a string representation, use it directly
            if isinstance(world_state, str) and not world_state.startswith('<unknown-'):
                false_worlds.add(world_state)
            # If it's a Z3 BitVec
            elif hasattr(world_state, 'as_ast'):
                evaluated_bit = z3_model.evaluate(world_state)
                false_worlds.add(bitvec_to_worldstate(evaluated_bit))
            # If it's any other type
            else:
                try:
                    # Try to convert it to a world state
                    if hasattr(world_state, 'as_long') or isinstance(world_state, int):
                        false_worlds.add(bitvec_to_worldstate(world_state))
                    else:
                        # Fall back to using the string representation
                        false_worlds.add(str(world_state))
                except Exception:
                    # If all else fails, use the string representation
                    false_worlds.add(str(world_state))
                
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
            true_contingent_state = z3.BitVec("true_contingent_state", semantics.N)
            false_contingent_state = z3.BitVec("false_contingent_state", semantics.N)
            possibly_true = Exists(
                [true_contingent_state],
                semantics.truth_condition(true_contingent_state, sentence_letter)
            )
            possibly_false = Exists(
                [false_contingent_state],
                z3.Not(semantics.truth_condition(false_contingent_state, sentence_letter))
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
                        z3.Or(
                            z3.Not(semantics.truth_condition(disjoint_state, sentence_letter)),
                            z3.Not(semantics.truth_condition(disjoint_state, other_letter))
                        )
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
                        self.sentence, world_id, time
                    )
                    evaluated_expr = self.z3_model.evaluate(truth_expr)
                    if z3.is_true(evaluated_expr):
                        true_times.append(time)
                    else:
                        false_times.append(time)
                
                # Store the extension for this world_id
                extension[world_id] = (true_times, false_times)
                
            return extension
            
        elif self.operator is not None:
            # For complex sentences, delegate to the operator's find_truth_condition method
            # Consistently use world ID
            return self.operator.find_truth_condition(*arguments, self.eval_world, self.eval_time)
            
        raise ValueError(f"There is no proposition for {self}.")

    def extract_world_states(self) -> tuple[set, set]:
        """Extract sets of world states where the proposition is true and false.
        
        Processes the proposition's temporal profiles for each world to determine
        the set of world states where the proposition is true and where it is false.
        
        Returns:
            tuple[set, set]: A pair of sets containing:
                - First set: World states where the proposition is true
                - Second set: World states where the proposition is false
                
        Raises:
            KeyError: If a required world ID is missing
            ValueError: If world state extraction fails in a way that breaks the model
        """
        # Extract states where proposition is true
        truth_states = set()
        false_states = set()
        
        for world_id, (true_times, false_times) in self.extension.items():
            # Get the world array for this world ID - fail if not found
            if world_id not in self.model_structure.world_arrays:
                raise KeyError(f"World {world_id} not in world_arrays, but required for proposition {self.name}")
                
            world_array = self.model_structure.world_arrays[world_id]
            
            # Prefer world histories when available
            if world_id in self.model_structure.world_histories:
                world_history = self.model_structure.world_histories[world_id]
                
                # Process true times
                for time in true_times:
                    if time not in world_history:
                        # Skip times that aren't in the world history instead of raising an error
                        # This handles cases where time intervals don't perfectly match
                        continue
                        
                    state = world_history[time]
                    # Add the state to the truth set
                    if isinstance(state, str):
                        truth_states.add(state)
                    else:
                        # Convert to string representation if needed
                        state_str = str(state)
                        truth_states.add(state_str)
                
                # Process false times
                for time in false_times:
                    if time not in world_history:
                        # Skip times that aren't in the world history instead of raising an error
                        continue
                        
                    state = world_history[time]
                    # Add the state to the false set
                    if isinstance(state, str):
                        false_states.add(state)
                    else:
                        # Convert to string representation if needed
                        state_str = str(state)
                        false_states.add(state_str)
            else:
                # Direct array access using safe_select
                
                # Process true times
                for time in true_times:
                    try:
                        # Use safe_select with direct time value - it handles type conversion
                        state = self.model_structure.semantics.safe_select(
                            self.z3_model, world_array, time)
                        state_val = bitvec_to_worldstate(state)
                        truth_states.add(state_val)
                    except (TypeError, z3.Z3Exception) as e:
                        error_msg = f"Failed to extract state at world {world_id}, time {time}: {e}"
                        raise ValueError(error_msg) from e
                
                # Process false times
                for time in false_times:
                    try:
                        # Use safe_select with direct time value - it handles type conversion
                        state = self.model_structure.semantics.safe_select(
                            self.z3_model, world_array, time)
                        state_val = bitvec_to_worldstate(state)
                        false_states.add(state_val)
                    except (TypeError, z3.Z3Exception) as e:
                        error_msg = f"Failed to extract state at world {world_id}, time {time}: {e}"
                        raise ValueError(error_msg) from e
                
        return truth_states, false_states

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
            print(f"WARNING: No extension available for proposition {self} at world {eval_world}")
            return False
            
        # Check if the requested world_id exists in the extension
        if eval_world not in self.extension:
            print(f"WARNING: World ID {eval_world} not found in extension for {self}")
            # Return a default value when the world doesn't exist in the extension
            return False
            
        # Get the truth/falsity data for this world_id
        true_times, false_times = self.extension[eval_world]
        
        true_in_eval_world = eval_time in true_times
        false_in_eval_world = eval_time in false_times
        
        if true_in_eval_world and false_in_eval_world:
            # Both true and false (shouldn't happen in a well-formed model)
            try:
                world_array = self.model_structure.get_world_array(eval_world)
                eval_state = self.z3_model.evaluate(world_array[eval_time])
                print(
                    f"WARNING: the world_id {eval_world} at time {eval_time} "
                    f"makes {self} both true and false at the world_state {eval_state}."
                )
            except Exception as e:
                print(f"WARNING: Error accessing world state: {e}")
                
        return true_in_eval_world

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


class BimodalStructure(ModelDefaults):
    """Represents the model structure for a bimodal logic system.
    
    This class extends ModelDefaults to handle the specific structures needed
    for bimodal logic, including world arrays that map times to world states.
    It extracts world histories from the Z3 model and maintains consistent
    world array references for evaluation using world_ids as primary keys.
    
    Attributes:
        main_world (int): The world_id of the main world for evaluation
        main_time (int): The main time point for evaluation
        M (int): Number of time points
        all_times (range): Range of available time points
        world_arrays (dict): Maps world_id (int) to world array (Z3 object)
        world_histories (dict): Maps world_id (int) to {time: world_state} mappings
    """
    def __init__(self, model_constraints, max_time=1):
        """Initialize a BimodalStructure with model constraints.
        
        Args:
            model_constraints (ModelConstraints): Constraints for model generation
            max_time (int): Maximum solving time in seconds
        """
        # Initialize parent class first
        super().__init__(model_constraints, max_time)

        # Initialize temporal and world attributes
        self.M = self.semantics.M
        # Update time range to be centered around 0: [-M+1, M-1]
        self.all_times = range(-self.M + 1, self.M)
        
        # Initialize world_id based dictionaries
        self.world_arrays = {}  # Maps world_id (int) to world array (Z3 object)
        self.world_histories = {}  # Maps world_id (int) to {time: world_state} mappings
        self.time_shift_relations = {}  # Maps source_id to {shift: target_id}
        self.main_world = 0  # Default main world_id
        
        # Initialize Z3 model values
        self.z3_main_time = None
        self.z3_main_world_state = None
        # Initialize main_time with a default value (0) to avoid AttributeError
        self.main_time = 0

        # Only evaluate if we have a valid model
        if self.z3_model_status and self.z3_model is not None:
            # Give semantics a reference to this model structure for helper methods
            self.semantics.model_structure = self
            
            # Extract all world histories, arrays, and time-shift relations from the model
            self.world_histories, self.main_world_history, self.world_arrays, self.time_shift_relations = (
                self.semantics.extract_model_elements(self.z3_model)
            )
            
            # Get the main time and world
            self.z3_main_time = self.z3_model.evaluate(self.main_point["time"])
            
            # Convert Z3 time to Python int for easier handling in other places
            if hasattr(self.z3_main_time, 'as_long'):
                self.main_time = self.z3_main_time.as_long()
            else:
                # If not convertible, keep the Z3 value
                self.main_time = self.z3_main_time
            
            # Update the main point to use consistent keys with world as ID
            self.main_point = {
                "time": self.main_time,
                "world": self.main_world  # Use world_id (integer)
            }
            
            # Get the main world state if available
            if self.main_world in self.world_arrays:
                # Evaluate the world state of the main world at the main time
                main_world_array = self.world_arrays[self.main_world]
                
                try:
                    # Use the original Z3 time value directly - not the converted int
                    self.z3_main_world_state = self.semantics.safe_select(
                        self.z3_model, 
                        main_world_array,
                        self.z3_main_time  # Use original Z3 time value
                    )
                except (TypeError, z3.Z3Exception) as e:
                    # Fail with a clear error message
                    error_msg = (f"Failed to extract main world state at time {self.main_time}. "
                              f"This indicates a fundamental model access issue: {str(e)}")
                    raise ValueError(error_msg) from e
            else:
                # TODO: make fail-fast with error report
                # Set a placeholder value
                self.z3_main_world_state = None
            
            # Initialize the all_true and all_false dictionaries in the semantics
            # These provide truth values for extremal operators (Top/Bot)
            self.semantics.all_true = {}
            self.semantics.all_false = {}
            
            for world_id in self.world_arrays:
                self.semantics.all_true[world_id] = (list(self.all_times), [])
                self.semantics.all_false[world_id] = ([], list(self.all_times))
    
    def get_world_array(self, world_id):
        """Get the world array for a given world_id.
        
        Args:
            world_id (int): The world identifier
            
        Returns:
            Z3 Array: The world array mapping times to world states
            
        Raises:
            KeyError: If the world_id doesn't exist in world_arrays
        """
        # Direct dictionary access - will raise KeyError if the world_id doesn't exist
        return self.world_arrays[world_id]
    
    def get_world_history(self, world_id):
        """Get the time-to-state mapping for a given world_id.
        
        Args:
            world_id (int): The world identifier (integer)
            
        Returns:
            dict: Mapping from time points to world states
            
        Raises:
            KeyError: If the world_id doesn't exist in world_histories
            TypeError: If world_id is not an integer
        """
        if not isinstance(world_id, int):
            raise TypeError(f"world_id must be an integer, not {type(world_id)}")
            
        # Direct dictionary access - will raise KeyError if the world_id doesn't exist
        return self.world_histories[world_id]
    
    def get_world_state_at(self, world_id, time):
        """Get the world state at a specific time in a specific world.
        
        Args:
            world_id (int): The world identifier (integer)
            time (int): The time point
            
        Returns:
            Z3 BitVec: The world state at the specified time
            
        Raises:
            KeyError: If the world_id doesn't exist in world_histories
            KeyError: If the time doesn't exist in the history for world_id
            TypeError: If world_id is not an integer
        """
        history = self.get_world_history(world_id)
        return history[time]

    def print_evaluation(self, output=sys.__stdout__):
        """Print the evaluation world and time information.
        
        Displays the main world timeline, current evaluation time, and 
        the current world state at that time.
        
        Args:
            output: Output stream to print to. Defaults to sys.stdout.
        """
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

        # Get the main world history for display
        main_world_history = self.world_histories[self.main_world]

        # Create the sequence of states connected by arrows
        state_sequence = []
        for time in sorted(main_world_history.keys()):
            state_sequence.append(str(main_world_history[time]))
        
        # Join states with arrows and print
        world_line = " =⟹ ".join(state_sequence)

        # Get evaluation time and state
        eval_time = self.main_time
        eval_world_state = self.z3_main_world_state
        
        print(
            f"\nEvaluation Point:\n"
            + f"  {BLUE}World History W_{self.main_world}: {world_line}{RESET}\n"
            + f"  {BLUE}Time: {eval_time}{RESET}\n"
            + f"  {BLUE}World State: {bitvec_to_worldstate(eval_world_state)}{RESET}\n",
            file=output,
        )

    def format_time(self, time):
        """Format time with appropriate sign for display.
        
        Args:
            time: Time point to format
            
        Returns:
            str: Formatted time string with sign prefix
        """
        if time > 0:
            return f"+{time}"  # Add + prefix for positive non-zero times
        return f"{time}"  # Negative times already have - prefix, zero is just 0
    
    def _get_time_range(self, world_histories):
        """Get the minimum and maximum time points across all world histories.
        
        Args:
            world_histories: Dictionary mapping world_ids to time-state mappings
            
        Returns:
            tuple: (min_time, max_time)
        """
        min_time = float('inf')
        max_time = float('-inf')
        for world_id, time_states in world_histories.items():
            for time in time_states:
                min_time = min(min_time, time)
                max_time = max(max_time, time)
        return min_time, max_time
    
    def _create_formatted_states(self, world_histories, all_times):
        """Format states for each world at each time.
        
        Args:
            world_histories: Dictionary mapping world_ids to time-state mappings
            all_times: List of all time points to consider
            
        Returns:
            dict: Dictionary mapping world_ids to dictionaries mapping times to formatted state strings
        """
        formatted_states = {}
        for world_id, time_states in world_histories.items():
            formatted_states[world_id] = {}
            for time in all_times:
                if time in time_states:
                    # Format time with appropriate sign
                    formatted_time = self.format_time(time)
                    # Create formatted state string
                    formatted_states[world_id][time] = f"({formatted_time}:{time_states[time]})"
        return formatted_states
    
    def _calculate_column_widths(self, all_times, formatted_states):
        """Calculate the maximum width needed for each time column.
        
        Args:
            all_times: List of all time points to consider
            formatted_states: Dictionary mapping world_ids to dictionaries mapping times to formatted state strings
            
        Returns:
            dict: Dictionary mapping time points to column widths
        """
        column_widths = {}
        for time in all_times:
            max_width = 0
            for world_id in formatted_states:
                if time in formatted_states[world_id]:
                    max_width = max(max_width, len(formatted_states[world_id][time]))
            column_widths[time] = max_width
        return column_widths
    
    def _create_time_positions(self, all_times, column_widths):
        """Calculate starting position for each time column.
        
        Args:
            all_times: List of all time points to consider
            column_widths: Dictionary mapping time points to column widths
            
        Returns:
            dict: Dictionary mapping time points to their starting positions
        """
        time_positions = {}
        current_pos = 0
        for time in all_times:
            time_positions[time] = current_pos
            current_pos += column_widths[time] + 4  # Width + space for " ==> "
        return time_positions
    
    def _create_world_line(self, world_id, all_times, formatted_states, time_positions, column_widths):
        """Create a formatted line for a world history with proper alignment.
        
        Args:
            world_id: The world ID to create a line for
            all_times: List of all time points to consider
            formatted_states: Dictionary mapping world_ids to dictionaries mapping times to formatted state strings
            time_positions: Dictionary mapping time points to their starting positions
            column_widths: Dictionary mapping time points to column widths
            
        Returns:
            str: Formatted world line with properly aligned states
        """
        # Initialize the line with spaces
        total_width = max(time_positions.values()) + column_widths.get(all_times[-1], 0)
        line = [" "] * total_width
        
        # Add each visible state at its appropriate position
        visible_times = sorted([t for t in all_times if t in formatted_states[world_id]])
        
        for i, time in enumerate(visible_times):
            state_str = formatted_states[world_id][time]
            pos = time_positions[time]
            
            # Add the state
            for j, char in enumerate(state_str):
                if pos + j < len(line):
                    line[pos + j] = char
            
            # Add arrow if not the last state
            if i < len(visible_times) - 1:
                arrow_pos = pos + len(state_str)
                arrow = " =⟹ "
                for j, char in enumerate(arrow):
                    if arrow_pos + j < len(line):
                        line[arrow_pos + j] = char
        
        # Convert to string and remove trailing whitespace
        return "".join(line).rstrip()
        
    def print_world_histories(self, output=sys.__stdout__):
        """Print all world histories with time-aligned columns.
        
        This method prints world histories in a format where states at the same
        time points are vertically aligned, making it easier to compare states
        across different world histories.
        
        Args:
            output: Output stream to print to. Defaults to sys.stdout.
        """
        print("World Histories:", file=output)
        if self.z3_model is None or not hasattr(self, 'world_histories') or self.world_histories is None:
            print("No valid world histories available", file=output)
            return

        # Set up colors
        GRAY = ""
        RESET = ""
        if output is sys.__stdout__:
            GRAY = "\033[37m"
            RESET = "\033[0m"
        
        # 1. Determine the full time range
        min_time, max_time = self._get_time_range(self.world_histories)
        
        # 2. Create a list of all times in ascending order
        all_times = sorted(range(int(min_time), int(max_time) + 1))
        
        # 3. Format states for each world at each time
        formatted_states = self._create_formatted_states(self.world_histories, all_times)
        
        # 4. Determine column width for each time
        column_widths = self._calculate_column_widths(all_times, formatted_states)
        
        # 5. Calculate starting position for each time column
        time_positions = self._create_time_positions(all_times, column_widths)
        
        # 6. Print each world history with aligned columns
        for world_id in sorted(self.world_histories.keys()):
            # Create the world line with proper alignment
            world_line = self._create_world_line(
                world_id, all_times, formatted_states, time_positions, column_widths
            )
            
            # Print the formatted world line
            print(f"  {GRAY}W_{world_id}: {world_line}{RESET}", file=output)
        
    def _calculate_world_column_widths(self, world_ids, formatted_states, all_times):
        """Calculate the maximum width needed for each world's column.
        
        Args:
            world_ids: List of world IDs
            formatted_states: Dictionary mapping world_ids to dictionaries mapping times to formatted state strings
            all_times: List of all time points to consider
            
        Returns:
            dict: Dictionary mapping world_ids to column widths
        """
        world_column_widths = {}
        for world_id in world_ids:
            max_width = 0
            for time in all_times:
                if time in formatted_states.get(world_id, {}):
                    max_width = max(max_width, len(formatted_states[world_id][time]))
            world_column_widths[world_id] = max_width
        return world_column_widths
        
    def print_world_histories_vertical(self, output=sys.__stdout__):
        """Print world histories with time flowing vertically (top to bottom).
        
        This method arranges world histories in columns with time flowing from top 
        (earlier) to bottom (later), making it easier to visualize temporal evolution.
        
        Args:
            output: Output stream to print to. Defaults to sys.stdout.
        """
        print("World Histories:", file=output)
        if self.z3_model is None or not hasattr(self, 'world_histories') or self.world_histories is None:
            print("No valid world histories available", file=output)
            return

        # Set up colors
        GRAY = ""
        HIGHLIGHT = ""
        RESET = ""
        if output is sys.__stdout__:
            GRAY = "\033[37m"
            HIGHLIGHT = "\033[1;33m"  # Bold yellow for time 0
            RESET = "\033[0m"
        
        # Find time range and world IDs
        min_time, max_time = self._get_time_range(self.world_histories)
        all_times = sorted(range(int(min_time), int(max_time) + 1))
        world_ids = sorted(self.world_histories.keys())
        
        # Create formatted states and determine column widths
        formatted_states = self._create_formatted_states(self.world_histories, all_times)
        
        # Calculate maximum width needed for each world column
        column_widths = {}
        for world_id in world_ids:
            max_width = 0
            for time in all_times:
                if time in formatted_states.get(world_id, {}):
                    state_width = len(formatted_states[world_id][time])
                    max_width = max(max_width, state_width)
            column_widths[world_id] = max_width
        
        # Fixed width for the Time column (reduced for compactness)
        time_col_width = 6  # Reduced from 10
        
        # Calculate positions for each column separator to ensure alignment
        separator_positions = [time_col_width]  # Start after the time column
        for world_id in world_ids[:-1]:  # No separator needed after the last column
            separator_positions.append(
                separator_positions[-1] + column_widths[world_id] + 3  # +3 for " | "
            )
        
        # Create the header row
        header = "Time".ljust(time_col_width)
        for i, world_id in enumerate(world_ids):
            # Add separator if not the first column
            header += " | "
            # Add world ID with proper padding
            header += f"W_{world_id}".ljust(column_widths[world_id])
        
        print(f"  {GRAY}{header}{RESET}", file=output)
        
        # Create a separator line matching the header length with pipe characters
        separator_parts = ["=" * time_col_width]
        for world_id in world_ids:
            separator_parts.append("=|=" + "=" * column_widths[world_id])
            
        separator = "".join(separator_parts)
        print(f"  {GRAY}{separator}{RESET}", file=output)
        
        # Print each time row
        for time in all_times:
            # Format time with appropriate sign
            formatted_time = self.format_time(time)
            
            # Use highlighting for time 0
            time_prefix = HIGHLIGHT if time == 0 else GRAY
            
            # Start the row with the time column
            row_parts = [f"{formatted_time.ljust(time_col_width)}"]
            
            # Add each world's state at this time
            for world_id in world_ids:
                if time in formatted_states.get(world_id, {}):
                    # Get the state and pad it to match the column width
                    state = formatted_states[world_id][time]
                    padded_state = state.ljust(column_widths[world_id])
                else:
                    # Empty placeholder for missing state
                    padded_state = "".ljust(column_widths[world_id])
                
                # Add the separator and the padded state
                row_parts.append(" | " + padded_state)
            
            # Combine all parts and print
            row = "".join(row_parts)
            print(f"  {time_prefix}{row}{RESET}", file=output)
            
            # Add arrow between rows (except after the last time)
            if time < max_time:
                arrow_parts = [" " * time_col_width]  # Space for time column using updated width
                
                for i, world_id in enumerate(world_ids):
                    # Calculate position for the arrow in this column
                    arrow_position = (column_widths[world_id] - 1) // 2
                    
                    # Only show arrow if this world has a state at this time AND the next time
                    if (time in formatted_states.get(world_id, {}) and 
                        time + 1 in formatted_states.get(world_id, {})):
                        # Create a string with pipe, spaces and an arrow at the calculated position
                        arrow_str = " | "  # Keep the pipe separator
                        arrow_str += " " * arrow_position + "↓" + " " * (column_widths[world_id] - arrow_position - 1)
                    else:
                        # Keep the pipe separator but no arrow
                        arrow_str = " | " + " " * column_widths[world_id]
                    
                    arrow_parts.append(arrow_str)
                
                arrow_row = "".join(arrow_parts)
                print(f"  {GRAY}{arrow_row}{RESET}", file=output)
    
    def print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__):
        """Print complete model information including worlds, evaluation point, and sentences.
        
        Args:
            default_settings: Default settings for the model
            example_name: Name of the example being evaluated
            theory_name: Name of the theory being used
            output: Output stream to print to. Defaults to sys.stdout.
        """
        model_status = self.z3_model_status
        self.print_info(model_status, self.settings, example_name, theory_name, output)
        if model_status:
            # Choose the appropriate history display format based on settings
            align_vertically = self.settings.get("align_vertically", False)
            if align_vertically:
                self.print_world_histories_vertical(output)
            else:
                self.print_world_histories(output)
                
            self.print_evaluation(output)
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4) 
                print(f"Total Run Time: {total_time} seconds\n", file=output)
                print(f"{'='*40}", file=output)
            return

    def print_to(self, default_settings, example_name, theory_name, print_constraints=None, output=sys.__stdout__):
        """Print all model elements to the provided output stream.
        
        Args:
            default_settings: Default settings for the model
            example_name: Name of the example being evaluated
            theory_name: Name of the theory being used
            print_constraints: Whether to print constraints. Defaults to value in settings.
            output: Output stream to print to. Defaults to sys.stdout.
        """
        if print_constraints is None:
            print_constraints = self.settings["print_constraints"]
            
        # Check if we actually timed out (runtime >= max_time)
        actual_timeout = hasattr(self, 'z3_model_runtime') and self.z3_model_runtime >= self.max_time
        
        # Only show timeout if we really timed out and didn't find a model
        if actual_timeout and (not hasattr(self, 'z3_model') or self.z3_model is None):
            print(f"\nTIMEOUT: Model search exceeded maximum time of {self.max_time} seconds", file=output)
            print(f"No model for example {example_name} found before timeout.", file=output)
            print(f"Try increasing max_time > {self.max_time}.\n", file=output)
        
        self.print_all(self.settings, example_name, theory_name, output)
        if print_constraints and self.unsat_core is not None:
            self.print_grouped_constraints(output)

    def save_to(self, example_name, theory_name, include_constraints, output):
        """Save all model elements to the provided output file.
        
        Args:
            example_name: Name of the example being evaluated
            theory_name: Name of the theory being used
            include_constraints: Whether to include constraints in the output
            output: Output file to save to
        """
        constraints = self.model_constraints.all_constraints
        self.print_all(example_name, theory_name, output)
        self.build_test_file(output)
        if include_constraints:
            print("# Satisfiable constraints", file=output)
            print(f"all_constraints = {constraints}", file=output)
