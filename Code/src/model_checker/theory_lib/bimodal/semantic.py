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
        'N' : 3,
        'contingent' : False,
        'disjoint' : False,
        'max_time' : 1,
        'expectation' : True,
    }

    def __init__(self, settings):

        # Initialize the superclass to set defaults
        super().__init__(settings)

        # Define the primitive sorts

        self.WorldStateSort = z3.BitVecSort(self.N)
        # Create a sort for world states using bitvectors such as <001101>
        # N determines how many distinct worlds we can represent

        self.TimeSort = z3.IntSort()
        # Create a sort for times using integers

        # # Define all evolutions from times to world states 
        # self.all_worlds = [
        #     z3.Array(f'world_function_{i}', self.TimeSort, self.WorldStateSort) 
        #     for i in range(len(self.all_bits) ** len(self.all_times))
        # ]

        ### Define the Z3 primitives ###

        self.task = z3.Function(
            "Task",
            self.WorldStateSort,
            self.WorldStateSort,
            z3.BoolSort()
        )  # Define a binary task relation between world states
        
        self.main_world = z3.Array('main_world', self.TimeSort, self.WorldStateSort)
        # Define an arbitrary world at which to evaluate sentences 

        self.main_time = z3.Int('main_time')
        # Define an arbitrary time at which to evaluate sentences 

        # Ensure main_time is within valid range
        time_constraints = z3.And(
            self.main_time >= 0,
            self.main_time < self.M
        )

        self.main_point = {
            "world": self.main_world,
            "time": self.main_time,
        }

        self.truth_condition = z3.Function(
            "truth_condition",
            self.WorldStateSort,
            syntactic.AtomSort,
            z3.BoolSort()
        )

        ### Define the frame constraints ###
        tau = z3.Array('frame_world_tau', self.TimeSort, self.WorldStateSort)
        x = z3.Int("frame_time_x")
        lawful = z3.ForAll(
            [tau, x],  # Pass variables as a list
            z3.Implies(
                z3.And(x >= 0, x < self.M - 1),
                self.task(tau[x], tau[x + 1])
            )
        )  # Require there to be a task from every world state to its successor

        # Define frame constraints
        self.frame_constraints = [
            lawful,
            time_constraints,
        ]

        # Store valid world-arrays after model is found
        self.valid_world_arrays = []

        # Define invalidity conditions
        # TODO: fix

        self.premise_behavior = lambda premise: self.true_at(premise, self.main_world, self.main_time)
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_world, self.main_time)

    def extract_model_worlds(self, z3_model):
        """Extract all world states from a found model.
        
        Args:
            z3_model: The Z3 model to extract worlds from
            
        Returns:
            Tuple containing:
            1. Dictionary mapping world arrays to their time-state mappings
               {world_array: {time: bitvector_state}}
            2. Dictionary containing main world mapping {time: bitvector_state}
            3. List of all unique world arrays found in the model

        Usage:
            # Get state of world_0 at time 1
            state = self.world_mappings[self.all_worlds[0]][1]

            # Get all states for world_0 
            world_0_states = self.world_mappings[self.all_worlds[0]]

            # Get all worlds' states at time 1
            time_1_states = [mapping[1] for mapping in self.world_mappings.values()]
        """
        main_world_mapping = {}
        world_mappings = {}
        all_worlds = {}
        seen_arrays = set()
        
        def get_array_signature(world_array):
            """Generate a unique signature for a world array based on its values"""
            signature = []
            for t in range(self.M):
                state = z3_model.eval(world_array[t])
                signature.append(str(state))
            return tuple(signature)
        
        # Find all unique world arrays in the model including quantified ones
        decls = z3_model.decls()
        world_count = 0
        for decl in decls:
            if z3.is_array(decl.range()):  # Check if it's an array declaration
                array = z3_model.get_interp(decl)
                if array is not None:
                    sig = get_array_signature(array)
                    if sig not in seen_arrays:
                        seen_arrays.add(sig)
                        key = f'world_function_{world_count:02d}'  # Zero-padded 2 digit number
                        all_worlds[key] = array
                        world_count += 1
        
        # Process main world separately
        if z3_model:
            main_world_array = z3_model.eval(self.main_world)
            for time in range(self.M):
                state = z3_model.eval(main_world_array[time])
                state_val = bitvec_to_substates(state, self.N)
                main_world_mapping[time] = state_val
            
            # Add main world to unique arrays if not already there
            main_sig = get_array_signature(main_world_array)
            if main_sig not in seen_arrays:
                seen_arrays.add(main_sig)
                key = f'world_function_{len(all_worlds):02d}'
                all_worlds[key] = main_world_array
        
        # Process all world arrays (including those found through quantifiers)
        for world_key, world_array in all_worlds.items():
            time_states = {}
            for time in range(self.M):
                state = z3_model.eval(world_array[time])
                state_val = bitvec_to_substates(state, self.N)
                time_states[time] = state_val
            world_mappings[world_key] = time_states
        
        return world_mappings, main_world_mapping, all_worlds

    def find_valid_world_arrays(self, max_time):
        """Find all world arrays that satisfy the frame constraints.
        
        Args:
            max_time: Maximum time point to consider
            
        Returns:
            List of valid world arrays, where each array maps time points to world states
        """
        # Create a new array to test possibilities
        test_array = z3.Array('test_world', self.TimeSort, self.WorldStateSort)
        
        # Get all possible world states from the model
        world_states = []
        for i in range(2**self.N):  # All possible bitvectors of length N
            world_states.append(z3.BitVecVal(i, self.N))
            
        def check_array_validity(assignments):
            """Check if a specific array assignment satisfies frame constraints"""
            # Create constraints for this specific assignment
            assignment_constraints = []
            for t, w in assignments.items():
                assignment_constraints.append(test_array[t] == w)
                
            # Check if this assignment satisfies frame constraints
            s = z3.Solver()
            s.add(self.frame_constraints)
            s.add(assignment_constraints)
            return s.check() == z3.sat
            
        # Generate all possible assignments recursively
        def generate_assignments(current_time=0, current_assignment={}):
            if current_time > max_time:
                if check_array_validity(current_assignment):
                    self.valid_world_arrays.append(current_assignment.copy())
                return
                
            for world in world_states:
                current_assignment[current_time] = world
                generate_assignments(current_time + 1, current_assignment)
                current_assignment.pop(current_time)
                
        generate_assignments()
        return self.valid_world_arrays

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
            eval_world_state = eval_world[eval_time]
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


class BimodalProposition(PropositionDefaults):
    """Defines the proposition assigned to the sentences of the language.
    all user has to keep for their own class is super().__init__ and super().__poster_init__
    in the __init__ method.
    """

    def __init__(self, sentence, bimodal_structure, eval_world='main', eval_time='now'):

        super().__init__(sentence, bimodal_structure)

        main_point = bimodal_structure.main_point
        self.eval_world = main_point["world"] if eval_world == 'main' else eval_world
        self.eval_time = main_point["time"] if eval_time == 'now' else eval_time
        self.truth_set, self.false_set = self.find_proposition()

    def __eq__(self, other):
        return (
            self.truth_set == other.truth_condition
            and self.false_set == other.false_condition
            and self.name == other.name
        )

    def __repr__(self):
        N = self.model_structure.model_constraints.semantics.N
        z3_model = self.model_structure.z3_model
        
        # Handle truth set
        truth_worlds = set()
        for bit in self.truth_set:
            if hasattr(bit, 'as_ast'):  # If it's a Z3 BitVec
                evaluated_bit = z3_model.evaluate(bit)
                truth_worlds.add(bitvec_to_substates(evaluated_bit, N))
            else:  # If it's already evaluated
                print(f"BIT {bit} TYPE {type(bit)}")
                truth_worlds.add(bitvec_to_substates(bit, N))
                
        # Handle false set
        false_worlds = set()
        for bit in self.false_set:  # Note: Changed from truth_set to false_set
            if hasattr(bit, 'as_ast'):  # If it's a Z3 BitVec
                evaluated_bit = z3_model.evaluate(bit)
                false_worlds.add(bitvec_to_substates(evaluated_bit, N))
            else:  # If it's already evaluated
                false_worlds.add(bitvec_to_substates(bit, N))
                
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

    def find_proposition(self):
        """takes self, returns the V, F tuple
        used in find_verifiers_and_falsifiers"""
        model = self.model_structure.z3_model
        semantics = self.semantics
        arguments = self.arguments or ()
        if self.sentence_letter is not None:
            T, F = set(), set()
            # Use the actual world arrays from all_worlds
            for world_key, world_array in self.model_structure.all_worlds.items():
                for time in range(self.semantics.M):
                    # Get the world state at this time point
                    world_state = model.evaluate(world_array[time])
                    # Evaluate if the sentence is true at this world and time
                    evaluated_expr = model.evaluate(
                        semantics.true_at(self.sentence, world_array, time)
                    )
                    if z3.is_true(evaluated_expr):
                        T.add(world_state)
                    else:
                        F.add(world_state)
            return T, F
        if self.operator is not None:
            return self.operator.find_truth_condition(*arguments, self.eval_world, self.eval_time)
        raise ValueError(f"There is no proposition for {self}.")

    def print_proposition(self, eval_point, indent_num, use_colors):
        """Print proposition with truth value at evaluation point."""
        semantics = self.model_structure.model_constraints.semantics
        z3_model = self.model_structure.z3_model
        
        if z3_model is None:
            print(f"{'  ' * indent_num}Cannot evaluate proposition - no valid model found")
            return

        # NOTE: THIS IS THE CORRECT WAY TO EVALUATE A WORLD AT A TIME
        # Get the world, time value, and world_state
        eval_time = eval_point["time"]
        eval_world = eval_point["world"]

        if eval_world is None:
            print(f"{'  ' * indent_num}Cannot evaluate proposition - no evaluation world available")
            return

        z3_eval_time = z3_model.evaluate(eval_time)
        world_state = z3_model.evaluate(eval_world[z3_eval_time])

        # Get truth value
        truth_expr = semantics.true_at(self.sentence, eval_world, eval_time)
        evaluated_expr = z3_model.evaluate(truth_expr)
        truth_value = z3.is_true(evaluated_expr) if z3.is_bool(evaluated_expr) else None
        
        # Convert to substates representation directly
        world_state_repr = bitvec_to_substates(world_state, semantics.N)
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
        self.all_times = range(1, self.M + 1)

        # Initialize Z3 model values
        self.z3_main_world = None
        self.z3_main_time = None
        self.z3_main_world_state = None
        self.world_mappings = None  # Will store all world states after model is found

        # Only evaluate if we have a valid model
        if self.z3_model_status and self.z3_model is not None:
            self.z3_main_world = self.z3_model[self.main_world]
            self.z3_main_time = self.z3_model[self.main_time]
            self.main_point["world"] = self.z3_main_world
            self.main_point["time"] = self.z3_main_time
            # self.all_worlds = self.semantics.all_worlds
            # Extract all world mappings from the model
            self.world_mappings, self.main_world_mapping, self.all_worlds = self.semantics.extract_model_worlds(self.z3_model)
            if self.z3_main_world is not None and self.z3_main_time is not None:
                self.z3_main_world_state = self.z3_main_world[self.z3_main_time]

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
