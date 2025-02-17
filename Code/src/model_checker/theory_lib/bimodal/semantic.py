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
    }

    def __init__(self, N):

        # Initialize the superclass to set defaults
        super().__init__(N)

        ### Define the Z3 primitives ###

        self.WorldStateSort = z3.BitVecSort(N)
        # Create a sort for world states using bitvectors such as <001101>
        # N determines how many distinct worlds we can represent

        self.task = z3.Function(
            "Task",
            self.WorldStateSort,
            self.WorldStateSort,
            z3.BoolSort()
        )  # Define a binary task relation between world states
        
        self.TimeSort = z3.IntSort()
        # Create a sort for times using integers

        self.main_time = z3.Int('main_time')

        self.truth_condition = z3.Function(
            "truth_condition",
            self.WorldStateSort,
            syntactic.AtomSort,
            z3.BoolSort()
        )

        self.main_world = z3.Array('main_world', self.TimeSort, self.WorldStateSort)
        # Define an arbitrary world at which to evaluate sentences 
        # The identity of this world may change between models
        # For each time t, main_world[t] gives exactly one world state
        # Use `Store(array, index, value)` to update mappings
            # Set the world state at time 1
            # new_main_world = z3.Store(self.main_world, 1, some_world_state)
        # Use `Select(array, index)` to get values
            # Get the world state at time 0
            # world_at_time_0 = z3.Select(self.main_world, 0)

        ### Define the frame constraints ###

        tau = z3.Array('frame_world_tau', self.TimeSort, self.WorldStateSort)
        # declare possible world variable named to reflect the constraint
        x, y = z3.Ints("frame_time_x frame_time_y")
        # declare two time variables with names to reflect the constraint
        lawful = z3.ForAll(
            tau,
            z3.ForAll(
                [x, y],
                z3.Implies(
                    y == x + 1,
                    self.task(tau[x], tau[y])
                )
            )
        )  # Require there to be a task from every world state to its successor

        u, v = z3.BitVecs("frame_state_u frame_state_v", N)
        # Define variables for world states with names to indicate constraint
        seriel = ForAll(
            u,
            Exists(
                v,
                self.task(u, v)
            )
        )  # Serial: Require every world state to see some state

        # Define frame constraints
        self.frame_constraints = [
            lawful,
            # seriel,
        ]

        # Define invalidity conditions
        self.premise_behavior = lambda premise: self.true_at(premise, self.main_world, self.main_time)
        self.conclusion_behavior = lambda conclusion: self.true_at(conclusion, self.main_world, self.main_time)

    def true_at(self, sentence, eval_world, eval_time):
        """Returns a Z3 formula that is satisfied when the sentence is true at eval_world at eval_time.

        Args:
            sentence: The sentence to evaluate
            eval_world: The world state array at which to evaluate the sentence
            eval_time: The time point at which to evaluate the sentence
            
        Returns:
            Z3 formula that is satisfied when sentence is true at eval_world at eval_time
        """
        sentence_letter = sentence.sentence_letter  # store sentence letter

        # base case
        if sentence_letter is not None:                     
            eval_world_state = eval_world[eval_time]
            return self.truth_condition(eval_world_state, sentence_letter)  # true in main_world

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

    def __init__(self, sentence, model_structure, eval_world='main', eval_time='now'):

        super().__init__(sentence, model_structure)
        self.eval_world = model_structure.main_world if eval_world == 'main' else eval_world
        self.eval_time = model_structure.main_time if eval_time == 'now' else eval_time
        self.truth_set, self.false_set = self.find_proposition()

    def __eq__(self, other):
        return (
            self.truth_set == other.truth_condition
            and self.false_set == other.false_condition
            and self.name == other.name
        )

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
                semantics.false_at(x, sentence_letter)
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
        all_world_states = self.model_structure.all_bits
        model = self.model_structure.z3_model
        semantics = self.semantics
        eval_world = self.eval_world
        eval_time = self.eval_time
        operator = self.operator
        arguments = self.arguments or ()
        sentence_letter = self.sentence_letter
        if sentence_letter is not None:
            T, F = set(), set()
            for world_state in all_world_states:
                T.add(world_state) if model.evaluate(
                    semantics.true_at(world_state, sentence_letter)
                ) else F.add(world_state)
            return T, F
        if operator is not None:
            return operator.find_truth_condition(*arguments, eval_world, eval_time)
        raise ValueError(f"Their is no proposition for {self}.")

    def print_proposition(self, eval_world, eval_time, indent_num, use_colors):
        semantics = self.model_structure.model_constraints.semantics
        eval_world_state = eval_world[eval_time]
        truth_value = semantics.true_at(eval_world_state)
        world_state = bitvec_to_substates(eval_world_state, semantics.N)
        RESET, FULL, PART = self.set_colors(
            self.name,
            indent_num,
            truth_value,
            world_state,
            use_colors
        )
        print(
            f"{'  ' * indent_num}{FULL}|{self.name}| = {self}{RESET}"
            f"  {PART}({truth_value} in {world_state}){RESET}"
        )


# TODO: continue adapting to BimodalSemantics
class BimodalStructure(ModelDefaults):

    def __init__(self, model_constraints, max_time=1):

        super().__init__(model_constraints, max_time)

        # Store possible_bits, world_bits, and main_world from the Z3 model
        if not self.z3_model_status:
            self.main_world, self.main_time = None, None
            return
        # self.poss_bits = [
        #     bit
        #     for bit in self.all_bits
        #     if bool(self.z3_model.evaluate(self.semantics.possible(bit)))  # type: ignore
        # ]
        if not self.z3_model is None:
            self.main_world = self.z3_model[self.main_world]
            self.main_time = self.z3_model[self.main_time]

    def print_evaluation(self, output=sys.__stdout__):
        """print the evaluation world and all sentences letters that true/false
        in that world"""
        BLUE = ""
        RESET = ""
        main_world = self.main_world
        if output is sys.__stdout__:
            BLUE = "\033[34m"
            RESET = "\033[0m"
        print(
            f"\nThe evaluation world is: {BLUE}{bitvec_to_substates(main_world, self.N)}{RESET}\n",
            file=output,
        )

    def print_states(self, output=sys.__stdout__):
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
        print("State Space:", file=output)
        for bit in self.all_bits:
            state = bitvec_to_substates(bit, self.N)
            bin_rep = binary_bitvector(bit)
            if bit == 0:
                format_state(bin_rep, state, self.COLORS["initial"])
            elif bit in self.world_bits:
                format_state(bin_rep, state, self.COLORS["world"], "world")
            elif bit in self.poss_bits:
                format_state(bin_rep, state, self.COLORS["possible"])
            elif self.settings['print_impossible']:
                format_state(bin_rep, state, self.COLORS["impossible"], "impossible")

    def print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__):
        """prints states, sentence letters evaluated at the designated world and
        recursively prints each sentence and its parts"""
        model_status = self.z3_model_status
        self.print_info(model_status, default_settings, example_name, theory_name, output)
        if model_status:
            self.print_states(output)
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
