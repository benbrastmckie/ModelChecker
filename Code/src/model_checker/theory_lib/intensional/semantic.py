import z3

from model_checker.model import (
    IntensionalSemanticDefaults,
    IntensionalPropositionDefaults,
)

from model_checker.utils import (
    ForAll,
    Exists,
    bitvec_to_substates,
)

from model_checker import syntactic


##############################################################################
######################### SEMANTICS AND PROPOSITIONS #########################
##############################################################################


class Semantics(IntensionalSemanticDefaults):
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

        self.main_time = z3.Int('main_time', self.TimeSort)

        self.truth_condition = z3.Function(
            "truth_condition",
            self.WorldStateSort,
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
            seriel,
        ]

        # Define invalidity conditions
        self.premise_behavior = self.true_at
        self.conclusion_behavior = self.false_at


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
            return self.truth_condition(eval_world_state)  # true in main_world

        # recursive case
        operator = sentence.operator  # store operator
        arguments = sentence.arguments or () # store arguments
        return operator.true_at(
            *arguments,  # this is a possibly empty tuple
            eval_world,  # passed through from above
            eval_time  # passed through from above
        )  # apply semantics for the operator

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


class IntensionalProposition(IntensionalPropositionDefaults):
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
