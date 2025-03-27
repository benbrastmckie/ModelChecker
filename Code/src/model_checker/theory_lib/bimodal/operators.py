import z3


# Try local imports first (for development)
try:
    from src.model_checker import syntactic
    from src.model_checker.utils import pretty_set_print
except ImportError:
    from model_checker import syntactic
    from model_checker.utils import pretty_set_print

##############################################################################
############################ EXTENSIONAL OPERATORS ###########################
##############################################################################

class NegationOperator(syntactic.Operator):
    """Logical negation operator that inverts the truth value of its argument."""

    name = "\\neg"
    arity = 1

    def true_at(self, argument, eval_world, eval_time):
        """Returns true if argument is false."""
        return self.semantics.false_at(argument, eval_world, eval_time)

    def false_at(self, argument, eval_world, eval_time):
        """Returns false if argument is true."""
        return self.semantics.true_at(argument, eval_world, eval_time)

    def find_truth_condition(self, arg_sent_obj, eval_world, eval_time):
        """Returns truth and false sets for negation."""
        Y_V, Y_F = arg_sent_obj.proposition.find_proposition()
        return Y_F, Y_V

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class AndOperator(syntactic.Operator):
    """Logical conjunction operator."""

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world, eval_time):
        """Returns true if both arguments are true."""
        semantics = self.semantics
        return z3.And(
            semantics.true_at(leftarg, eval_world, eval_time),
            semantics.true_at(rightarg, eval_world, eval_time)
        )

    def false_at(self, leftarg, rightarg, eval_world, eval_time):
        """Returns true if either argument is false."""
        semantics = self.semantics
        return z3.Or(
            semantics.false_at(leftarg, eval_world, eval_time),
            semantics.false_at(rightarg, eval_world, eval_time)
        )

    def find_truth_condition(self, leftarg, rightarg, eval_world, eval_time):
        """Gets truth/false sets for conjunction of arguments."""
        Y_V, Y_F = leftarg.proposition.find_proposition()
        Z_V, Z_F = rightarg.proposition.find_proposition()
        return Y_V.intersection(Z_V), Y_F.union(Z_F)
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class OrOperator(syntactic.Operator):
    """Logical disjunction operator."""

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world, eval_time):
        """Returns true if either argument is true."""
        semantics = self.semantics
        return z3.Or(
            semantics.true_at(leftarg, eval_world, eval_time),
            semantics.true_at(rightarg, eval_world, eval_time)
        )

    def false_at(self, leftarg, rightarg, eval_world, eval_time):
        """Returns true if both arguments are false."""
        semantics = self.semantics
        return z3.And(
            semantics.false_at(leftarg, eval_world, eval_time),
            semantics.false_at(rightarg, eval_world, eval_time)
        )

    def find_truth_condition(self, leftarg, rightarg, eval_world, eval_time):
        """Gets truth/false sets for disjunction of arguments."""
        Y_V, Y_F = leftarg.proposition.find_proposition()
        Z_V, Z_F = rightarg.proposition.find_proposition()
        return Y_V.union(Z_V), Y_F.intersection(Z_F)
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
############################## EXTREMAL OPERATORS ############################
##############################################################################

class TopOperator(syntactic.Operator):
    """Top element of the space of propositions with respect to ground.
    Is verified by everything and falsified by the full state."""

    name = "\\top"
    arity = 0

    def true_at(self, eval_world, eval_time):
        """Returns true for any world state."""
        world_state = eval_world[eval_time]
        return world_state == world_state

    def false_at(self, eval_world, eval_time):
        """Returns false for any world state."""
        world_state = eval_world[eval_time]
        return world_state != world_state

    def find_truth_condition(self, eval_world, eval_time):
        """Returns (all bits, empty set)."""
        return set(self.semantics.all_bits), set()

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BotOperator(syntactic.Operator):
    """Bottom element of space of propositions. Verified by nothing, falsified by null state."""

    name = "\\bot"
    arity = 0

    def true_at(self, eval_world, eval_time):
        """Returns true if world state != itself (always false)."""
        world_state = eval_world[eval_time]
        return world_state != world_state

    def false_at(self, eval_world, eval_time):
        """Returns true if world state == itself (always true)."""
        world_state = eval_world[eval_time]
        return world_state == world_state

    def find_truth_condition(self, eval_world, eval_time):
        """Returns (empty set, all bits)."""
        return set(), set(self.semantics.all_bits)

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
############################## MODAL OPERATORS ###############################
##############################################################################

class NecessityOperator(syntactic.Operator):
    name = "\\Box"
    arity = 1

    def true_at(self, argument, eval_world, eval_time):
        """Returns true if argument is true in all possible worlds at eval_time.
        It is important that no restrictions are placed on accessibility between worlds."""
        semantics = self.semantics
        world_id = z3.Int('nec_true_world_id')
        return z3.ForAll(
            world_id,
            z3.Implies(
                # If world_id is used in the world_function
                semantics.world_exists(world_id, eval_time),
                # Then world_id makes the argument true
                semantics.true_at(argument, semantics.world_function(world_id), eval_time)
            )
        )

    def false_at(self, argument, eval_world, eval_time):
        """Returns true if argument is false in at least one possible world at eval_time.
        It is important that no restrictions are placed on accessibility between worlds."""
        semantics = self.semantics
        world_id = z3.Int('nec_false_world_id')
        return z3.Exists(
            world_id,
            z3.And(
                # The world_id is used in the world_function
                semantics.world_exists(world_id, eval_time),
                # And world_id makes the argument false
                semantics.false_at(argument, semantics.world_function(world_id), eval_time)
            )
        )

    def find_truth_condition(self, argument, eval_world, eval_time):
        """Gets truth/false sets for necessity of argument.
        □φ is true at a world w iff φ is true at all worlds accessible from w."""
        model_structure = argument.proposition.model_structure
        z3_model = model_structure.z3_model
        semantics = self.semantics
        
        # Check if argument is true in all worlds
        all_true = True
        for world_array in model_structure.all_worlds.values():
            truth_expr = semantics.true_at(argument, world_array, eval_time)
            evaluated_expr = z3_model.evaluate(truth_expr)
            if not z3.is_true(evaluated_expr):
                all_true = False
                break
        
        all_world_states = set(self.semantics.all_bits)
        if all_true:
            return all_world_states, set()  # True everywhere
        return set(), all_world_states  # False everywhere

    def print_method(self, argument, eval_point, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = argument.proposition.model_structure.all_worlds.values()
        self.print_over_worlds(argument, eval_point, all_worlds, indent_num, use_colors)
   

##############################################################################
############################## TENSE OPERATORS ###############################
##############################################################################

class FutureOperator(syntactic.Operator):
    name = "\\Future"
    arity = 1

    def true_at(self, argument, eval_world, eval_time):
        semantics = self.semantics
        time = z3.Int('future_true_time')
        return z3.ForAll(
            time,
            z3.Implies(
                z3.And(
                    semantics.time_exists(time),
                    eval_time < time,
                ),
                semantics.true_at(argument, eval_world, time),
            )
        )
    
    def false_at(self, argument, eval_world, eval_time):
        semantics = self.semantics
        time = z3.Int('future_false_time')
        return z3.Exists(
            time,
            z3.And(
                semantics.time_exists(time),
                eval_time < time,
                semantics.false_at(argument, eval_world, time),
            )
        )
    
    # TODO: replace with (world, time) pairs, calling this the extension
    def find_truth_condition(self, argument, eval_world, eval_time):
        Y_V, Y_F = argument.proposition.find_proposition()
        Z_V = self.semantics.all_bits if Y_V else set()
        Z_F = set() if Y_F else self.semantics.all_bits
        return Z_V, Z_F
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_times = sentence_obj.proposition.model_structure.all_times
        self.print_over_times(sentence_obj, eval_point, all_times, indent_num, use_colors)


class PastOperator(syntactic.Operator):
    name = "\\Past"
    arity = 1

    def true_at(self, argument, eval_world, eval_time):
        semantics = self.semantics
        time = z3.Int('past_true_time')
        return z3.ForAll(
            time,
            z3.Implies(
                z3.And(
                    semantics.time_exists(time),
                    eval_time > time,
                ),
                semantics.true_at(argument, eval_world, time),
            )
        )
    
    def false_at(self, argument, eval_world, eval_time):
        semantics = self.semantics
        time = z3.Int('past_false_time')
        return z3.Exists(
            time,
            z3.And(
                semantics.time_exists(time),
                eval_time > time,
                semantics.false_at(argument, eval_world, time),
            )
        )
    
    # TODO: replace with (world, time) pairs, calling this the extension
    def find_truth_condition(self, argument, eval_world, eval_time):
        Y_V, Y_F = argument.proposition.find_proposition()
        Z_V = self.semantics.all_bits if Y_V else set()
        Z_F = set() if Y_F else self.semantics.all_bits
        return Z_V, Z_F
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        all_times = sentence_obj.proposition.model_structure.all_times
        self.print_over_times(sentence_obj, eval_point, all_times, indent_num, use_colors)


##############################################################################
######################## DEFINED EXTENSIONAL OPERATORS #######################
##############################################################################

class ConditionalOperator(syntactic.DefinedOperator):

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):  # type: ignore
        return [OrOperator, [NegationOperator, leftarg], rightarg]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BiconditionalOperator(syntactic.DefinedOperator):

    name = "\\leftrightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):  # type: ignore
        right_to_left = [ConditionalOperator, leftarg, rightarg]
        left_to_right = [ConditionalOperator, rightarg, leftarg]
        return [AndOperator, right_to_left, left_to_right]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
####################### DEFINED INTENSIONAL OPERATORS ########################
##############################################################################

class DefPossibilityOperator(syntactic.DefinedOperator):

    name = "\\Diamond"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [NegationOperator, [NecessityOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.all_worlds.values()
        self.print_over_worlds(sentence_obj, eval_point, all_worlds, indent_num, use_colors)

##############################################################################
######################### DEFINED TEMPORAL OPERATORS #########################
##############################################################################

class DefFutureOperator(syntactic.DefinedOperator):

    name = "\\future"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [NegationOperator, [FutureOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        all_times = sentence_obj.proposition.model_structure.all_times
        self.print_over_times(sentence_obj, eval_point, all_times, indent_num, use_colors)

class DefPastOperator(syntactic.DefinedOperator):

    name = "\\past"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [NegationOperator, [PastOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        all_times = sentence_obj.proposition.model_structure.all_times
        self.print_over_times(sentence_obj, eval_point, all_times, indent_num, use_colors)


intensional_operators = syntactic.OperatorCollection(
    # extensional operators
    NegationOperator,
    AndOperator,
    OrOperator,

    # extremal operators
    TopOperator,
    BotOperator,

    # modal operators
    NecessityOperator,

    # tense operators
    FutureOperator,
    PastOperator,

    # defined operators
    ConditionalOperator,
    BiconditionalOperator,
    DefPossibilityOperator,
    DefFutureOperator,
    DefPastOperator,
)

