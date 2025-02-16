import z3

from model_checker.utils import (
    ForAll,
    Exists,
)

from model_checker import syntactic

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

    def print_method(self, sentence_obj, eval_world, eval_time, indent_num, use_colors):
        """Prints the proposition and its argument."""
        world_state = eval_world[eval_time]
        self.general_print(sentence_obj, world_state, indent_num, use_colors)


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
    
    def print_method(self, sentence_obj, eval_world, eval_time, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        world_state = eval_world[eval_time]
        self.general_print(sentence_obj, world_state, indent_num, use_colors)


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
    
    def print_method(self, sentence_obj, eval_world, eval_time, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        world_state = eval_world[eval_time]
        self.general_print(sentence_obj, world_state, indent_num, use_colors)


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

    def print_method(self, sentence_obj, eval_world, eval_time, indent_num, use_colors):
        """Prints the proposition."""
        world_state = eval_world[eval_time]
        self.general_print(sentence_obj, world_state, indent_num, use_colors)


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

    def find_truth_condition(self, eval_world, eval_time, eval_time):
        """Returns (empty set, all bits)."""
        return set(), set(self.semantics.all_bits)

    def print_method(self, sentence_obj, eval_world, eval_time, indent_num, use_colors):
        """Prints the proposition."""
        world_state = eval_world[eval_time]
        self.general_print(sentence_obj, world_state, indent_num, use_colors)


##############################################################################
########################### INTENSIONAL OPERATORS ############################
##############################################################################

class NecessityOperator(syntactic.Operator):
    name = "\\Box"
    arity = 1

    def true_at(self, argument, eval_world, eval_time):
        semantics = self.semantics
        tau = z3.Array('true_world_tau', semantics.TimeSort, semantics.WorldStateSort)
        return ForAll(
            tau,
            semantics.true_at(argument, tau, eval_time),
        )
    
    def false_at(self, argument, eval_world, eval_time):
        semantics = self.semantics
        mu = z3.Array('false_world_tau', semantics.TimeSort, semantics.WorldStateSort)
        return ForAll(
            mu,
            semantics.false_at(argument, mu, eval_time),
        )
    
    def find_truth_condition(self, argument, eval_world, eval_time):
        evaluate = argument.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(argument, eval_world, eval_time))):
            return {self.semantics.all_bits}, set()
        if bool(evaluate(self.false_at(argument, eval_world, eval_time))):
            return set(), {self.semantics.all_bits}
        raise ValueError(
            f"{self.name} {argument} "
            f"is neither true nor false in the world {eval_world}."
        )
    
    def print_method(self, sentence_obj, eval_world, eval_time, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        world_state = eval_world[eval_time]
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, world_state, all_worlds, indent_num, use_colors)


##############################################################################
######################## DEFINED EXTENSIONAL OPERATORS #######################
##############################################################################

class ConditionalOperator(syntactic.DefinedOperator):

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):  # type: ignore
        return [OrOperator, [NegationOperator, leftarg], rightarg]
    
    def print_method(self, sentence_obj, eval_world, eval_time, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        world_state = eval_world[eval_time]
        self.general_print(sentence_obj, world_state, indent_num, use_colors)


class BiconditionalOperator(syntactic.DefinedOperator):

    name = "\\leftrightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):  # type: ignore
        right_to_left = [ConditionalOperator, leftarg, rightarg]
        left_to_right = [ConditionalOperator, rightarg, leftarg]
        return [AndOperator, right_to_left, left_to_right]
    
    def print_method(self, sentence_obj, eval_world, eval_time, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        world_state = eval_world[eval_time]
        self.general_print(sentence_obj, world_state, indent_num, use_colors)


##############################################################################
####################### DEFINED INTENSIONAL OPERATORS ########################
##############################################################################

class DefPossibilityOperator(syntactic.DefinedOperator):

    name = "\\possible"
    arity = 1

    def derived_definition(self, arg):  # type: ignore
        return [NegationOperator, [NecessityOperator, [NegationOperator, arg]]]
    
    def print_method(self, sentence_obj, eval_world, eval_time, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        world_state = eval_world[eval_time]
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, world_state, all_worlds, indent_num, use_colors)

intensional_operators = syntactic.OperatorCollection(
    # primitive operators
    NegationOperator,
    AndOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    NecessityOperator,

    # defined operators
    ConditionalOperator,
    BiconditionalOperator,
    DefPossibilityOperator,
)

