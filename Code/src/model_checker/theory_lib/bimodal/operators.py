import z3


# Try installed package imports first
try:
    from model_checker import syntactic
    from model_checker.utils import pretty_set_print
except ImportError:
    # Fall back to local imports for development
    from src.model_checker import syntactic
    from src.model_checker.utils import pretty_set_print

##############################################################################
############################ EXTENSIONAL OPERATORS ###########################
##############################################################################

class NegationOperator(syntactic.Operator):
    """Logical negation operator that inverts the truth value of its argument."""

    name = "\\neg"
    arity = 1

    def true_at(self, argument, eval_world, eval_time):
        """Returns true if argument is false.
        
        Args:
            argument: The argument to negate
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        return self.semantics.false_at(argument, eval_world, eval_time)

    def false_at(self, argument, eval_world, eval_time):
        """Returns false if argument is true.
        
        Args:
            argument: The argument to negate
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        return self.semantics.true_at(argument, eval_world, eval_time)

    def find_truth_condition(self, argument, eval_world, eval_time):
        """Gets truth-condition for the negation of an argument.
        
        Args:
            argument: The argument to negate
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        argument_truth_condition = argument.proposition.extension
        new_truth_condition = {}
        for world_array, temporal_profile in argument_truth_condition.items():
            true_times, false_times = temporal_profile
            new_truth_condition[world_array] = (false_times, true_times)
        return new_truth_condition

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class AndOperator(syntactic.Operator):
    """Logical conjunction operator."""

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world, eval_time):
        """Returns true if both arguments are true.
        
        Args:
            leftarg: The left argument of the conjunction
            rightarg: The right argument of the conjunction
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics
        return z3.And(
            semantics.true_at(leftarg, eval_world, eval_time),
            semantics.true_at(rightarg, eval_world, eval_time)
        )

    def false_at(self, leftarg, rightarg, eval_world, eval_time):
        """Returns true if either argument is false.
        
        Args:
            leftarg: The left argument of the conjunction
            rightarg: The right argument of the conjunction
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics
        return z3.Or(
            semantics.false_at(leftarg, eval_world, eval_time),
            semantics.false_at(rightarg, eval_world, eval_time)
        )

    def find_truth_condition(self, leftarg, rightarg, eval_world, eval_time):
        """Gets truth-condition for the conjunction of two arguments.
        
        Args:
            leftarg: The left argument of the conjunction
            rightarg: The right argument of the conjunction
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        leftarg_truth_condition = leftarg.proposition.extension
        rightarg_truth_condition = rightarg.proposition.extension
        new_truth_condition = {}
        for world_array, temporal_profile in leftarg_truth_condition.items():
            left_true_times, left_false_times = temporal_profile
            right_true_times, right_false_times = rightarg_truth_condition[world_array]
            # Find intersection while preserving order from left_true_times
            new_true_times = [t for t in left_true_times if t in right_true_times]
            # Find union while preserving order and removing duplicates
            new_false_times = sorted(set(left_false_times) | set(right_false_times))
            new_truth_condition[world_array] = (new_true_times, new_false_times)
        return new_truth_condition

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class OrOperator(syntactic.Operator):
    """Logical disjunction operator."""

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world, eval_time):
        """Returns true if either argument is true.
        
        Args:
            leftarg: The left argument of the disjunction
            rightarg: The right argument of the disjunction
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics
        return z3.Or(
            semantics.true_at(leftarg, eval_world, eval_time),
            semantics.true_at(rightarg, eval_world, eval_time)
        )

    def false_at(self, leftarg, rightarg, eval_world, eval_time):
        """Returns true if both arguments are false.
        
        Args:
            leftarg: The left argument of the disjunction
            rightarg: The right argument of the disjunction
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics
        return z3.And(
            semantics.false_at(leftarg, eval_world, eval_time),
            semantics.false_at(rightarg, eval_world, eval_time)
        )

    def find_truth_condition(self, leftarg, rightarg, eval_world, eval_time):
        """Gets truth-condition for the disjunction of two arguments.
        
        Args:
            leftarg: The left argument of the disjunction
            rightarg: The right argument of the disjunction
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        leftarg_truth_condition = leftarg.proposition.extension
        rightarg_truth_condition = rightarg.proposition.extension
        new_truth_condition = {}
        for world_array, temporal_profile in leftarg_truth_condition.items():
            left_true_times, left_false_times = temporal_profile
            right_true_times, right_false_times = rightarg_truth_condition[world_array]
            # Find union of true times
            new_true_times = sorted(set(left_true_times) | set(right_true_times))
            # Find intersection of false times
            new_false_times = [t for t in left_false_times if t in right_false_times]
            new_truth_condition[world_array] = (new_true_times, new_false_times)
        return new_truth_condition
    
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
        # Get the world array from the world ID
        world_array = self.semantics.world_function(eval_world)
        world_state = z3.Select(world_array, eval_time)
        return world_state == world_state

    def false_at(self, eval_world, eval_time):
        """Returns false for any world state."""
        # Get the world array from the world ID
        world_array = self.semantics.world_function(eval_world)
        world_state = z3.Select(world_array, eval_time)
        return world_state != world_state

    def find_truth_condition(self, eval_world, eval_time):
        """Returns (all bits, empty set)."""
        return self.semantics.all_true

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BotOperator(syntactic.Operator):
    """Bottom element of space of propositions. Verified by nothing, falsified by null state."""

    name = "\\bot"
    arity = 0

    def true_at(self, eval_world, eval_time):
        """Returns true if world state != itself (always false)."""
        # Get the world array from the world ID
        world_array = self.semantics.world_function(eval_world)
        world_state = z3.Select(world_array, eval_time)
        return world_state != world_state

    def false_at(self, eval_world, eval_time):
        """Returns true if world state == itself (always true)."""
        # Get the world array from the world ID
        world_array = self.semantics.world_function(eval_world)
        world_state = z3.Select(world_array, eval_time)
        return world_state == world_state

    def find_truth_condition(self, eval_world, eval_time):
        """Returns (empty set, all bits)."""
        return self.semantics.all_false

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
                semantics.true_at(argument, world_id, eval_time)
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
                semantics.false_at(argument, world_id, eval_time)
            )
        )

    def find_truth_condition(self, argument, eval_world, eval_time):
        """Gets truth-condition for: 'It is necessary that: argument'."""
        model_structure = argument.proposition.model_structure
        argument_extension = argument.proposition.extension
        for world_array, temporal_profile in argument_extension.items():
            true_times, false_times = temporal_profile
            if eval_time in false_times:
                # If eval_time is in false_times, mark all times as false for all worlds
                return self.semantics.all_false
        return self.semantics.all_true

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
        """Returns true if argument is true at all future times in this world's interval.
        
        Args:
            argument: The argument to apply the future operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics
        time = z3.Int('future_true_time')
        return z3.ForAll(
            time,
            z3.Implies(
                z3.And(
                    # Time is within the valid range for this world's interval
                    semantics.is_valid_time_for_world(eval_world, time),
                    # Time is in the future of eval_time
                    eval_time < time,
                ),
                semantics.true_at(argument, eval_world, time),
            )
        )
    
    def false_at(self, argument, eval_world, eval_time):
        """Returns true if argument is false at at least one future time in this world's interval.
        
        Args:
            argument: The argument to apply the future operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics
        time = z3.Int('future_false_time')
        return z3.Exists(
            time,
            z3.And(
                # Time is within the valid range for this world's interval
                semantics.is_valid_time_for_world(eval_world, time),
                # Time is in the future of eval_time
                eval_time < time,
                semantics.false_at(argument, eval_world, time),
            )
        )
    
    def find_truth_condition(self, argument, eval_world, eval_time):
        """Gets truth-condition for 'It will always be the case that: argument'.
        
        Args:
            argument: The argument to apply the future operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        model_structure = argument.proposition.model_structure
        argument_extension = argument.proposition.extension
        new_truth_condition = {}
        for world_array, temporal_profile in argument_extension.items():
            true_times, false_times = temporal_profile
            if not false_times:  # If false_times is empty
                new_truth_condition[world_array] = (model_structure.all_times, [])
            else:
                # Get a copy to avoid modifying the original
                false_times_copy = list(false_times)
                final_false_time = max(false_times_copy) if false_times_copy else -1
                new_true_times = []
                new_false_times = []
                for time in model_structure.all_times:
                    if time > final_false_time:
                        new_true_times.append(time)
                    else:
                        new_false_times.append(time)
                new_truth_condition[world_array] = (new_true_times, new_false_times)
        return new_truth_condition
    
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
        """Returns true if argument is true at all past times in this world's interval.
        
        Args:
            argument: The argument to apply the past operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics
        time = z3.Int('past_true_time')
        return z3.ForAll(
            time,
            z3.Implies(
                z3.And(
                    # Time is within the valid range for this world's interval
                    semantics.is_valid_time_for_world(eval_world, time),
                    # Time is in the past of eval_time
                    eval_time > time,
                ),
                semantics.true_at(argument, eval_world, time),
            )
        )
    
    def false_at(self, argument, eval_world, eval_time):
        """Returns true if argument is false at at least one past time in this world's interval.
        
        Args:
            argument: The argument to apply the past operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics
        time = z3.Int('past_false_time')
        return z3.Exists(
            time,
            z3.And(
                # Time is within the valid range for this world's interval
                semantics.is_valid_time_for_world(eval_world, time),
                # Time is in the past of eval_time
                eval_time > time,
                semantics.false_at(argument, eval_world, time),
            )
        )
    
    def find_truth_condition(self, argument, eval_world, eval_time):
        """Gets truth-condition for 'It has always been the case that: argument'.
        
        Args:
            argument: The argument to apply the past operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        model_structure = argument.proposition.model_structure
        argument_extension = argument.proposition.extension
        new_truth_condition = {}
        for world_array, temporal_profile in argument_extension.items():
            true_times, false_times = temporal_profile
            # Get a copy to avoid modifying the original
            false_times_copy = list(false_times)
            first_false_time = min(false_times_copy) if false_times_copy else float('inf')
            new_true_times = []
            new_false_times = []
            for time in model_structure.all_times:
                if time < first_false_time:
                    new_true_times.append(time)
                else:
                    new_false_times.append(time)
            new_truth_condition[world_array] = (new_true_times, new_false_times)
        return new_truth_condition
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print the sentence over all time points.
        
        Args:
            sentence_obj: The sentence to print
            eval_point: The evaluation point (world ID and time)
            indent_num: The indentation level
            use_colors: Whether to use colors in output
        """
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

