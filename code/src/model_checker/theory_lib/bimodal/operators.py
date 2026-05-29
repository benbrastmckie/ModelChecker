"""Implements the operators for bimodal logic in the model checker.

This module provides implementations of various logical operators used in bimodal logic,
which combines temporal and modal reasoning. The operators are organized into several
categories based on their semantic role:

Extensional Operators:
    - NegationOperator (¬): Logical negation
    - AndOperator (∧): Logical conjunction
    - OrOperator (∨): Logical disjunction
    - ConditionalOperator (→): Material implication (defined)
    - BiconditionalOperator (↔): Material biconditional (defined)

Extremal Operators:
    - BotOperator (⊥): Logical contradiction/falsity
    - TopOperator (⊤): Logical tautology/truth (defined)

Modal Operators:
    - NecessityOperator (□): Truth in all possible worlds
    - DefPossibilityOperator (◇): Truth in at least one possible world (defined)

Temporal Operators:
    - FutureOperator (⏵): Truth at all future times
    - PastOperator (⏴): Truth at all past times
    - UntilOperator (U): Event holds at future time with guard in between
    - SinceOperator (S): Event held at past time with guard in between
    - DefFutureOperator: Possibility of future truth (defined)
    - DefPastOperator: Possibility of past truth (defined)

All operators adhere to a fail-fast philosophy, raising explicit errors when
required data is missing or invalid rather than attempting fallbacks.
"""

from model_checker import z3_shim as z3


from model_checker import syntactic
from model_checker.utils import pretty_set_print
from model_checker.solver import is_true

##############################################################################
############################ EXTENSIONAL OPERATORS ###########################
##############################################################################

class NegationOperator(syntactic.Operator):
    """Logical negation operator that inverts the truth value of its argument.
    
    This operator implements classical logical negation (¬). When applied to a formula A,
    it returns true when A is false and false when A is true.
    
    Key Properties:
        - Involutive: ¬¬A ≡ A
        - Preserves excluded middle: A ∨ ¬A is a tautology
        - Preserves non-contradiction: ¬(A ∧ ¬A) is a tautology
        - Extensional: Value depends only on truth value of argument
        
    Example:
        If p means "it's raining", then ¬p means "it's not raining"
    """

    name = "\\neg"
    arity = 1

    def true_at(self, argument, eval_point):
        """Returns true if argument is false.
        
        Args:
            argument: The argument to negate
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        return self.semantics.false_at(argument, eval_point)

    def false_at(self, argument, eval_point):
        """Returns false if argument is true.
        
        Args:
            argument: The argument to negate
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        return self.semantics.true_at(argument, eval_point)

    def find_truth_condition(self, argument, eval_point):
        """Gets truth-condition for the negation of an argument.
        
        Args:
            argument: The argument to negate
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where the true and false times are swapped from the argument's extension
        """
        new_truth_condition = {}
        for world_id, temporal_profile in argument.proposition.extension.items():
            true_times, false_times = temporal_profile
            new_truth_condition[world_id] = (false_times, true_times)
        return new_truth_condition

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class AndOperator(syntactic.Operator):
    """Logical conjunction operator that returns true when both arguments are true.
    
    This operator implements classical logical conjunction (∧). When applied to formulas
    A and B, it returns true when both A and B are true, and false otherwise.
    
    Key Properties:
        - Commutative: A ∧ B ≡ B ∧ A
        - Associative: (A ∧ B) ∧ C ≡ A ∧ (B ∧ C)
        - Identity: A ∧ ⊤ ≡ A
        - Annihilator: A ∧ ⊥ ≡ ⊥
        - Idempotent: A ∧ A ≡ A
        - Extensional: Value depends only on truth values of arguments
        
    Example:
        If p means "it's raining" and q means "it's cold", then (p ∧ q) means 
        "it's raining and it's cold"
    """

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Returns true if both arguments are true.
        
        Args:
            leftarg: The left argument of the conjunction
            rightarg: The right argument of the conjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics
        return z3.And(
            semantics.true_at(leftarg, eval_point),
            semantics.true_at(rightarg, eval_point)
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Returns true if either argument is false.
        
        Args:
            leftarg: The left argument of the conjunction
            rightarg: The right argument of the conjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics
        return z3.Or(
            semantics.false_at(leftarg, eval_point),
            semantics.false_at(rightarg, eval_point)
        )

    def find_truth_condition(self, leftarg, rightarg, eval_point):
        """Gets truth-condition for the conjunction of two arguments.
        
        Args:
            leftarg: The left argument of the conjunction
            rightarg: The right argument of the conjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where true_times are the intersection of both arguments' true times,
                 and false_times are the union of both arguments' false times
        """
        leftarg_truth_condition = leftarg.proposition.extension
        rightarg_truth_condition = rightarg.proposition.extension
        new_truth_condition = {}
        
        for world_id, temporal_profile in leftarg_truth_condition.items():
            left_true_times, left_false_times = temporal_profile
            right_true_times, right_false_times = rightarg_truth_condition[world_id]
            
            # Find intersection while preserving order from left_true_times
            new_true_times = [t for t in left_true_times if t in right_true_times]
            
            # Find union while preserving order and removing duplicates
            new_false_times = sorted(set(left_false_times) | set(right_false_times))
            
            new_truth_condition[world_id] = (new_true_times, new_false_times)
            
        return new_truth_condition

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class OrOperator(syntactic.Operator):
    """Logical disjunction operator that returns true when at least one argument is true.
    
    This operator implements classical logical disjunction (∨). When applied to formulas
    A and B, it returns true when either A or B (or both) are true, and false otherwise.
    
    Key Properties:
        - Commutative: A ∨ B ≡ B ∨ A
        - Associative: (A ∨ B) ∨ C ≡ A ∨ (B ∨ C)
        - Identity: A ∨ ⊥ ≡ A
        - Annihilator: A ∨ ⊤ ≡ ⊤
        - Idempotent: A ∨ A ≡ A
        - Extensional: Value depends only on truth values of arguments
        
    Example:
        If p means "it's raining" and q means "it's cold", then (p ∨ q) means 
        "it's raining or it's cold (or both)"
    """

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Returns true if either argument is true.
        
        Args:
            leftarg: The left argument of the disjunction
            rightarg: The right argument of the disjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics
        return z3.Or(
            semantics.true_at(leftarg, eval_point),
            semantics.true_at(rightarg, eval_point)
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Returns true if both arguments are false.
        
        Args:
            leftarg: The left argument of the disjunction
            rightarg: The right argument of the disjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics
        return z3.And(
            semantics.false_at(leftarg, eval_point),
            semantics.false_at(rightarg, eval_point)
        )

    def find_truth_condition(self, leftarg, rightarg, eval_point):
        """Gets truth-condition for the disjunction of two arguments.
        
        Args:
            leftarg: The left argument of the disjunction
            rightarg: The right argument of the disjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where true_times are the union of both arguments' true times,
                 and false_times are the intersection of both arguments' false times
        """
        leftarg_truth_condition = leftarg.proposition.extension
        rightarg_truth_condition = rightarg.proposition.extension
        new_truth_condition = {}
        
        for world_id, temporal_profile in leftarg_truth_condition.items():
            left_true_times, left_false_times = temporal_profile
            right_true_times, right_false_times = rightarg_truth_condition[world_id]
            
            # Find union of true times
            new_true_times = sorted(set(left_true_times) | set(right_true_times))
            
            # Find intersection of false times
            new_false_times = [t for t in left_false_times if t in right_false_times]
            
            new_truth_condition[world_id] = (new_true_times, new_false_times)
            
        return new_truth_condition
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
############################## EXTREMAL OPERATORS ############################
##############################################################################

class BotOperator(syntactic.Operator):
    """Bottom element of the space of propositions is false at all worlds and times.
    
    This operator implements logical falsity (⊥). It evaluates to false at every world
    and time point in the model structure.
    
    Key Properties:
        - Always evaluates to false regardless of context
        - Identity element for disjunction: ⊥ ∨ A ≡ A
        - Annihilator for conjunction: ⊥ ∧ A ≡ ⊥
        - Negation gives top: ¬⊥ ≡ ⊤
        
    Example:
        ⊥ represents a logical contradiction like "it's raining and not raining"
    """

    name = "\\bot"
    arity = 0

    def true_at(self, eval_point):
        """Returns true if world state != itself (always false)."""
        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        # Get the world array from the world ID
        world_array = self.semantics.world_function(eval_world)
        world_state = z3.Select(world_array, eval_time)
        return world_state != world_state

    def false_at(self, eval_point):
        """Returns true if world state == itself (always true)."""
        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        # Get the world array from the world ID
        world_array = self.semantics.world_function(eval_world)
        world_state = z3.Select(world_array, eval_time)
        return world_state == world_state

    def find_truth_condition(self, eval_point):
        """Returns the extension where all times are false at all worlds.
        
        Args:
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where for each world, no times are true and all times are false
        """
        return self.semantics.all_false

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)



##############################################################################
############################## MODAL OPERATORS ###############################
##############################################################################

class NecessityOperator(syntactic.Operator):
    """Modal operator that evaluates whether a formula holds in all possible worlds.

    This operator implements 'it is necessary that'. It evaluates whether its argument
    holds in all possible worlds at the current time.

    Key Properties:
        - Evaluates truth across all possible worlds at the current time
        - Returns true only if the argument is true in ALL possible worlds
        - Returns false if there exists ANY possible world where the argument is false
        - Dual of possibility: □A ≡ ¬◇¬A
        - Only considers worlds within the valid model structure

    Methods:
        true_at: Returns true if argument holds in all possible worlds
        false_at: Returns true if argument fails in some possible world
        find_truth_condition: Computes temporal profiles for all worlds
        print_method: Displays evaluation across different possible worlds

    Example:
        If p means "it's raining", then □p means "it is necessarily raining"
        (true in all possible worlds at the current time).
    """
    name = "\\Box"
    arity = 1

    def true_at(self, argument, eval_point):
        """Returns true if argument is true in all possible worlds at the eval_time."""
        semantics = self.semantics
        
        # Extract time from eval_point
        eval_time = eval_point["time"]
        
        # The argument must be true in all worlds at the eval_time
        other_world = z3.Int('nec_true_world')
        # For any other_world
        return z3.ForAll(
            other_world,
            z3.Implies(
                z3.And(
                    # If other_world is a valid world
                    semantics.is_world(other_world),
                    # And eval_time is in other_world
                    semantics.is_valid_time_for_world(other_world, eval_time),
                ),
                # Then the argument is true in other_world at the eval_time
                semantics.true_at(argument, {"world": other_world, "time": eval_time})
            )
        )

    def false_at(self, argument, eval_point):
        """Returns true if argument is false in any possible worlds at the eval_time."""
        semantics = self.semantics
        
        # Extract time from eval_point
        eval_time = eval_point["time"]
        
        # The argument must be false in some world at the eval_time
        other_world = z3.Int('nec_true_world')
        # There is some other_world
        return z3.Exists(
            other_world,
            z3.And(
                # Where other_world is a valid world
                semantics.is_world(other_world),
                # And eval_time is in other_world
                semantics.is_valid_time_for_world(other_world, eval_time),
                # And the argument is false in other_world at the eval_time
                semantics.false_at(argument, {"world": other_world, "time": eval_time})
            )
        )

    # TODO: should this use eval_point?
    def find_truth_condition(self, argument, eval_point):
        """Gets truth-condition for: 'It is necessary that: argument'.
        
        Args:
            argument: The argument to apply necessity to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context (not used)
                - "time": The time for evaluation context (not used)
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs.
                 Box A is true at test_time in current_world if:
                 - A is true in any_world in all_worlds at the test_time.
                 And false otherwise.
        """
        semantics = argument.proposition.model_structure.semantics
        all_worlds = argument.proposition.model_structure.world_arrays.keys()
        argument_extension = argument.proposition.extension
        # Initialize result dictionary to eventually return
        new_truth_condition = {}

        # For each world in the model
        for current_world in all_worlds:
            # Get the time interval for this world
            start_time, end_time = semantics.world_time_intervals[current_world]
            # Generate a list of all valid times for this world
            world_time_interval = list(range(start_time, end_time + 1))
            # # Skip worlds that do not include the eval_time
            # if eval_time not in world_time_interval:
            #     continue
            # Initialize lists to store times when necessity is true/false
            true_times, false_times = [], []

            # For each time point in this world's interval
            for test_time in world_time_interval:
                # Check if argument is false at this time in any possible world
                is_false_in_some_world = any(
                    test_time in argument_extension[any_world][1]
                    for any_world in all_worlds
                )
                # If false in any world
                if is_false_in_some_world:
                    # Then the necessity is false at this time
                    false_times.append(test_time)
                else:
                    # Otherwise the necessity is true at this time
                    true_times.append(test_time)

            # Store the temporal profile for this world
            new_truth_condition[current_world] = (true_times, false_times)

        # Return result dictionary
        return new_truth_condition
            
    def print_method(self, argument, eval_point, indent_num, use_colors):
        """Print the modal operator and its argument across all possible worlds.
        """
        # Get the model structure and all world IDs
        model_structure = argument.proposition.model_structure
        
        # Get all worlds (IDs) for evaluation
        all_worlds = list(model_structure.world_arrays.keys())
        
        # Pass the worlds to print_over_worlds
        self.print_over_worlds(argument, eval_point, all_worlds, indent_num, use_colors)
   


##############################################################################
############################## TENSE OPERATORS ###############################
##############################################################################

class FutureOperator(syntactic.Operator):
    """Temporal operator that evaluates whether a formula holds at all future times.

    This operator implements the 'it will always be the case that'. It evaluates
    whether its argument holds at all future times within the eval_world (after the present).

    Key Properties:
        - Evaluates truth across all future times in the current world
        - Returns true only if the argument is true at ALL future times
        - Returns false if there exists ANY future time where the argument is false
        - Vacuously true if there are no future times (e.g., at the end of the timeline)
        - Only considers times within the valid interval for the current world

    Methods:
        true_at: Returns true if argument holds at all future times
        false_at: Returns true if argument fails at some future time
        find_truth_condition: Computes temporal profiles for all worlds
        print_method: Displays evaluation across different time points

    Example:
        If p means "it's raining", then ⏵p means "it will always be raining"
        (from all times after the preset).
    """
    name = "\\Future"
    arity = 1

    def true_at(self, argument, eval_point):
        """Returns true if argument is true at all future times in this world's interval."""
        semantics = self.semantics

        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]

        future_time = z3.Int('future_true_time')
        return semantics.ForAllTime(
            eval_world,
            future_time,
            z3.Implies(
                # Time is in the future of eval_time
                eval_time < future_time,
                # Then the argument is true in the eval_world at the future_time
                semantics.true_at(argument, {"world": eval_world, "time": future_time})
            )
        )
    
    def false_at(self, argument, eval_point):
        """Returns true if argument is false at at least one future time in this world's interval.

        Args:
            argument: The argument to apply the future operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics

        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]

        future_time = z3.Int('future_false_time')
        return semantics.ExistsTime(
            eval_world,
            future_time,
            z3.And(
                # Time is in the future of eval_time
                eval_time < future_time,
                # And the argument is false in the eval_world at the future_time
                semantics.false_at(argument, {"world": eval_world, "time": future_time})
            )
        )
    
    def find_truth_condition(self, argument, eval_point):
        """Gets truth-condition for 'It will always be the case that: argument'.

        ProofChecker Alignment: Quantifies over ALL times in domain D, not just the
        world's interval. Arguments at times outside the world's interval are evaluated
        via semantics.true_at(), which returns FALSE for atoms (via is_valid_time_for_world)
        and evaluates complex formulas (e.g., negations) recursively.

        Args:
            argument: The argument to apply the future operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context

        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where a time is in the true_times if the argument is true in all
                 future times and the time is in the false_times otherwise

        Raises:
            KeyError: If world_time_intervals information is missing for a required world_id.
                      This follows the fail-fast philosophy to make errors explicit.
        """
        model_structure = argument.proposition.model_structure
        semantics = model_structure.semantics
        argument_extension = argument.proposition.extension
        truth_condition = {}

        # Domain D: all valid times (not world-specific)
        # Using semantics.M to get the time domain range (-M+1, M-1)
        all_D_times = list(range(-semantics.M + 1, semantics.M))

        # For any current_world with a temporal_profile of true and false times
        for current_world, temporal_profile in argument_extension.items():
            true_times, false_times = temporal_profile

            # Start with empty lists for past/future times
            new_true_times, new_false_times = [], []

            # Find the time_interval for the current_world (for iteration over evaluation points)
            start_time, end_time = semantics.world_time_intervals[current_world]
            time_interval = list(range(start_time, end_time + 1))

            # Calculate which times the argument always will be true
            for time_point in time_interval:

                # Check if there are any times strictly after this time_point in domain D
                has_future_times = any(any_time > time_point for any_time in all_D_times)

                # If there are no future times in domain D, the Future operator is vacuously true
                if not has_future_times:
                    new_true_times.append(time_point)
                    continue

                # ProofChecker alignment: check all times in D that are > time_point
                # Times outside the world's interval are evaluated via semantics.true_at()
                future_false = False
                for future_time in all_D_times:
                    if future_time > time_point:
                        if future_time in time_interval:
                            # Time is in world's interval: check argument extension
                            if future_time in false_times:
                                future_false = True
                                break
                        else:
                            # Time is outside world's interval: evaluate argument using
                            # semantics.true_at() which handles atoms (FALSE via
                            # is_valid_time_for_world) and complex formulas (recursive eval)
                            truth_expr = semantics.true_at(
                                argument.proposition.sentence,
                                {"world": current_world, "time": future_time}
                            )
                            if not is_true(argument.proposition.z3_model.evaluate(truth_expr)):
                                future_false = True
                                break

                if future_false:
                    new_false_times.append(time_point)
                else:
                    new_true_times.append(time_point)

            # Store the results for this world_id
            truth_condition[current_world] = (new_true_times, new_false_times)

        # Return result dictionary
        return truth_condition

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)


class PastOperator(syntactic.Operator):
    """Temporal operator that evaluates whether an argument holds at all past times.

    This operator implements the 'it has always been the case that'. It evaluates
    whether its argument is true at all past times within the eval_world (before the present).

    Key Properties:
        - Evaluates truth across all past times in the current world
        - Returns true only if the argument is true at ALL past times
        - Returns false if there exists ANY past time where the argument is false
        - Vacuously true if there are no past times (e.g., at the start of the timeline)
        - Only considers times within the valid interval for the current world

    Methods:
        true_at: Returns true if argument holds at all past times
        false_at: Returns true if argument fails at some past time
        find_truth_condition: Computes temporal profiles for all worlds
        print_method: Displays evaluation across different time points

    Example:
        If p means "it's raining", then ⏴p means "it has always been raining"
        (from all times before the present).
    """

    name = "\\Past"
    arity = 1

    def true_at(self, argument, eval_point):
        """Returns true if argument is true at all past times in this world's interval.

        Args:
            argument: The argument to apply the past operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics

        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]

        past_time = z3.Int('past_true_time')
        return semantics.ForAllTime(
            eval_world,
            past_time,
            z3.Implies(
                # The past_time is before the eval_time
                past_time < eval_time,
                # Then the argument is true at the past_time in the eval_world
                semantics.true_at(argument, {"world": eval_world, "time": past_time})
            )
        )

    def false_at(self, argument, eval_point):
        """Returns true if argument is false at at least one past time in this world's interval.

        Args:
            argument: The argument to apply the past operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics

        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]

        past_time = z3.Int('past_false_time')
        return semantics.ExistsTime(
            eval_world,
            past_time,
            z3.And(
                # The past_time is before the eval_time
                past_time < eval_time,
                # And the argument is false at the past_time in the eval_world
                semantics.false_at(argument, {"world": eval_world, "time": past_time})
            )
        )

    def find_truth_condition(self, argument, eval_point):
        """Gets truth-condition for 'It has always been the case that: argument'.

        ProofChecker Alignment: Quantifies over ALL times in domain D, not just the
        world's interval. Arguments at times outside the world's interval are evaluated
        via semantics.true_at(), which returns FALSE for atoms (via is_valid_time_for_world)
        and evaluates complex formulas (e.g., negations) recursively.

        Args:
            argument: The argument to apply the past operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context

        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where a time is in the true_times if the argument is true in all
                 past times and the time is in the false_times otherwise

        Raises:
            KeyError: If world_time_intervals information is missing for a world_id.
                     This follows the fail-fast philosophy to make errors explicit.
        """
        model_structure = argument.proposition.model_structure
        semantics = model_structure.semantics
        argument_extension = argument.proposition.extension
        truth_condition = {}

        # Domain D: all valid times (not world-specific)
        all_D_times = list(range(-semantics.M + 1, semantics.M))

        # For any current_world with a temporal_profile of true and false times
        for current_world, temporal_profile in argument_extension.items():
            true_times, false_times = temporal_profile

            # Start with empty lists for past/future times
            new_true_times, new_false_times = [], []

            # Find the time_interval for the current_world (for iteration over evaluation points)
            start_time, end_time = semantics.world_time_intervals[current_world]
            time_interval = list(range(start_time, end_time + 1))

            # Calculate which times the argument always has been true
            for time_point in time_interval:

                # Check if there are any times strictly before this time_point in domain D
                has_past_times = any(any_time < time_point for any_time in all_D_times)

                # If there are no past times in domain D, the Past operator is vacuously true
                if not has_past_times:
                    new_true_times.append(time_point)
                    continue

                # ProofChecker alignment: check all times in D that are < time_point
                # Times outside the world's interval are evaluated via semantics.true_at()
                past_false = False
                for past_time in all_D_times:
                    if past_time < time_point:
                        if past_time in time_interval:
                            # Time is in world's interval: check argument extension
                            if past_time in false_times:
                                past_false = True
                                break
                        else:
                            # Time is outside world's interval: evaluate argument using
                            # semantics.true_at() which handles atoms (FALSE via
                            # is_valid_time_for_world) and complex formulas (recursive eval)
                            truth_expr = semantics.true_at(
                                argument.proposition.sentence,
                                {"world": current_world, "time": past_time}
                            )
                            if not is_true(argument.proposition.z3_model.evaluate(truth_expr)):
                                past_false = True
                                break

                if past_false:
                    new_false_times.append(time_point)
                else:
                    new_true_times.append(time_point)

            # Store the results for this world_id
            truth_condition[current_world] = (new_true_times, new_false_times)

        # Return result dictionary
        return truth_condition

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print the sentence over all time points.

        Args:
            sentence_obj: The sentence to print
            eval_point: The evaluation point (world ID and time)
            indent_num: The indentation level
            use_colors: Whether to use colors in output
        """
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)


class UntilOperator(syntactic.Operator):
    """Temporal operator U(event, guard): event holds at some future time s > t,
    and guard holds for all times in the open interval (t, s).

    This operator implements the temporal Until operator following the Burgess convention
    and ProofChecker semantics. U(event, guard) is true at time t if there exists a
    strictly future time s where the event holds, and the guard holds at all times
    strictly between t and s.

    Key Properties:
        - Strict witness: The event time s must be strictly greater than evaluation time t
        - Open guard interval: Guard must hold for all r in (t, s), excluding endpoints
        - Current time excluded: Guard does NOT need to hold at time t
        - Witness time excluded: Guard does NOT need to hold at time s
        - Vacuously false at last time: No future times means no witness can exist
        - Burgess convention: untl(event, guard) - event is what eventually happens

    Semantics (from ProofChecker Truth.lean):
        U(phi, psi) is true at t iff:
        exists s > t: phi(s) AND forall r in (t,s): psi(r)

    Methods:
        true_at: Returns true if there exists a future witness with guard holding in between
        false_at: Returns true if no such witness exists
        find_truth_condition: Computes temporal profiles for all worlds
        print_method: Displays evaluation across different time points

    Example:
        If p means "the train arrives" and q means "waiting", then U(p, q) means
        "the train will arrive and until then we are waiting"
    """

    name = "\\Until"
    arity = 2

    def true_at(self, event_arg, guard_arg, eval_point):
        """Returns true if Until condition is satisfied: exists witness s > t where
        event holds at s and guard holds for all times in (t, s).

        Args:
            event_arg: The event formula (what eventually holds)
            guard_arg: The guard formula (what holds until then)
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context

        Returns:
            Z3 expression representing the Until truth condition with nested quantifiers
        """
        semantics = self.semantics

        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]

        # Create uniquely named time variables to avoid collision
        witness_time = z3.Int('until_witness_time')
        guard_time = z3.Int('until_guard_time')

        # U(event, guard) is true at t iff:
        # exists s > t: event(s) AND forall r in (t,s): guard(r)
        return semantics.ExistsTime(
            eval_world,
            witness_time,
            z3.And(
                # Strict witness: s > t
                eval_time < witness_time,
                # Event holds at witness time
                semantics.true_at(event_arg, {"world": eval_world, "time": witness_time}),
                # Guard holds for all r in the open interval (t, s)
                semantics.ForAllTime(
                    eval_world,
                    guard_time,
                    z3.Implies(
                        z3.And(eval_time < guard_time, guard_time < witness_time),
                        semantics.true_at(guard_arg, {"world": eval_world, "time": guard_time})
                    )
                )
            )
        )

    def false_at(self, event_arg, guard_arg, eval_point):
        """Returns true if Until condition is not satisfied: for all potential witnesses,
        either event fails or guard fails at some intermediate point.

        Args:
            event_arg: The event formula (what eventually holds)
            guard_arg: The guard formula (what holds until then)
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context

        Returns:
            Z3 expression representing the negation of Until condition
        """
        semantics = self.semantics

        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]

        # Create uniquely named time variables
        witness_time = z3.Int('until_false_witness_time')
        guard_time = z3.Int('until_false_guard_time')

        # U(event, guard) is false at t iff:
        # forall s > t: event is false at s OR exists r in (t,s): guard is false at r
        return semantics.ForAllTime(
            eval_world,
            witness_time,
            z3.Implies(
                eval_time < witness_time,
                z3.Or(
                    # Event fails at potential witness
                    semantics.false_at(event_arg, {"world": eval_world, "time": witness_time}),
                    # Or guard fails at some intermediate point
                    semantics.ExistsTime(
                        eval_world,
                        guard_time,
                        z3.And(
                            eval_time < guard_time,
                            guard_time < witness_time,
                            semantics.false_at(guard_arg, {"world": eval_world, "time": guard_time})
                        )
                    )
                )
            )
        )

    def find_truth_condition(self, event_arg, guard_arg, eval_point):
        """Computes the extension for Until operator by checking each time point.

        ProofChecker Alignment: Considers all times in domain D. Arguments at times
        outside the world's interval are evaluated via semantics.true_at(), which returns
        FALSE for atoms (via is_valid_time_for_world) and evaluates complex formulas
        (e.g., negations) recursively.

        For each time t, Until is true if there exists a witness time s > t where:
        - event holds at s
        - guard holds for all times in the open interval (t, s)

        Args:
            event_arg: The event formula (what eventually holds)
            guard_arg: The guard formula (what holds until then)
            eval_point: Dictionary containing evaluation parameters

        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs
        """
        model_structure = event_arg.proposition.model_structure
        semantics = model_structure.semantics
        event_extension = event_arg.proposition.extension
        guard_extension = guard_arg.proposition.extension
        truth_condition = {}

        # Domain D: all valid times (not world-specific)
        all_D_times = list(range(-semantics.M + 1, semantics.M))

        # For each world in the model
        for world_id in event_extension.keys():
            event_true_times = event_extension[world_id][0]
            guard_true_times = guard_extension[world_id][0]

            # Get the time interval for this world
            start_time, end_time = semantics.world_time_intervals[world_id]
            time_interval = list(range(start_time, end_time + 1))

            true_times, false_times = [], []

            # For each time point t in this world
            for t in time_interval:
                # Check if Until holds at time t
                found_witness = False

                # Search for a witness s > t where event holds
                # Note: Witnesses are limited to the world's interval for event evaluation
                for s in range(t + 1, end_time + 1):
                    if s in event_true_times:
                        # Check if guard holds for all r in open interval (t, s) within domain D
                        # ProofChecker alignment: times outside world's interval evaluated via true_at()
                        guard_ok = True
                        for r in all_D_times:
                            if t < r < s:
                                if r in time_interval:
                                    # Time inside world's interval: check guard extension
                                    if r not in guard_true_times:
                                        guard_ok = False
                                        break
                                else:
                                    # Time outside world's interval: evaluate guard using
                                    # semantics.true_at() which handles atoms (FALSE via
                                    # is_valid_time_for_world) and complex formulas (recursive eval)
                                    truth_expr = semantics.true_at(
                                        guard_arg.proposition.sentence,
                                        {"world": world_id, "time": r}
                                    )
                                    if not is_true(guard_arg.proposition.z3_model.evaluate(truth_expr)):
                                        guard_ok = False
                                        break
                        if guard_ok:
                            found_witness = True
                            break

                if found_witness:
                    true_times.append(t)
                else:
                    false_times.append(t)

            truth_condition[world_id] = (true_times, false_times)

        return truth_condition

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print the Until operator evaluation across different time points.

        Args:
            sentence_obj: The sentence to print
            eval_point: The evaluation point (world ID and time)
            indent_num: The indentation level
            use_colors: Whether to use colors in output
        """
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)


class SinceOperator(syntactic.Operator):
    """Temporal operator S(event, guard): event held at some past time s < t,
    and guard held for all times in the open interval (s, t).

    This operator implements the temporal Since operator following the Burgess convention
    and ProofChecker semantics. S(event, guard) is true at time t if there exists a
    strictly past time s where the event held, and the guard held at all times
    strictly between s and t.

    Key Properties:
        - Strict witness: The event time s must be strictly less than evaluation time t
        - Open guard interval: Guard must hold for all r in (s, t), excluding endpoints
        - Current time excluded: Guard does NOT need to hold at time t
        - Witness time excluded: Guard does NOT need to hold at time s
        - Vacuously false at first time: No past times means no witness can exist
        - Burgess convention: snce(event, guard) - event is what previously happened

    Semantics (from ProofChecker Truth.lean):
        S(phi, psi) is true at t iff:
        exists s < t: phi(s) AND forall r in (s,t): psi(r)

    Methods:
        true_at: Returns true if there exists a past witness with guard holding in between
        false_at: Returns true if no such witness exists
        find_truth_condition: Computes temporal profiles for all worlds
        print_method: Displays evaluation across different time points

    Example:
        If p means "the alarm rang" and q means "sleeping", then S(p, q) means
        "the alarm rang and since then we have been sleeping" (actually: "and before
        that we were sleeping")
    """

    name = "\\Since"
    arity = 2

    def true_at(self, event_arg, guard_arg, eval_point):
        """Returns true if Since condition is satisfied: exists witness s < t where
        event held at s and guard held for all times in (s, t).

        Args:
            event_arg: The event formula (what previously held)
            guard_arg: The guard formula (what held since then)
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context

        Returns:
            Z3 expression representing the Since truth condition with nested quantifiers
        """
        semantics = self.semantics

        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]

        # Create uniquely named time variables to avoid collision
        witness_time = z3.Int('since_witness_time')
        guard_time = z3.Int('since_guard_time')

        # S(event, guard) is true at t iff:
        # exists s < t: event(s) AND forall r in (s,t): guard(r)
        return semantics.ExistsTime(
            eval_world,
            witness_time,
            z3.And(
                # Strict witness: s < t
                witness_time < eval_time,
                # Event held at witness time
                semantics.true_at(event_arg, {"world": eval_world, "time": witness_time}),
                # Guard held for all r in the open interval (s, t)
                semantics.ForAllTime(
                    eval_world,
                    guard_time,
                    z3.Implies(
                        z3.And(witness_time < guard_time, guard_time < eval_time),
                        semantics.true_at(guard_arg, {"world": eval_world, "time": guard_time})
                    )
                )
            )
        )

    def false_at(self, event_arg, guard_arg, eval_point):
        """Returns true if Since condition is not satisfied: for all potential witnesses,
        either event failed or guard failed at some intermediate point.

        Args:
            event_arg: The event formula (what previously held)
            guard_arg: The guard formula (what held since then)
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context

        Returns:
            Z3 expression representing the negation of Since condition
        """
        semantics = self.semantics

        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]

        # Create uniquely named time variables
        witness_time = z3.Int('since_false_witness_time')
        guard_time = z3.Int('since_false_guard_time')

        # S(event, guard) is false at t iff:
        # forall s < t: event was false at s OR exists r in (s,t): guard was false at r
        return semantics.ForAllTime(
            eval_world,
            witness_time,
            z3.Implies(
                witness_time < eval_time,
                z3.Or(
                    # Event failed at potential witness
                    semantics.false_at(event_arg, {"world": eval_world, "time": witness_time}),
                    # Or guard failed at some intermediate point
                    semantics.ExistsTime(
                        eval_world,
                        guard_time,
                        z3.And(
                            witness_time < guard_time,
                            guard_time < eval_time,
                            semantics.false_at(guard_arg, {"world": eval_world, "time": guard_time})
                        )
                    )
                )
            )
        )

    def find_truth_condition(self, event_arg, guard_arg, eval_point):
        """Computes the extension for Since operator by checking each time point.

        ProofChecker Alignment: Considers all times in domain D. Arguments at times
        outside the world's interval are evaluated via semantics.true_at(), which returns
        FALSE for atoms (via is_valid_time_for_world) and evaluates complex formulas
        (e.g., negations) recursively.

        For each time t, Since is true if there exists a witness time s < t where:
        - event held at s
        - guard held for all times in the open interval (s, t)

        Args:
            event_arg: The event formula (what previously held)
            guard_arg: The guard formula (what held since then)
            eval_point: Dictionary containing evaluation parameters

        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs
        """
        model_structure = event_arg.proposition.model_structure
        semantics = model_structure.semantics
        event_extension = event_arg.proposition.extension
        guard_extension = guard_arg.proposition.extension
        truth_condition = {}

        # Domain D: all valid times (not world-specific)
        all_D_times = list(range(-semantics.M + 1, semantics.M))

        # For each world in the model
        for world_id in event_extension.keys():
            event_true_times = event_extension[world_id][0]
            guard_true_times = guard_extension[world_id][0]

            # Get the time interval for this world
            start_time, end_time = semantics.world_time_intervals[world_id]
            time_interval = list(range(start_time, end_time + 1))

            true_times, false_times = [], []

            # For each time point t in this world
            for t in time_interval:
                # Check if Since holds at time t
                found_witness = False

                # Search for a witness s < t where event held
                # Note: Witnesses are limited to the world's interval for event evaluation
                for s in range(start_time, t):
                    if s in event_true_times:
                        # Check if guard held for all r in open interval (s, t) within domain D
                        # ProofChecker alignment: times outside world's interval evaluated via true_at()
                        guard_ok = True
                        for r in all_D_times:
                            if s < r < t:
                                if r in time_interval:
                                    # Time inside world's interval: check guard extension
                                    if r not in guard_true_times:
                                        guard_ok = False
                                        break
                                else:
                                    # Time outside world's interval: evaluate guard using
                                    # semantics.true_at() which handles atoms (FALSE via
                                    # is_valid_time_for_world) and complex formulas (recursive eval)
                                    truth_expr = semantics.true_at(
                                        guard_arg.proposition.sentence,
                                        {"world": world_id, "time": r}
                                    )
                                    if not is_true(guard_arg.proposition.z3_model.evaluate(truth_expr)):
                                        guard_ok = False
                                        break
                        if guard_ok:
                            found_witness = True
                            break

                if found_witness:
                    true_times.append(t)
                else:
                    false_times.append(t)

            truth_condition[world_id] = (true_times, false_times)

        return truth_condition

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print the Since operator evaluation across different time points.

        Args:
            sentence_obj: The sentence to print
            eval_point: The evaluation point (world ID and time)
            indent_num: The indentation level
            use_colors: Whether to use colors in output
        """
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)


##############################################################################
######################## DEFINED EXTENSIONAL OPERATORS #######################
##############################################################################

class ConditionalOperator(syntactic.DefinedOperator):
    """Material conditional operator that returns true unless the antecedent is true and consequent false.
    
    This operator implements classical material implication (→). When applied to formulas
    A and B, it returns true when either A is false or B is true, and false otherwise.
    
    Key Properties:
        - Defined as: A → B ≡ ¬A ∨ B
        - Vacuously true when antecedent is false
        - Extensional: Value depends only on truth values of arguments
        - Not equivalent to natural language "if-then"
        - Supports modus ponens: From A and A → B, infer B
        - Supports modus tollens: From ¬B and A → B, infer ¬A
        
    Example:
        If p means "it's raining" and q means "the ground is wet", then (p → q) means 
        "if it's raining then the ground is wet" (in the material sense)
    """

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):  # type: ignore
        return [OrOperator, [NegationOperator, leftarg], rightarg]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BiconditionalOperator(syntactic.DefinedOperator):
    """Material biconditional operator that returns true when both arguments have the same truth value.
    
    This operator implements classical material biconditional (↔). When applied to formulas
    A and B, it returns true when A and B have the same truth value (both true or both false).
    
    Key Properties:
        - Defined as: A ↔ B ≡ (A → B) ∧ (B → A)
        - Commutative: A ↔ B ≡ B ↔ A
        - Reflexive: A ↔ A is a tautology
        - Extensional: Value depends only on truth values of arguments
        - Not equivalent to natural language "if and only if"
        - Represents logical equivalence between formulas
        
    Example:
        If p means "it's raining" and q means "there are clouds", then (p ↔ q) means 
        "it's raining if and only if there are clouds" (in the material sense)
    """

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
####################### DEFINED EXTREMAL OPERATORS ###########################
##############################################################################

class TopOperator(syntactic.DefinedOperator):
    """Top element of the space of propositions is true at all worlds and times.
    
    This operator implements logical truth (⊤). It evaluates to true at every world
    and time point in the model structure.
    
    Key Properties:
        - Always evaluates to true regardless of context
        - Identity element for conjunction: ⊤ ∧ A ≡ A
        - Annihilator for disjunction: ⊤ ∨ A ≡ ⊤
        - Negation gives bottom: ¬⊤ ≡ ⊥
        
    Example:
        ⊤ represents a logical tautology like "it's raining or not raining"
    """

    name = "\\top"
    arity = 0

    def derived_definition(self):  # type: ignore
        """Define top in terms of negation and bottom."""
        return [NegationOperator, [BotOperator]]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)



##############################################################################
####################### DEFINED INTENSIONAL OPERATORS ########################
##############################################################################

class DefPossibilityOperator(syntactic.DefinedOperator):
    """Modal operator that evaluates whether a formula holds in at least one possible world.

    This operator implements 'it is possible that'. It evaluates whether its argument
    holds in at least one possible world at the current time.

    Key Properties:
        - Evaluates truth across all possible worlds at the current time
        - Returns true if the argument is true in ANY possible world
        - Returns false if the argument is false in ALL possible worlds
        - Defined as the dual of necessity: ◇A ≡ ¬□¬A
        - Only considers worlds within the valid model structure

    Methods:
        derived_definition: Defines possibility in terms of negation and necessity
        print_method: Displays evaluation across different possible worlds

    Example:
        If p means "it's raining", then ◇p means "it is possible that it's raining"
        (true in at least one possible world at the current time).
    """
    name = "\\Diamond"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        """Define possibility in terms of negation and necessity."""
        return [NegationOperator, [NecessityOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print the possibility operator and its argument across all possible worlds.
        """
        # Get the model structure and all world IDs
        model_structure = sentence_obj.proposition.model_structure
        
        # Get all worlds (IDs) for evaluation
        all_worlds = list(model_structure.world_arrays.keys())
        
        # Pass the worlds to print_over_worlds
        self.print_over_worlds(sentence_obj, eval_point, all_worlds, indent_num, use_colors)



##############################################################################
######################### DEFINED TEMPORAL OPERATORS #########################
##############################################################################

class DefFutureOperator(syntactic.DefinedOperator):
    """Temporal operator that evaluates whether a formula holds at some future time.

    This operator implements 'it will at some point be the case that'. It evaluates
    whether its argument is true at at least one future time within the eval_world
    (after the present).

    Key Properties:
        - Evaluates truth across all future times in the current world
        - Returns true if the argument is true at ANY future time
        - Returns false if the argument is false at ALL future times
        - Defined as the dual of future necessity: ⏵A ≡ ¬⏵¬A
        - Only considers times within the valid interval for the current world

    Methods:
        derived_definition: Defines future possibility in terms of negation and future necessity
        print_method: Displays evaluation across different time points

    Example:
        If p means "it's raining", then ⏵p means "it will at some point be raining"
        (true at at least one future time).
    """

    name = "\\future"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [NegationOperator, [FutureOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)


class DefPastOperator(syntactic.DefinedOperator):

    name = "\\past"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [NegationOperator, [PastOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)




bimodal_operators = syntactic.OperatorCollection(
    # extensional operators
    NegationOperator,
    AndOperator,
    OrOperator,

    # extremal operators
    TopOperator,

    # modal operators
    NecessityOperator,

    # tense operators
    FutureOperator,
    PastOperator,
    UntilOperator,
    SinceOperator,

    # defined operators
    ConditionalOperator,
    BiconditionalOperator,
    BotOperator,
    DefPossibilityOperator,
    DefFutureOperator,
    DefPastOperator,
)

