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

        # # Add debug print
        # print(f"\nDEBUG: Evaluating necessity operator")
        # print(f"Argument: {argument}")
        # print(f"Eval world: {eval_world}")
        # print(f"Eval time: {eval_time}")
        
        # Quantify over all worlds without any accessibility restrictions
        result = z3.ForAll(
            world_id,
            z3.Implies(
                # If world_id is used in the world_function
                semantics.world_exists(world_id, eval_time),
                # Then world_id makes the argument true
                semantics.true_at(argument, semantics.world_function(world_id), eval_time)
            )
        )
        # print(f"Necessity result: {result}")
        return result

    def false_at(self, argument, eval_world, eval_time):
        """Returns true if argument is false in at least one possible world at eval_time.
        It is important that no restrictions are placed on accessibility between worlds."""
        semantics = self.semantics
        world_id = z3.Int('nec_false_world_id')
        # Allow any world to serve as a counterexample without accessibility restrictions
        return z3.Exists(
            world_id,
            z3.And(
                # The world_id is used in the world_function
                semantics.world_exists(world_id, eval_time),
                # And world_id makes the argument false
                semantics.false_at(argument, semantics.world_function(world_id), eval_time)
            )
        )

    # def true_at(self, argument, eval_world, eval_time):
    #     """Returns true if argument is true in all worlds at eval_time."""
    #     semantics = self.semantics
    #     # Create a list of truth conditions for each world array
    #     truth_conditions = []
    #     for world_array in semantics.all_worlds.values():
    #         truth_conditions.append(semantics.true_at(argument, world_array, eval_time))
    #     # Return conjunction of all truth conditions
    #     return z3.And(truth_conditions)
    #
    # def false_at(self, argument, eval_world, eval_time):
    #     """Returns true if argument is false in at least one world at eval_time."""
    #     semantics = self.semantics
    #     # Create a list of false conditions for each world array
    #     false_conditions = []
    #     for world_array in semantics.all_worlds.values():
    #         false_conditions.append(semantics.false_at(argument, world_array, eval_time))
    #     # Return disjunction of all false conditions
    #     return z3.Or(false_conditions)

    # def true_at(self, argument, eval_world, eval_time):
    #     semantics = self.semantics
    #     nec_true_world_id = z3.Int('nec_true_world_id')
    #     return z3.ForAll(
    #         nec_true_world_id,
    #         z3.Implies(
    #             nec_true_world_id >= 0,  # Only consider non-negative world IDs
    #             semantics.true_at(argument, semantics.world_function(nec_true_world_id), eval_time)
    #         )
    #     )
    #
    # def false_at(self, argument, eval_world, eval_time):
    #     semantics = self.semantics
    #     nec_false_world_id = z3.Int('nec_false_world_id')
    #     return z3.Exists(
    #         nec_false_world_id,
    #         z3.And(
    #             nec_false_world_id >= 0,  # Only consider non-negative world IDs
    #             semantics.false_at(argument, semantics.world_function(nec_false_world_id), eval_time)
    #         )
    #     )

    # def true_at(self, argument, eval_world, eval_time):
    #     """Returns true if argument is true in all worlds at eval_time."""
    #     semantics = self.semantics
    #     # Create a list of truth conditions for each world array
    #     truth_conditions = []
    #     for world_array in semantics.all_worlds.values():
    #         truth_conditions.append(semantics.true_at(argument, world_array, eval_time))
    #     # Return conjunction of all truth conditions
    #     return z3.And(truth_conditions)
    #
    # def false_at(self, argument, eval_world, eval_time):
    #     """Returns true if argument is false in at least one world at eval_time."""
    #     semantics = self.semantics
    #     # Create a list of false conditions for each world array
    #     false_conditions = []
    #     for world_array in semantics.all_worlds.values():
    #         false_conditions.append(semantics.false_at(argument, world_array, eval_time))
    #     # Return disjunction of all false conditions
    #     return z3.Or(false_conditions)

    # # TODO: remove quantification over times once abundance constraint is added
    # def true_at(self, argument, eval_world, eval_time):
    #     semantics = self.semantics
    #     nec_true_world_id = z3.Int('nec_true_world_id')
    #     nec_true_time = z3.Int('nec_true_time')
    #     return z3.ForAll(
    #         [nec_true_world_id, nec_true_time],
    #         z3.Implies(
    #             z3.And(
    #                 nec_true_world_id >= 0,
    #                 nec_true_time >= 0,
    #                 nec_true_time < semantics.M
    #             ),
    #             semantics.true_at(argument, semantics.world_function(nec_true_world_id), nec_true_time)
    #         )
    #     )
    # 
    # def false_at(self, argument, eval_world, eval_time):
    #     semantics = self.semantics
    #     nec_false_world_id = z3.Int('nec_false_world_id')
    #     nec_false_time = z3.Int('nec_false_time')
    #     return z3.Exists(
    #         [nec_false_world_id, nec_false_time],
    #         z3.And(
    #             nec_false_world_id >= 0,
    #             nec_false_time >= 0,
    #             nec_false_time < semantics.M,
    #             semantics.false_at(argument, semantics.world_function(nec_false_world_id), nec_false_time)
    #         )
    #     )

    # def false_at(self, argument, eval_world, eval_time):
    #     semantics = self.semantics
    #     nec_false_world_id = z3.Int('nec_false_world_id')
    #     # tau = z3.Array('true_world_tau', semantics.TimeSort, semantics.WorldStateSort)
    #     # x = z3.Int("frame_time_x frame_time_y")
    #     # Only consider worlds that satisfy frame constraints
    #     return z3.Exists(
    #         nec_false_world_id,
    #         # z3.And(
    #     # - If argument is false anywhere (Y_F not empty), necessity is false everywhere
    #     # - If argument is true everywhere (Y_F empty), necessity is true everywhere
    #     if Y_F:
    #         return set(), all_world_states  # False everywhere
    #     return all_world_states, set()  # True everywhere

        # FROM BEFORE
        # Y_V, Y_F = argument.proposition.find_proposition()
        # all_world_states = set(self.semantics.all_bits)
        # print(f"VER {Y_V} FAL {Y_F} ALL {all_world_states}")
        #
        # # Convert list to tuple so it can be added to a set
        # Z_V = set() if Y_F else all_world_states
        # Z_F = all_world_states if Y_F else set()
        # return Z_V, Z_F

        # FROM BEFORE BEFORE
        # evaluate = argument.proposition.model_structure.z3_model.evaluate
        # if bool(evaluate(self.true_at(argument, eval_world, eval_time))):
        #     return {self.semantics.all_bits}, set()

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
        # Get model structure and z3 model
        model_structure = argument.proposition.model_structure
        all_worlds = model_structure.all_worlds.values()
        # print(f"EVAL WORLD {eval_point['world']} EVAL TIME {eval_point['time']}")
        # world_mappings = model_structure.world_mappings
        # z3_model = model_structure.z3_model
        #
        # main_world = model_structure.main_world
        # main_time = model_structure.main_time
        # z3_main_world = z3_model.evaluate(main_world)
        # z3_main_time = z3_model.evaluate(main_time)
        # print(f"MAIN WORLD {z3_main_world} MAIN TIME {z3_main_time}")
        # z3_main_state = z3_model.evaluate(z3_main_world[z3_main_time])
        # print(f"MAIN STATE {z3_main_state}")

        # eval_time = eval_point["time"]
        #
        # # Print all_worlds contents
        # print("\nWorlds from all_worlds:")
        # for i, world in enumerate(all_worlds):
        #     concrete_time = z3_model.evaluate(eval_time)
        #     concrete_array = z3_model.evaluate(world)
        #     world_state = z3_model.evaluate(concrete_array[concrete_time])
        #     print(f"WORLD {world} TYPE {type(world)}")
        #     print(f"World {i}: {world_state}")
            
        self.print_over_worlds(argument, eval_point, all_worlds, indent_num, use_colors)
   
    # def print_method(self, argument, eval_point, indent_num, use_colors):
    #     """Print the necessity operator's evaluation by examining all accessible worlds
    #     through the world_function mapping."""
    #     model_structure = argument.proposition.model_structure
    #     z3_model = model_structure.z3_model
    #     eval_time = eval_point["time"]
    #     
    #     # Collect accessible worlds through world_function
    #     accessible_worlds = []
    #     for i in range(model_structure.semantics.N):  # N is number of worlds
    #         try:
    #             world = model_structure.semantics.world_function(i)
    #             concrete_array = z3_model.evaluate(world)
    #             accessible_worlds.append(concrete_array)
    #         except z3.Z3Exception:
    #             continue  # Skip undefined world mappings
    #             
    #     self.print_over_worlds(argument, eval_point, accessible_worlds, indent_num, use_colors)

##############################################################################
############################## TENSE OPERATORS ###############################
##############################################################################

class FutureOperator(syntactic.Operator):
    name = "\\Future"
    arity = 1

    def true_at(self, argument, eval_world, eval_time):
        semantics = self.semantics
        x = z3.Ints('true_time_x')
        return z3.ForAll(
            x,
            z3.Implies(
                eval_time < x,
                semantics.true_at(argument, eval_world, x),
            )
        )
    
    def false_at(self, argument, eval_world, eval_time):
        semantics = self.semantics
        x = z3.Ints('false_time_x')
        return z3.Exists(
            x,
            z3.And(
                eval_time < x,
                semantics.false_at(argument, eval_world, x),
            )
        )
    
    # TODO: replace with (world, time) pairs, calling this the extension
    def find_truth_condition(self, argument, eval_world, eval_time):
        Y_V, Y_F = argument.proposition.find_proposition()
        Z_V = {self.semantics.all_bits} if Y_V else set()
        Z_F = set() if Y_F else {self.semantics.all_bits}
        return Z_V, Z_F
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
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
    
    def print_method(self, argument, eval_point, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = argument.proposition.model_structure.all_worlds.values()

        # world_functions = argument.proposition.model_structure.world_mappings
        # for world in world_functions:
        #     print(f"WORLD {world} TYPE {type(world)}")

        # eval_time = eval_point["time"]
        # z3_model = argument.proposition.model_structure.z3_model

        # print("\nDEBUG: World States at time =", eval_time)
        # for i, world in enumerate(all_worlds):
        #     # Evaluate the time first to get concrete value
        #     concrete_time = z3_model.evaluate(eval_time)
        #     # Then evaluate the array to get concrete array
        #     concrete_array = z3_model.evaluate(world)
        #     # Finally evaluate the world state at that time
        #     world_state = z3_model.evaluate(concrete_array[concrete_time])
        #     print(f"World {i}: {world_state}")
        # print()  # Empty line for better readability

        self.print_over_worlds(argument, eval_point, all_worlds, indent_num, use_colors)

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

    # defined operators
    ConditionalOperator,
    BiconditionalOperator,
    DefPossibilityOperator,
)

