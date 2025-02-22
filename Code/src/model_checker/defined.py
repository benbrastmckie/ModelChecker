from . import syntactic

from .primitive import (
    AndOperator, NegationOperator, OrOperator, # extensional
    TopOperator, BotOperator, # top and bottom zero-place operators
    IdentityOperator, GroundOperator, EssenceOperator, # constitutive
    RelevanceOperator, # relevance
    CounterfactualOperator, # counterfactual
    ImpositionOperator,
    NecessityOperator, PossibilityOperator, # modal
)

##############################################################################
######################## DEFINED EXTENSIONAL OPERATORS #######################
##############################################################################

class ConditionalOperator(syntactic.DefinedOperator):

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [OrOperator, [NegationOperator, leftarg], rightarg]
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_world, indent_num, use_colors)


class BiconditionalOperator(syntactic.DefinedOperator):

    name = "\\leftrightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        right_to_left = [ConditionalOperator, leftarg, rightarg]
        left_to_right = [ConditionalOperator, rightarg, leftarg]
        return [AndOperator, right_to_left, left_to_right]
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_world, indent_num, use_colors)



##############################################################################
####################### DEFINED CONSTITUTIVE OPERATORS #######################
##############################################################################

class DefGroundOperator(syntactic.DefinedOperator):

    name = "\\ground"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [IdentityOperator, [OrOperator, leftarg, rightarg], rightarg]

    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_world, indent_num, use_colors)


class DefEssenceOperator(syntactic.DefinedOperator):

    name = "\\essence"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [IdentityOperator, [AndOperator, leftarg, rightarg], rightarg]

    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_world, indent_num, use_colors)



##############################################################################
###################### DEFINED COUNTERFACTUAL OPERATORS ######################
##############################################################################

class MightCounterfactualOperator(syntactic.DefinedOperator):

    name = "\\diamondright"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [
            NegationOperator, [
                CounterfactualOperator,
                leftarg,
                [NegationOperator, rightarg]
            ]
        ]

    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        is_alt = self.semantics.calculate_alternative_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_alt(left_argument_verifiers, eval_world, model_structure)
        self.print_over_worlds(sentence_obj, eval_world, alt_worlds, indent_num, use_colors)



class MightImpositionOperator(syntactic.DefinedOperator):

    name = "\\could"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [
            NegationOperator, [
                ImpositionOperator,
                leftarg,
                [NegationOperator, rightarg]
            ]
        ]

    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        is_outcome = self.semantics.calculate_outcome_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_outcome(left_argument_verifiers, eval_world, model_structure)
        self.print_over_worlds(sentence_obj, eval_world, alt_worlds, indent_num, use_colors)



##############################################################################
####################### DEFINED INTENSIONAL OPERATORS ########################
##############################################################################

class DefNecessityOperator(syntactic.DefinedOperator):

    name = "\\necessary"
    arity = 1

    def derived_definition(self, rightarg):
        # NOTE: TopOperator is not a list like the others, so [TopOperator]
        return [CounterfactualOperator, [TopOperator], rightarg]
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, eval_world, all_worlds, indent_num, use_colors)


class DefPossibilityOperator(syntactic.DefinedOperator):

    name = "\\possible"
    arity = 1

    def derived_definition(self, arg):
        return [NegationOperator, [NecessityOperator, [NegationOperator, arg]]]
        # return [NegationOperator, [DefNecessityOperator, [NegationOperator, arg]]]
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, eval_world, all_worlds, indent_num, use_colors)


class DefPossibilityOperator2(syntactic.DefinedOperator):

    name = "\\possible2" # note name change
    arity = 1

    def derived_definition(self, arg):
        return [MightCounterfactualOperator, [TopOperator], arg]
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, eval_world, all_worlds, indent_num, use_colors)


##############################################################################
####################### CIRCULAR DEFINITIONS TESTING #########################
##############################################################################

class CircNecessityOperator(syntactic.DefinedOperator):
    """Defined to check for definitional loops."""

    name = "\\circNec"
    arity = 1

    def derived_definition(self, arg):
        return [NegationOperator, [CircPossibilityOperator, [NegationOperator, arg]]]
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, eval_world, all_worlds, indent_num, use_colors)


class CircPossibilityOperator(syntactic.DefinedOperator):
    """Defined to check for definitional loops."""

    name = "\\circPoss"
    arity = 1

    def derived_definition(self, arg):
        return [NegationOperator, [CircNecessityOperator, [NegationOperator, arg]]]
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, eval_world, all_worlds, indent_num, use_colors)


class CircNecessityOperator1(syntactic.DefinedOperator):
    """Defined to check for definitional loops."""

    name = "\\circNec1"
    arity = 1

    def derived_definition(self, arg):
        return [NegationOperator, [CircPossibilityOperator1, [NegationOperator, arg]]]
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, eval_world, all_worlds, indent_num, use_colors)


class CircPossibilityOperator1(syntactic.DefinedOperator):
    """Defined to check for definitional loops."""

    name = "\\circPoss1"
    arity = 1

    def derived_definition(self, arg):
        return [NegationOperator, [CircNecessityOperator2, [NegationOperator, arg]]]
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, eval_world, all_worlds, indent_num, use_colors)


class CircNecessityOperator2(syntactic.DefinedOperator):
    """Defined to check for definitional loops."""

    name = "\\circNec2"
    arity = 1

    def derived_definition(self, arg):
        return [NegationOperator, [CircPossibilityOperator2, [NegationOperator, arg]]]
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, eval_world, all_worlds, indent_num, use_colors)


class CircPossibilityOperator2(syntactic.DefinedOperator):
    """Defined to check for definitional loops."""

    name = "\\circPoss2"
    arity = 1

    def derived_definition(self, arg):
        return [NegationOperator, [CircNecessityOperator1, [NegationOperator, arg]]]
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, eval_world, all_worlds, indent_num, use_colors)
