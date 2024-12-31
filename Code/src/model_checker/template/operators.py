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
    """doc string place holder"""

    name = "\\neg"
    arity = 1

    def true_at(self, argument, eval_world):
        """doc string place holder"""
        return self.semantics.false_at(argument, eval_world)

    def false_at(self, argument, eval_world):
        """doc string place holder"""
        return self.semantics.true_at(argument, eval_world)

    def extended_verify(self, state, arg, eval_world):
        return self.semantics.extended_falsify(state, arg, eval_world)
    
    def extended_falsify(self, state, arg, eval_world):
        return self.semantics.extended_verify(state, arg, eval_world)

    def find_verifiers_and_falsifiers(self, arg_sent_obj, eval_world):
        Y_V, Y_F = arg_sent_obj.proposition.find_proposition()
        return Y_F, Y_V

    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(sentence_obj, eval_world, indent_num, use_colors)


class AndOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder
        args are derived_objects (ie things of the third kind) I think, def 2nd or 3rd kind
        """
        sem = self.semantics
        return z3.And(
            sem.true_at(leftarg, eval_world),
            sem.true_at(rightarg, eval_world)
        )

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return z3.Or(sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world))

    def extended_verify(self, state, leftarg, rightarg, eval_world):
        x = z3.BitVec("ex_and_ver_x", self.semantics.N)
        y = z3.BitVec("ex_and_ver_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                self.semantics.fusion(x, y) == state,
                self.semantics.extended_verify(x, leftarg, eval_world),
                self.semantics.extended_verify(y, rightarg, eval_world),
            )
        )
    
    def extended_falsify(self, state, leftarg, rightarg, eval_world):
        x = z3.BitVec("ex_and_fal_x", self.semantics.N)
        y = z3.BitVec("ex_and_fal_y", self.semantics.N)
        return z3.Or(
            self.semantics.extended_falsify(state, leftarg, eval_world),
            self.semantics.extended_falsify(state, rightarg, eval_world),
            Exists(
                [x, y],
                z3.And(
                    state == self.semantics.fusion(x, y),
                    self.semantics.extended_falsify(x, leftarg, eval_world),
                    self.semantics.extended_falsify(y, rightarg, eval_world),
                ),
            )
        )

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_world):
        """Takes sentences objects as arguments, finds their verifiers and
        falsifiers, and returns the verifiers and falsifiers for the operator"""
        sem = self.semantics
        Y_V, Y_F = leftarg.proposition.find_proposition()
        Z_V, Z_F = rightarg.proposition.find_proposition()
        return sem.product(Y_V, Z_V), sem.coproduct(Y_F, Z_F)
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_world, indent_num, use_colors)


class OrOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        # print(f"true_at input types: {type(leftarg), type(eval_world)}")
        sem = self.semantics
        return z3.Or(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return z3.And(sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world))

    def extended_verify(self, state, leftarg, rightarg, eval_world):
        x = z3.BitVec("ex_or_ver_x", self.semantics.N)
        y = z3.BitVec("ex_or_ver_y", self.semantics.N)
        return z3.Or(
            self.semantics.extended_verify(state, leftarg, eval_world),
            self.semantics.extended_verify(state, rightarg, eval_world),
            Exists(
                [x, y],
                z3.And(
                    self.semantics.fusion(x, y) == state,
                    self.semantics.extended_verify(x, leftarg, eval_world),
                    self.semantics.extended_verify(y, rightarg, eval_world),
                )
            )
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_world):
        x = z3.BitVec("ex_fal_x", self.semantics.N)
        y = z3.BitVec("ex_fal_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                state == self.semantics.fusion(x, y),
                self.semantics.extended_falsify(x, leftarg, eval_world),
                self.semantics.extended_falsify(y, rightarg, eval_world),
            ),
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_world):
        sem = self.semantics
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        return sem.coproduct(Y_V, Z_V), sem.product(Y_F, Z_F)
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_world, indent_num, use_colors)


##############################################################################
############################## EXTREMAL OPERATORS ############################
##############################################################################

class TopOperator(syntactic.Operator):
    """Top element of the space of propositions with respect to ground.
    Is verified by everything and falsified by the full state."""

    name = "\\top"
    arity = 0

    def true_at(self, eval_world):
        """doc string place holder"""
        return eval_world == eval_world
        # return z3.Not(self.semantics.possible(self.semantics.full_bit))

    def false_at(self, eval_world):
        """doc string place holder"""
        return eval_world != eval_world

    def extended_verify(self, state, eval_world):
        return state == state

    def extended_falsify(self, state, eval_world):
        return state == self.semantics.full_bit

    def find_verifiers_and_falsifiers(self, eval_world):
        return set(self.semantics.all_bits), {self.semantics.full_bit}

    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Prints the proposition for sentence_obj."""
        self.general_print(sentence_obj, eval_world, indent_num, use_colors)


class BotOperator(syntactic.Operator):
    """Bottom element of the space of propositions with respect to ground.
    Is verified by nothing and falsified by the null state."""

    name = "\\bot"
    arity = 0

    def true_at(self, eval_world):
        """doc string place holder"""
        return eval_world != eval_world

    def false_at(self, eval_world):
        """doc string place holder"""
        return eval_world == eval_world

    def extended_verify(self, state, eval_world):
        return state != state

    def extended_falsify(self, state, eval_world):
        return state == self.semantics.null_bit

    def find_verifiers_and_falsifiers(self, eval_world):
        return set(), {self.semantics.null_bit}

    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Prints the proposition for sentence_obj."""
        self.general_print(sentence_obj, eval_world, indent_num, use_colors)


##############################################################################
########################### CONSTITUTIVE OPERATORS ###########################
##############################################################################

class IdentityOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\equiv"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_id_x", N)
        return z3.And(
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, leftarg, eval_world),
                    sem.extended_verify(x, rightarg, eval_world)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, leftarg, eval_world),
                    sem.extended_falsify(x, rightarg, eval_world)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, rightarg, eval_world),
                    sem.extended_verify(x, leftarg, eval_world)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, rightarg, eval_world),
                    sem.extended_falsify(x, leftarg, eval_world)
                ),
            )
        )

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_id_x", N)
        return z3.Or(
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, leftarg, eval_world),
                    z3.Not(sem.extended_verify(x, rightarg, eval_world))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_world),
                    z3.Not(sem.extended_falsify(x, rightarg, eval_world))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, rightarg, eval_world),
                    z3.Not(sem.extended_verify(x, leftarg, eval_world))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, rightarg, eval_world),
                    z3.Not(sem.extended_falsify(x, leftarg, eval_world))
                ),
            )
        )

    def extended_verify(self, state, leftarg, rightarg, eval_world):
        return z3.And(
            state == self.semantics.null_bit,
            self.true_at(leftarg, rightarg, eval_world)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_world):
        return z3.And(
            state == self.semantics.null_bit,
            self.false_at(leftarg, rightarg, eval_world)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_world):
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if Y_V == Z_V and Y_F == Z_F:
            return {self.semantics.null_bit}, set()
        return set(), {self.semantics.null_bit}
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_world, indent_num, use_colors)


##############################################################################
########################## COUNTERFACTUAL OPERATORS ##########################
##############################################################################

class CounterfactualOperator(syntactic.Operator):
    name = "\\boxright"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("t_ncf_x", N)
        u = z3.BitVec("t_ncf_u", N)
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    sem.extended_verify(x, leftarg, eval_world), # need extended_verify
                    sem.is_alternative(u, x, eval_world)
                ),
                sem.true_at(rightarg, u),
            ),
        )
    
    def false_at(self, leftarg, rightarg, eval_world):
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("f_ncf_x", N)
        u = z3.BitVec("f_ncf_u", N)
        return Exists(
            [x, u],
            z3.And(
                sem.extended_verify(x, leftarg, eval_world), # need extended_verify
                sem.is_alternative(u, x, eval_world),
                sem.false_at(rightarg, u)),
        )
    
    def extended_verify(self, state, leftarg, rightarg, eval_world):
        # TODO: add constraint which requires state to be the null_bit
        return self.true_at(leftarg, rightarg, eval_world)
    
    def extended_falsify(self, state, leftarg, rightarg, eval_world):
        # TODO: add constraint which requires state to be the null_bit
        return self.false_at(leftarg, rightarg, eval_world)

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_world):
        evaluate = leftarg.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(leftarg, rightarg, eval_world))):
            return {self.semantics.null_bit}, set()
        if bool(evaluate(self.false_at(leftarg, rightarg, eval_world))):
            return set(), {self.semantics.null_bit}
        raise ValueError(
            f"{leftarg.name} {self.name} {rightarg.name} "
            f"is neither true nor false in the world {eval_world}."
        )
    
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


##############################################################################
########################### INTENSIONAL OPERATORS ############################
##############################################################################

class NecessityOperator(syntactic.Operator):
    name = "\\Box"
    arity = 1

    def true_at(self, argument, eval_world):
        sem = self.semantics
        u = z3.BitVec("t_nec_u", sem.N)
        return ForAll(
            u,
            z3.Implies(
                sem.is_world(u),
                sem.true_at(argument, u),
            ),
        )
    
    def false_at(self, argument, eval_world):
        sem = self.semantics
        u = z3.BitVec("t_nec_u", sem.N)
        return Exists(
            u,
            z3.And(
                sem.is_world(u),
                sem.false_at(argument, u),
            ),
        )
    
    def extended_verify(self, state, argument, eval_world):
        # TODO: add constraint which requires state to be the null_bit
        return self.true_at(argument, eval_world) # M: I think this is right?
    
    def extended_falsify(self, state, argument, eval_world):
        # TODO: add constraint which requires state to be the null_bit
        return self.false_at(argument, eval_world)

    def find_verifiers_and_falsifiers(self, argument, eval_world):
        evaluate = argument.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(argument, eval_world))):
            return {self.semantics.null_bit}, set()
        if bool(evaluate(self.false_at(argument, eval_world))):
            return set(), {self.semantics.null_bit}
        raise ValueError(
            f"{self.name} {argument} "
            f"is neither true nor false in the world {eval_world}."
        )
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, eval_world, all_worlds, indent_num, use_colors)


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

    name = "\\circleright"
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

##############################################################################
####################### DEFINED INTENSIONAL OPERATORS ########################
##############################################################################

class DefPossibilityOperator(syntactic.DefinedOperator):

    name = "\\possible"
    arity = 1

    def derived_definition(self, arg):
        return [NegationOperator, [NecessityOperator, [NegationOperator, arg]]]
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.world_bits
        self.print_over_worlds(sentence_obj, eval_world, all_worlds, indent_num, use_colors)

operators = syntactic.OperatorCollection(
    NegationOperator,
    AndOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    IdentityOperator,
    CounterfactualOperator,
    NecessityOperator,
    ConditionalOperator,
    DefGroundOperator,
    DefEssenceOperator,
    MightCounterfactualOperator,
    DefPossibilityOperator,
)

