import z3

# Try local imports first (for development)
try:
    from src.model_checker.utils import (
        ForAll,
        Exists,
        bitvec_to_substates,
    )
    from src.model_checker import syntactic
except ImportError:
    # Fall back to installed package imports
    from model_checker.utils import (
        ForAll,
        Exists,
        bitvec_to_substates,
    )
    from model_checker import syntactic

##############################################################################
############################ EXTENSIONAL OPERATORS ###########################
##############################################################################

class NegationOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\neg"
    arity = 1

    def true_at(self, argument, eval_point):
        """doc string place holder"""
        return self.semantics.false_at(argument, eval_point)

    def false_at(self, argument, eval_point):
        """doc string place holder"""
        return self.semantics.true_at(argument, eval_point)

    def extended_verify(self, state, arg, eval_point):
        return self.semantics.extended_falsify(state, arg, eval_point)
    
    def extended_falsify(self, state, arg, eval_point):
        return self.semantics.extended_verify(state, arg, eval_point)

    def find_verifiers_and_falsifiers(self, arg_sent_obj, eval_point):
        Y_V, Y_F = arg_sent_obj.proposition.find_proposition()
        return Y_F, Y_V

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class AndOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """doc string place holder
        args are derived_objects (ie things of the third kind) I think, def 2nd or 3rd kind
        """
        sem = self.semantics
        return z3.And(
            sem.true_at(leftarg, eval_point),
            sem.true_at(rightarg, eval_point)
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        sem = self.semantics
        return z3.Or(sem.false_at(leftarg, eval_point), sem.false_at(rightarg, eval_point))

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        x = z3.BitVec("ex_and_ver_x", self.semantics.N)
        y = z3.BitVec("ex_and_ver_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                self.semantics.fusion(x, y) == state,
                self.semantics.extended_verify(x, leftarg, eval_point),
                self.semantics.extended_verify(y, rightarg, eval_point),
            )
        )
    
    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        x = z3.BitVec("ex_and_fal_x", self.semantics.N)
        y = z3.BitVec("ex_and_fal_y", self.semantics.N)
        return z3.Or(
            self.semantics.extended_falsify(state, leftarg, eval_point),
            self.semantics.extended_falsify(state, rightarg, eval_point),
            Exists(
                [x, y],
                z3.And(
                    state == self.semantics.fusion(x, y),
                    self.semantics.extended_falsify(x, leftarg, eval_point),
                    self.semantics.extended_falsify(y, rightarg, eval_point),
                ),
            )
        )

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point):
        """Takes sentences objects as arguments, finds their verifiers and
        falsifiers, and returns the verifiers and falsifiers for the operator"""
        sem = self.semantics
        Y_V, Y_F = leftarg.proposition.find_proposition()
        Z_V, Z_F = rightarg.proposition.find_proposition()
        return sem.product(Y_V, Z_V), sem.coproduct(Y_F, Z_F)
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class OrOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        # print(f"true_at input types: {type(leftarg), type(eval_point)}")
        sem = self.semantics
        return z3.Or(sem.true_at(leftarg, eval_point), sem.true_at(rightarg, eval_point))

    def false_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        sem = self.semantics
        return z3.And(sem.false_at(leftarg, eval_point), sem.false_at(rightarg, eval_point))

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        x = z3.BitVec("ex_or_ver_x", self.semantics.N)
        y = z3.BitVec("ex_or_ver_y", self.semantics.N)
        return z3.Or(
            self.semantics.extended_verify(state, leftarg, eval_point),
            self.semantics.extended_verify(state, rightarg, eval_point),
            Exists(
                [x, y],
                z3.And(
                    self.semantics.fusion(x, y) == state,
                    self.semantics.extended_verify(x, leftarg, eval_point),
                    self.semantics.extended_verify(y, rightarg, eval_point),
                )
            )
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        x = z3.BitVec("ex_fal_x", self.semantics.N)
        y = z3.BitVec("ex_fal_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                state == self.semantics.fusion(x, y),
                self.semantics.extended_falsify(x, leftarg, eval_point),
                self.semantics.extended_falsify(y, rightarg, eval_point),
            ),
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        sem = self.semantics
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        return sem.coproduct(Y_V, Z_V), sem.product(Y_F, Z_F)
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
############################## EXTREMAL OPERATORS ############################
##############################################################################

class TopOperator(syntactic.Operator):
    """Top element of the space of propositions with respect to ground.
    Is verified by everything and falsified by the full state."""

    name = "\\top"
    arity = 0

    def true_at(self, eval_point):
        """doc string place holder"""
        return 1 == 1
        # return z3.Not(self.semantics.possible(self.semantics.full_bit))

    def false_at(self, eval_point):
        """doc string place holder"""
        return 1 != 1

    def extended_verify(self, state, eval_point):
        return state == state

    def extended_falsify(self, state, eval_point):
        return state == self.semantics.full_bit

    def find_verifiers_and_falsifiers(self, eval_point):
        return set(self.semantics.all_bits), {self.semantics.full_bit}

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BotOperator(syntactic.Operator):
    """Bottom element of the space of propositions with respect to ground.
    Is verified by nothing and falsified by the null state."""

    name = "\\bot"
    arity = 0

    def true_at(self, eval_point):
        """doc string place holder"""
        return 1 != 1

    def false_at(self, eval_point):
        """doc string place holder"""
        return 1 == 1

    def extended_verify(self, state, eval_point):
        return state != state

    def extended_falsify(self, state, eval_point):
        return state == self.semantics.null_bit

    def find_verifiers_and_falsifiers(self, eval_point):
        return set(), {self.semantics.null_bit}

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
########################### CONSTITUTIVE OPERATORS ###########################
##############################################################################

class IdentityOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\equiv"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_id_x", N)
        return z3.And(
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(x, rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(x, rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, rightarg, eval_point),
                    sem.extended_verify(x, leftarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, rightarg, eval_point),
                    sem.extended_falsify(x, leftarg, eval_point)
                ),
            )
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_id_x", N)
        return z3.Or(
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    z3.Not(sem.extended_verify(x, rightarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    z3.Not(sem.extended_falsify(x, rightarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, rightarg, eval_point),
                    z3.Not(sem.extended_verify(x, leftarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, rightarg, eval_point),
                    z3.Not(sem.extended_falsify(x, leftarg, eval_point))
                ),
            )
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        return z3.And(
            state == self.semantics.null_bit,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        return z3.And(
            state == self.semantics.null_bit,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if Y_V == Z_V and Y_F == Z_F:
            return {self.semantics.null_bit}, set()
        return set(), {self.semantics.null_bit}
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class GroundOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\leq"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_seq_x", N)
        y = z3.BitVec("t_seq_y", N)
        return z3.And(
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(x, rightarg, eval_point)
                )
            ),
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        sem.extended_falsify(x, leftarg, eval_point),
                        sem.extended_falsify(y, rightarg, eval_point)
                    ),
                    sem.extended_falsify(sem.fusion(x, y), rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, rightarg, eval_point),
                    Exists(
                        y,
                        z3.And(
                            sem.extended_falsify(y, leftarg, eval_point),
                            sem.is_part_of(y, x),
                        )
                    )
                ),
            ),
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_seq_x", N)
        y = z3.BitVec("f_seq_y", N)
        return z3.Or(
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    z3.Not(sem.extended_verify(x, rightarg, eval_point))
                )
            ),
            Exists(
                [x, y],
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(y, rightarg, eval_point),
                    z3.Not(sem.extended_falsify(sem.fusion(x, y), rightarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, rightarg, eval_point),
                    ForAll(
                        y,
                        z3.Implies(
                            sem.extended_falsify(y, leftarg, eval_point),
                            z3.Not(sem.is_part_of(y, x)),
                        )
                    )
                ),
            ),
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        return z3.And(
            state == self.semantics.null_bit,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        return z3.And(
            state == self.semantics.null_bit,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if coproduct(Y_V, Z_V) == Z_V and product(Y_F, Z_F) == Z_F:
            return {self.semantics.null_bit}, set()
        return set(), {self.semantics.null_bit}

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors ):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class EssenceOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\sqsubseteq"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_seq_x", N)
        y = z3.BitVec("t_seq_y", N)
        return z3.And(
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        sem.extended_verify(x, leftarg, eval_point),
                        sem.extended_verify(y, rightarg, eval_point)
                    ),
                    sem.extended_verify(sem.fusion(x, y), rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, rightarg, eval_point),
                    Exists(
                        y,
                        z3.And(
                            sem.extended_verify(y, leftarg, eval_point),
                            sem.is_part_of(y, x),
                        )
                    )
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(x, rightarg, eval_point)
                )
            )
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_seq_x", N)
        y = z3.BitVec("f_seq_y", N)
        return z3.Or(
            Exists(
                [x, y],
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(y, rightarg, eval_point),
                    z3.Not(sem.extended_verify(sem.fusion(x, y), rightarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, rightarg, eval_point),
                    ForAll(
                        y,
                        z3.Implies(
                            sem.extended_verify(y, leftarg, eval_point),
                            z3.Not(sem.is_part_of(y, x)),
                        )
                    )
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    z3.Not(sem.extended_falsify(x, rightarg, eval_point))
                )
            )
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        return z3.And(
            state == self.semantics.null_bit,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        return z3.And(
            state == self.semantics.null_bit,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if product(Y_V, Z_V) == Z_V and coproduct(Y_F, Z_F) == Z_F:
            return {self.semantics.null_bit}, set()
        return set(), {self.semantics.null_bit}
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


###############################################################################
############################# RELEVANCE OPERATORS #############################
###############################################################################

class RelevanceOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\preceq"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_peq_x", N)
        y = z3.BitVec("t_peq_y", N)
        return z3.And(
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        sem.extended_verify(x, leftarg, eval_point),
                        sem.extended_verify(y, rightarg, eval_point)
                    ),
                    sem.extended_verify(sem.fusion(x, y), rightarg, eval_point)
                ),
            ),
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        sem.extended_falsify(x, leftarg, eval_point),
                        sem.extended_falsify(y, rightarg, eval_point)
                    ),
                    sem.extended_falsify(sem.fusion(x, y), rightarg, eval_point)
                ),
            ),
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_seq_x", N)
        y = z3.BitVec("f_seq_y", N)
        return z3.Or(
            Exists(
                [x, y],
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(y, rightarg, eval_point),
                    z3.Not(sem.extended_verify(sem.fusion(x, y), rightarg, eval_point))
                ),
            ),
            Exists(
                [x, y],
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(y, rightarg, eval_point),
                    z3.Not(sem.extended_falsify(sem.fusion(x, y), rightarg, eval_point))
                ),
            ),
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        return z3.And(
            state == self.semantics.null_bit,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        return z3.And(
            state == self.semantics.null_bit,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if product(Y_V, Z_V) == Z_V and coproduct(Y_F, Z_F) == Z_F:
            return {self.semantics.null_bit}, set()
        return set(), {self.semantics.null_bit}
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
########################## COUNTERFACTUAL OPERATORS ##########################
##############################################################################

class CounterfactualOperator(syntactic.Operator):
    name = "\\boxright"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("t_ncf_x", N)
        u = z3.BitVec("t_ncf_u", N)
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point), # need extended_verify
                    sem.is_alternative(u, x, eval_point)
                ),
                sem.true_at(rightarg, u),
            ),
        )
    
    def false_at(self, leftarg, rightarg, eval_point):
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("f_ncf_x", N)
        u = z3.BitVec("f_ncf_u", N)
        return Exists(
            [x, u],
            z3.And(
                sem.extended_verify(x, leftarg, eval_point), # need extended_verify
                sem.is_alternative(u, x, eval_point),
                sem.false_at(rightarg, u)),
        )
    
    def extended_verify(self, state, leftarg, rightarg, eval_point):
        # TODO: add constraint which requires state to be the null_bit
        return self.true_at(leftarg, rightarg, eval_point)
    
    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        # TODO: add constraint which requires state to be the null_bit
        return self.false_at(leftarg, rightarg, eval_point)

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point):
        evaluate = leftarg.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(leftarg, rightarg, eval_point))):
            return {self.semantics.null_bit}, set()
        if bool(evaluate(self.false_at(leftarg, rightarg, eval_point))):
            return set(), {self.semantics.null_bit}
        raise ValueError(
            f"{leftarg.name} {self.name} {rightarg.name} "
            f"is neither true nor false in the world {eval_point}."
        )
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_point. Then
        print the consequent in each alternative to the evaluation world.
        """
        is_alt = self.semantics.calculate_alternative_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_alt(left_argument_verifiers, eval_point, model_structure)
        self.print_over_worlds(sentence_obj, eval_point, alt_worlds, indent_num, use_colors)



##############################################################################
########################### INTENSIONAL OPERATORS ############################
##############################################################################

class NecessityOperator(syntactic.Operator):
    name = "\\Box"
    arity = 1

    def true_at(self, argument, eval_point):
        sem = self.semantics
        u = z3.BitVec("t_nec_u", sem.N)
        return ForAll(
            u,
            z3.Implies(
                sem.is_world(u),
                sem.true_at(argument, u),
            ),
        )
    
    def false_at(self, argument, eval_point):
        sem = self.semantics
        u = z3.BitVec("t_nec_u", sem.N)
        return Exists(
            u,
            z3.And(
                sem.is_world(u),
                sem.false_at(argument, u),
            ),
        )
    
    def extended_verify(self, state, argument, eval_point):
        # TODO: add constraint which requires state to be the null_bit
        return self.true_at(argument, eval_point) # M: I think this is right?
    
    def extended_falsify(self, state, argument, eval_point):
        # TODO: add constraint which requires state to be the null_bit
        return self.false_at(argument, eval_point)

    def find_verifiers_and_falsifiers(self, argument, eval_point):
        evaluate = argument.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(argument, eval_point))):
            return {self.semantics.null_bit}, set()
        if bool(evaluate(self.false_at(argument, eval_point))):
            return set(), {self.semantics.null_bit}
        raise ValueError(
            f"{self.name} {argument} "
            f"is neither true nor false in the world {eval_point}."
        )
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_point. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.z3_world_bits
        self.print_over_worlds(sentence_obj, eval_point, all_worlds, indent_num, use_colors)


##############################################################################
######################## DEFINED EXTENSIONAL OPERATORS #######################
##############################################################################

class ConditionalOperator(syntactic.DefinedOperator):

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg): # type: ignore
        return [OrOperator, [NegationOperator, leftarg], rightarg]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BiconditionalOperator(syntactic.DefinedOperator):

    name = "\\leftrightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg): # type: ignore
        right_to_left = [ConditionalOperator, leftarg, rightarg]
        left_to_right = [ConditionalOperator, rightarg, leftarg]
        return [AndOperator, right_to_left, left_to_right]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
###################### DEFINED COUNTERFACTUAL OPERATORS ######################
##############################################################################

class MightCounterfactualOperator(syntactic.DefinedOperator):

    name = "\\diamondright"
    arity = 2

    def derived_definition(self, leftarg, rightarg): # type: ignore
        return [
            NegationOperator, [
                CounterfactualOperator,
                leftarg,
                [NegationOperator, rightarg]
            ]
        ]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_point. Then
        print the consequent in each alternative to the evaluation world.
        """
        is_alt = self.semantics.calculate_alternative_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_alt(left_argument_verifiers, eval_point, model_structure)
        self.print_over_worlds(sentence_obj, eval_point, alt_worlds, indent_num, use_colors)


##############################################################################
####################### DEFINED INTENSIONAL OPERATORS ########################
##############################################################################

class DefPossibilityOperator(syntactic.DefinedOperator):

    name = "\\Diamond"
    arity = 1

    def derived_definition(self, arg): # type: ignore
        return [NegationOperator, [NecessityOperator, [NegationOperator, arg]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_point. Then
        print the consequent in each alternative to the evaluation world.
        """
        all_worlds = sentence_obj.proposition.model_structure.z3_world_bits
        self.print_over_worlds(sentence_obj, eval_point, all_worlds, indent_num, use_colors)

default_operators = syntactic.OperatorCollection(
    # primitive operators
    NegationOperator,
    AndOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    IdentityOperator,
    CounterfactualOperator,
    NecessityOperator,

    # defined operators
    ConditionalOperator,
    BiconditionalOperator,
    MightCounterfactualOperator,
    DefPossibilityOperator,
)

