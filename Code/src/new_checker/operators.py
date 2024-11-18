import z3

from hidden_helpers import (
    ForAll,
    Exists,
    bitvec_to_substates,
    pretty_set_print,
)

import syntactic

##############################################################################
############################ EXTENSIONAL OPERATORS ###########################
##############################################################################

class NegationOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\neg"
    arity = 1

    def true_at(self, arg, eval_world):
        """doc string place holder"""
        return self.semantics.false_at(arg, eval_world)

    def false_at(self, arg, eval_world):
        """doc string place holder"""
        return self.semantics.true_at(arg, eval_world)

    def extended_verify(self, state, arg, eval_world):
        return self.semantics.extended_falsify(state, arg, eval_world)
    
    def extended_falsify(self, state, arg, eval_world):
        return self.semantics.extended_verify(state, arg, eval_world)

    def find_verifiers_and_falsifiers(self, arg_sent_obj, eval_world):
        Y_V, Y_F = arg_sent_obj.proposition.find_proposition()
        return Y_F, Y_V

    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)


class AndOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder
        args are prefix_objects (ie things of the third kind) I think, def 2nd or 3rd kind
        """
        sem = self.semantics
        return z3.And(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return z3.Or(sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world))

    def extended_verify(self, state, leftarg, rightarg, eval_world):
        x = z3.BitVec("ex_ver_x", self.semantics.N)
        y = z3.BitVec("ex_ver_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                self.semantics.fusion(x, y) == state,
                self.semantics.extended_verify(x, leftarg, eval_world),
                self.semantics.extended_verify(y, rightarg, eval_world),
            )
        )
    
    def extended_falsify(self, state, leftarg, rightarg, eval_world):
        return z3.Or(
            self.semantics.extended_falsify(state, leftarg, eval_world),
            self.semantics.extended_falsify(state, rightarg, eval_world),
            self.semantics.extended_falsify(
                state,
                [OrOperator(self.semantics), leftarg, rightarg],
                eval_world
            ),
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_world):
        """Takes sentences objects as arguments, finds their verifiers and
        falsifiers, and returns the verifiers and falsifiers for the operator"""
        sem = self.semantics
        # print(f"{left_sent_obj} has type {type(left_sent_obj)}")
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        return sem.product(Y_V, Z_V), sem.coproduct(Y_F, Z_F)
    
    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)


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
        # print(f"extended_verify input types: {type(leftarg), type(eval_world), type(eval_world)}")
        return z3.Or(
            self.semantics.extended_verify(state, leftarg, eval_world),
            self.semantics.extended_verify(state, rightarg, eval_world),
            self.semantics.extended_verify(
                state,
                [AndOperator(self.semantics), leftarg, rightarg], 
                eval_world),
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
    
    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)


##############################################################################
######################## DEFINED EXTENSIONAL OPERATORS #######################
##############################################################################

class ConditionalOperator(syntactic.DefinedOperator):

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [OrOperator, [NegationOperator, leftarg], rightarg]
    
    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)


class BiconditionalOperator(syntactic.DefinedOperator):

    name = "\\leftrightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        left_implies_right = [ConditionalOperator, leftarg, rightarg]
        right_implies_left = [ConditionalOperator, rightarg, leftarg]
        return [AndOperator, left_implies_right, right_implies_left]
    
    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)





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

    def find_verifiers_and_falsifiers(self):
        return set(self.semantics.all_bits), {self.semantics.full_bit}

    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)


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

    def find_verifiers_and_falsifiers(self):
        return set(), {self.semantics.null_bit}

    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)





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
    
    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)


class GroundOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\leq"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_seq_x", N)
        y = z3.BitVec("t_seq_y", N)
        return z3.And(
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, leftarg, eval_world),
                    sem.extended_verify(x, rightarg, eval_world)
                )
            ),
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        sem.extended_falsify(x, leftarg, eval_world),
                        sem.extended_falsify(y, rightarg, eval_world)
                    ),
                    sem.extended_falsify(sem.fusion(x, y), rightarg, eval_world)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, rightarg, eval_world),
                    Exists(
                        y,
                        z3.And(
                            sem.extended_falsify(y, leftarg, eval_world),
                            sem.is_part_of(y, x),
                        )
                    )
                ),
            ),
        )

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_seq_x", N)
        y = z3.BitVec("f_seq_y", N)
        return z3.Or(
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, leftarg, eval_world),
                    z3.Not(sem.extended_verify(x, rightarg, eval_world))
                )
            ),
            Exists(
                [x, y],
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_world),
                    sem.extended_falsify(y, rightarg, eval_world),
                    z3.Not(sem.extended_falsify(sem.fusion(x, y), rightarg, eval_world))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, rightarg, eval_world),
                    ForAll(
                        y,
                        z3.Implies(
                            sem.extended_falsify(y, leftarg, eval_world),
                            z3.Not(sem.is_part_of(y, x)),
                        )
                    )
                ),
            ),
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
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if coproduct(Y_V, Z_V) == Z_V and product(Y_F, Z_F) == Z_F:
            return {self.semantics.null_bit}, set()
        return set(), {self.semantics.null_bit}

    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)


class EssenceOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\sqsubseteq"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
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
                        sem.extended_verify(x, leftarg, eval_world),
                        sem.extended_verify(y, rightarg, eval_world)
                    ),
                    sem.extended_verify(sem.fusion(x, y), rightarg, eval_world)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, rightarg, eval_world),
                    Exists(
                        y,
                        z3.And(
                            sem.extended_verify(y, leftarg, eval_world),
                            sem.is_part_of(y, x),
                        )
                    )
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, leftarg, eval_world),
                    sem.extended_falsify(x, rightarg, eval_world)
                )
            )
        )

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_seq_x", N)
        y = z3.BitVec("f_seq_y", N)
        return z3.Or(
            Exists(
                [x, y],
                z3.And(
                    sem.extended_verify(x, leftarg, eval_world),
                    sem.extended_verify(y, rightarg, eval_world),
                    z3.Not(sem.extended_verify(sem.fusion(x, y), rightarg, eval_world))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, rightarg, eval_world),
                    ForAll(
                        y,
                        z3.Implies(
                            sem.extended_verify(y, leftarg, eval_world),
                            z3.Not(sem.is_part_of(y, x)),
                        )
                    )
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_world),
                    z3.Not(sem.extended_falsify(x, rightarg, eval_world))
                )
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
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if product(Y_V, Z_V) == Z_V and coproduct(Y_F, Z_F) == Z_F:
            return {self.semantics.null_bit}, set()
        return set(), {self.semantics.null_bit}
    
    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)



##############################################################################
####################### DEFINED CONSTITUTIVE OPERATORS #######################
##############################################################################

class DefGroundOperator(syntactic.DefinedOperator):

    name = "\\ground"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [IdentityOperator, [OrOperator, leftarg, rightarg], rightarg]

    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)


class DefEssenceOperator(syntactic.DefinedOperator):

    name = "\\essence"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [IdentityOperator, [AndOperator, leftarg, rightarg], rightarg]

    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)



##############################################################################
########################## COUNTERFACTUAL OPERATORS ##########################
##############################################################################

class CounterfactualOperator(syntactic.Operator):
    name = "\\boxright"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        sem = self.semantics
        x = z3.BitVec("t_ncf_x", sem.N)
        u = z3.BitVec("t_ncf_u", sem.N)
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    sem.extended_verify(x, leftarg, eval_world), # need extended_verify
                    # sem.verify(x, leftarg[0]), # for testing to see if it made a diff
                    sem.is_alternative(u, x, eval_world)
                ),
                sem.true_at(rightarg, u),
            ),
        )
    
    def false_at(self, leftarg, rightarg, eval_world):
        sem = self.semantics
        x = z3.BitVec("f_ncf_x", sem.N)
        u = z3.BitVec("f_ncf_u", sem.N)
        return Exists(
            [x, u],
            z3.And(
                sem.extended_verify(x, leftarg, eval_world), # need extended_verify
                sem.is_alternative(u, x, eval_world),
                sem.false_at(rightarg, u)),
        )
    
    def extended_verify(self, state, leftarg, rightarg, eval_world):
        # TODO: add constraint which requires state to be the null_bit
        return self.true_at(leftarg, rightarg, eval_world) # M: I think this is right?
    
    def extended_falsify(self, state, leftarg, rightarg, eval_world):
        # TODO: add constraint which requires state to be the null_bit
        return self.false_at(leftarg, rightarg, eval_world)

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_world):
        leftarg, rightarg = left_sent_obj.prefix_object, right_sent_obj.prefix_object
        eval_at_model = left_sent_obj.proposition.model_structure.z3_model.evaluate
        if bool(eval_at_model(self.true_at(leftarg, rightarg, eval_world))):
            return {self.semantics.null_bit}, set()
        if bool(eval_at_model(self.false_at(leftarg, rightarg, eval_world))):
            return set(), {self.semantics.null_bit}
        raise ValueError(
            f"{left_sent_obj} {self.name} {right_sent_obj} "
            f"is neither true nor false in the world {eval_world}."
        )
    
    # TODO: move to parent class since needed generally
    def calculate_alternative_worlds(self, verifiers, eval_world, model_structure):
        """Calculate alternative worlds given verifiers and eval_world."""
        is_alt = model_structure.semantics.is_alternative
        eval = model_structure.z3_model.evaluate
        world_bits = model_structure.world_bits
        return {
            pw for ver in verifiers
            for pw in world_bits
            if eval(is_alt(pw, ver, eval_world))
        }

    # TODO: move generalized version to parent class since needed generally
    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        CYAN, RESET = '\033[36m', '\033[0m'  # Move to class or config for flexibility

        sentence_obj = model_structure.all_sentences[syntactic.infix(DL_prefix_sentence)]
        # NOTE: TRANSLATE function would be useful here (above)
        proposition = sentence_obj.proposition
        N = proposition.N
        
        # Print main proposition
        # proposition.print_proposition(syntactic.infix(DL_prefix_sentence), eval_world, indent_num)
        
        # Increment indentation for nested output
        indent_num += 1
        
        # Retrieve primary subsentences and verifiers
        left_subsentence, right_subsentence = sentence_obj.arguments
        left_subprop_verifiers = left_subsentence.proposition.verifiers
        
        # Calculate alternative worlds
        alt_worlds = self.calculate_alternative_worlds(left_subprop_verifiers, eval_world, model_structure)
        alt_world_strings = {bitvec_to_substates(u, N) for u in alt_worlds}
        
        # Print left subsentence and alternatives
        model_structure.recursive_print(DL_prefix_sentence[1], eval_world, indent_num)
        print(
            f'{"  " * indent_num} {CYAN}{left_subsentence}-alternatives '
            f'to {bitvec_to_substates(eval_world, N)} = '
            f'{pretty_set_print(alt_world_strings)}{RESET}'
        )
        
        # Increment indentation for right subsentence print
        indent_num += 1
        for alt_world in alt_worlds:
            model_structure.recursive_print(DL_prefix_sentence[2], alt_world, indent_num)


        # 1. get the verifiers for the left subprop
        # 2. find the alt worlds (take ad)
        # 3. print the verifiers and falsifiers of the left subprop at the current world
        # 4. print all of the left_subprop-alternatives to the current world
        # 5. for each of those worlds, rec print the right subprop

        # left_subprop_vers = left_subprop['verifiers'] # get the verifiers
        # imp_worlds = self.find_alt_bits(left_subprop_vers, world_bit) # find the alt bits
        # imp_world_strings = {bitvec_to_substates(u,N) for u in imp_worlds}
        # self.recursive_print(left_subprop, world_bit, print_impossible, output, indent)
        # print(
        #     f'{"  " * indent}'
        #     f'{CYAN}{left_subprop}-alternatives to {bitvec_to_substates(world_bit, N)} = '
        #     f'{pretty_set_print(imp_world_strings)}{RESET}',
        #     file=output
        # )
        # indent += 1
        # for u in imp_worlds:
        #     self.recursive_print(right_subprop, u, print_impossible, output, indent)


##############################################################################
###################### DEFINED COUNTERFACTUAL OPERATORS ######################
##############################################################################

class MightCounterfactualOperator(syntactic.DefinedOperator):

    name = "\\circleright"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [NegationOperator, [CounterfactualOperator, leftarg, [NegationOperator, rightarg]]]

    def calculate_alternative_worlds(self, verifiers, eval_world, model_structure):
        """Calculate alternative worlds given verifiers and eval_world."""
        eval = model_structure.z3_model.evaluate
        is_alt = model_structure.semantics.is_alternative
        return {
            pw for ver in verifiers
            for pw in model_structure.world_bits
            if eval(is_alt(pw, ver, eval_world))
        }

    # TODO: move generalized version to parent class since needed generally
    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        CYAN, RESET = '\033[36m', '\033[0m'  # Move to class or config for flexibility

        oc = model_structure.model_constraints.operator_collection
        # B: why doesn't sentence_obj.model_structure exist?
        sentence_obj = model_structure.all_sentences[syntactic.infix(oc.apply_operator(DL_prefix_sentence))]
        # NOTE: TRANSLATE function would be useful here (above)
        proposition = sentence_obj.proposition
        N = proposition.N
        
        # Increment indentation for nested output
        indent_num += 1
        
        left_DL_prefix_sentence, right_DL_prefix_sentence = DL_prefix_sentence[1:]
        left_subsentence = model_structure.all_sentences[syntactic.infix(oc.apply_operator(left_DL_prefix_sentence))]
        # NOTE: TRANSLATE function would be useful here (above)
        left_subprop_verifiers = left_subsentence.proposition.verifiers
        
        # Calculate alternative worlds
        alt_worlds = self.calculate_alternative_worlds(left_subprop_verifiers, eval_world, model_structure)
        alt_world_strings = {bitvec_to_substates(u, N) for u in alt_worlds}
        
        # Print left subsentence and alternatives
        model_structure.recursive_print(left_DL_prefix_sentence, eval_world, indent_num)
        print(
            f'{"  " * indent_num} {CYAN}{left_subsentence}-alternatives '
            f'to {bitvec_to_substates(eval_world, N)} = '
            f'{pretty_set_print(alt_world_strings)}{RESET}'
        )
        
        # Increment indentation for right subsentence print
        indent_num += 1
        for alt_world in alt_worlds:
            model_structure.recursive_print(right_DL_prefix_sentence, alt_world, indent_num)


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

    def find_verifiers_and_falsifiers(self, sentence_object, eval_world):
        argument = sentence_object.prefix_object
        eval_at_model = sentence_object.proposition.model_structure.z3_model.evaluate
        if bool(eval_at_model(self.true_at(argument, eval_world))):
            return {self.semantics.null_bit}, set()
        if bool(eval_at_model(self.false_at(argument, eval_world))):
            return set(), {self.semantics.null_bit}
        raise ValueError(
            f"{self.name} {sentence_object} "
            f"is neither true nor false in the world {eval_world}."
        )
    
    def calculate_true_worlds(self, verifiers, eval_world, model_structure):
        """Calculate alternative worlds given verifiers and eval_world."""
        is_alt = model_structure.semantics.is_alternative
        eval = model_structure.z3_model.evaluate
        return {
            pw for ver in verifiers
            for pw in model_structure.world_bits
            if eval(is_alt(pw, ver, eval_world))
        }
    
    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)

    # NOTE: M: isn't below for CFs? Wouldn't print method for \\Box just be the general one (above)?
    # # TODO: move generalized version to parent class since needed generally
    # def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
    #     """Print counterfactual and the antecedent in the eval_world. Then
    #     print the consequent in each alternative to the evaluation world.
    #     """
    #     CYAN, RESET = '\033[36m', '\033[0m'  # Move to class or config for flexibility

    #     oc = model_structure.model_constraints.operator_collection
    #     sentence_obj = model_structure.all_sentences[syntactic.infix(oc.apply_operator(DL_prefix_sentence))]
    #     # NOTE: TRANSLATE function would be useful here (above)
    #     # B: why doesn't sentence_obj.model_structure exist?
    #     proposition = sentence_obj.proposition
    #     N = proposition.N
        
    #     # Print main proposition
    #     proposition.print_proposition(eval_world, indent_num)
        
    #     # Increment indentation for nested output
    #     indent_num += 1
        
    #     # TODO: need to adapt to single argument
    #     # Retrieve primary subsentences and verifiers
    #     left_subsentence, right_subsentence = sentence_obj.arguments
    #     left_subprop_verifiers = left_subsentence.proposition.verifiers
        
    #     # Calculate alternative worlds
    #     alt_worlds = self.calculate_alternative_worlds(left_subprop_verifiers, eval_world, model_structure)
    #     alt_world_strings = {bitvec_to_substates(u, N) for u in alt_worlds}
        
    #     # Print left subsentence and alternatives
    #     model_structure.recursive_print(left_subsentence, eval_world, indent_num)
    #     print(
    #         f'{"  " * indent_num} {CYAN}{left_subsentence}-alternatives '
    #         f'to {bitvec_to_substates(eval_world, N)} = '
    #         f'{pretty_set_print(alt_world_strings)}{RESET}'
    #     )
        
    #     # Increment indentation for right subsentence print
    #     indent_num += 1
    #     for alt_world in alt_worlds:
    #         model_structure.recursive_print(right_subsentence, alt_world, indent_num)


##############################################################################
####################### DEFINED INTENSIONAL OPERATORS ########################
##############################################################################

class DefNecessityOperator(syntactic.DefinedOperator):

    name = "\\necessary"
    arity = 1

    def derived_definition(self, rightarg):
        return [CounterfactualOperator, [TopOperator], rightarg]
    
    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)


# TODO: could be worth defining in terms of \circleright as well to compare
# M: see DefPossibilityOperator2 (note name change)
class DefPossibilityOperator(syntactic.DefinedOperator):

    name = "\\possible"
    arity = 1

    def derived_definition(self, arg):
        return [NegationOperator, [DefNecessityOperator, [NegationOperator, arg]]]
    
    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)

class DefPossibilityOperator2(syntactic.DefinedOperator):

    name = "\\possible2" # note name change
    arity = 1

    def derived_definition(self, arg):
        return [MightCounterfactualOperator, [TopOperator], arg]
    
    def print_method(self, DL_prefix_sentence, model_structure, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(DL_prefix_sentence, model_structure, eval_world, indent_num)

