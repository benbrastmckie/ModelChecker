import z3

# NOTE: go in API
from hidden_things import (
    PropositionDefaults,
)

# NOTE: go in API
from hidden_helpers import (
    ForAll,
    Exists,
    bitvec_to_substates,
    index_to_substate,
    pretty_set_print,
)

import syntactic


##############################################################################
######################### SEMANTICS AND PROPOSITIONS #########################
##############################################################################


class Semantics:
    """Includes the semantic primitives, semantic definitions, frame
    constraints, truth and falsity theories, and premise/conclusion behavior."""

    def __init__(self, N):

        # Store the number of states
        self.N = N

        # Define the Z3 primitives
        self.verify = z3.Function("verify", z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())
        self.falsify = z3.Function("falsify", z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())
        self.possible = z3.Function("possible", z3.BitVecSort(N), z3.BoolSort())
        self.main_world = z3.BitVec("w", N)

        # Define top and bottom states
        max_value = (1 << self.N) - 1 # NOTE: faster than 2**self.N - 1
        self.full_bit = z3.BitVecVal(max_value, self.N)
        self.null_bit = z3.BitVecVal(0, self.N)
        self.all_bits = [z3.BitVecVal(i, self.N) for i in range(1 << self.N)]
        
        # Define the frame constraints
        x, y = z3.BitVecs("frame_x frame_y", N)
        # x, y, z = z3.BitVecs("frame_x frame_y frame_z", N)
        self.frame_constraints = [
            ForAll(
                [x, y],
                z3.Implies(z3.And(self.possible(y), self.is_part_of(x, y)), self.possible(x)),
            ),
            self.is_world(self.main_world),
            z3.Not(self.possible(self.full_bit)),
            # NOTE: was needed to get top and bot to work
            # ForAll([x, y], Exists(z, self.fusion(x, y) == z)), # M: is this necessary?
            # NOTE: not needed give that bitvector spaces are complete because finite
            # worth keeping around for now to do some benchmark testing on later
        ]

        # Define invalidity conditions
        self.premise_behavior = self.true_at
        self.conclusion_behavior = self.false_at

    def fusion(self, bit_s, bit_t):
        """the result of taking the maximum for each index in bit_s and bit_t
        returns a Z3 constraint"""
        return bit_s | bit_t

    def is_part_of(self, bit_s, bit_t):
        """the fusion of bit_s and bit_t is identical to bit_t
        returns a Z3 constraint"""
        return self.fusion(bit_s, bit_t) == bit_t

    def non_null_part_of(self, bit_s, bit_t):
        """bit_s verifies atom and is not the null state
        returns a Z3 constraint"""
        return z3.And(z3.Not(bit_s == 0), self.is_part_of(bit_s, bit_t))

    def compatible(self, bit_x, bit_y):
        """the fusion of bit_x and bit_y is possible
        returns a Z3 constraint"""
        return self.possible(self.fusion(bit_x, bit_y))

    def maximal(self, bit_w):
        """bit_w includes all compatible states as parts.
        returns a Z3 constraint"""
        x = z3.BitVec("max_x", self.N)
        return ForAll(
            x,
            z3.Implies(
                self.compatible(x, bit_w),
                self.is_part_of(x, bit_w),
            ),
        )

    def is_world(self, bit_w):
        """bit_w is both possible and maximal.
        returns a Z3 constraint"""
        return z3.And(
            self.possible(bit_w),
            self.maximal(bit_w),
        )

    def max_compatible_part(self, bit_x, bit_w, bit_y):
        """bit_x is the biggest part of bit_w that is compatible with bit_y.
        returns a Z3 constraint"""
        z = z3.BitVec("max_part", self.N)
        return z3.And(
            self.is_part_of(bit_x, bit_w),
            self.compatible(bit_x, bit_y),
            ForAll(
                z,
                z3.Implies(
                    z3.And(
                        self.is_part_of(z, bit_w),
                        self.compatible(z, bit_y),
                        self.is_part_of(bit_x, z),
                    ),
                    bit_x == z,
                ),
            ),
        )

    def is_alternative(self, bit_u, bit_y, bit_w):
        """
        bit_u is a world that is the alternative that results from imposing state bit_y on
        world bit_w.
        returns a Z3 constraint
        """
        z = z3.BitVec("alt_z", self.N)
        return z3.And(
            self.is_world(bit_u),
            self.is_part_of(bit_y, bit_u),
            Exists(z, z3.And(self.is_part_of(z, bit_u), self.max_compatible_part(z, bit_w, bit_y))),
        )

    def true_at(self, prefix_sentence, eval_world):
        """
        prefix_sentence is always a list, eval world a BitVector
        prefix_sentence is the third kind of prefix_sentence
        """
        if str(prefix_sentence[0]).isalnum():
            sentence_letter = prefix_sentence[0]
            x = z3.BitVec("t_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.verify(x, sentence_letter)))
        operator = prefix_sentence[0]
        assert not isinstance(operator, type), "operator should be an instance of a class"
        args = prefix_sentence[1:]
        return operator.true_at(*args, eval_world)

    def false_at(self, prefix_sentence, eval_world):
        if str(prefix_sentence[0]).isalnum():
            sentence_letter = prefix_sentence[0]
            x = z3.BitVec("f_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.falsify(x, sentence_letter)))
        operator = prefix_sentence[0]
        assert not isinstance(operator, type), "operator should be an instance of a class"
        args = prefix_sentence[1:]
        return operator.false_at(*args, eval_world)
    
    def extended_verify(self, state, prefix_sentence, eval_world):
        if str(prefix_sentence[0]).isalnum():
            return self.verify(state, prefix_sentence[0])
        op, args = prefix_sentence[0], prefix_sentence[1:]
        return op.extended_verify(state, *args, eval_world)
    
    def extended_falsify(self, state, prefix_sentence, eval_world):
        if str(prefix_sentence[0]).isalnum():
            return self.falsify(state, prefix_sentence[0])
        op, args = prefix_sentence[0], prefix_sentence[1:]
        return op.extended_falsify(state, *args, eval_world)

    def product(self, set_A, set_B):
        """set of pairwise fusions of elements in set_A and set_B"""
        product_set = set()
        for bit_a in set_A:
            for bit_b in set_B:
                bit_ab = z3.simplify(bit_a | bit_b)
                product_set.add(bit_ab)
        return product_set

    def coproduct(self, set_A, set_B):
        """union closed under pairwise fusion"""
        A_U_B = set_A.union(set_B)
        return A_U_B.union(self.product(set_A, set_B))


class Proposition(PropositionDefaults):
    """Defines the proposition assigned to the sentences of the language.
    all user has to keep for their own class is super().__init__ and super().__poster_init__
    in the __init__ method.
    """

    def __init__(self, sentence, model_structure, eval_world='main'):
        '''
        sentence is of type Sentence, model_structure is of type ModelStructure
        '''
        super().__init__(sentence, model_structure)
        self.eval_world = model_structure.main_world if eval_world == 'main' else eval_world
        self.verifiers, self.falsifiers = self.find_proposition()
        

    def __eq__(self, other):
        return (
            self.verifiers == other.verifiers
            and self.falsifiers == other.falsifiers
            and str(self.prefix_sentence) == str(other.prefix_sentence)
        )

    # TODO: break this up into smaller methods for each set of constraints
    def proposition_constraints(self, atom):
        """."""
        semantics = self.semantics
        x = z3.BitVec("prop_x", semantics.N)
        y = z3.BitVec("prop_y", semantics.N)
        non_null_constraints = [
            z3.Not(semantics.verify(0, atom)),
            z3.Not(semantics.falsify(0, atom)),
        ]
        contingent_constraints = [
            Exists(
                x,
                z3.And(
                    semantics.possible(x),
                    semantics.verify(x, atom),
                )
            ),
            Exists(
                y,
                z3.And(
                    semantics.possible(y),
                    semantics.falsify(y, atom),
                )
            ),
        ]
        classical_constraints = [
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.verify(x, atom), semantics.verify(y, atom)),
                    semantics.verify(semantics.fusion(x, y), atom),
                ),
            ),
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.falsify(x, atom), semantics.falsify(y, atom)),
                    semantics.falsify(semantics.fusion(x, y), atom),
                ),
            ),
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.verify(x, atom), semantics.falsify(y, atom)),
                    z3.Not(semantics.compatible(x, y)),
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    semantics.possible(x),
                    Exists(
                        y,
                        z3.And(
                            semantics.compatible(x, y),
                            z3.Or(semantics.verify(y, atom), semantics.falsify(y, atom)),
                        ),
                    ),
                ),
            ),
        ]
        constraints = classical_constraints
        if self.disjoint:
            z = z3.BitVec("prop_z", semantics.N)
            for other_atom in self.sentence_letters:
                if not other_atom is atom:
                    disjoin_constraints = [
                        ForAll(
                            [x, y],
                            z3.Implies(
                                z3.And(
                                    semantics.non_null_part_of(x, y),
                                    z3.Or(
                                        semantics.verify(y, atom),
                                        semantics.falsify(y, atom)
                                    )
                                ),
                                ForAll(
                                    z,
                                    z3.Implies(
                                        z3.Or(
                                            semantics.verify(z, other_atom),
                                            semantics.falsify(z, other_atom)
                                        ),
                                        z3.Not(semantics.is_part_of(x, z))
                                    )
                                )
                            )
                        )
                    ]
                    constraints.extend(disjoin_constraints)
                    constraints += non_null_constraints
                    # NOTE: non_null_constraints are important to avoid
                    # trivializing the disjoin_constraints
        if self.contingent:
            constraints += contingent_constraints
            # NOTE: contingent_constraints entail non_null_constraints and so
            # the disjoin_constraints constraints can be skipped
        elif self.non_null and not self.disjoint:
            constraints += non_null_constraints
            # NOTE: since non_null_constraints are included in the
            # disjoin_constraints they don't need to be added again here
        return constraints

    def find_proposition(self):
        """takes self, returns the V, F tuple
        used in find_verifiers_and_falsifiers"""
        all_sentences = self.model_constraints.all_sentences
        all_bits = self.model_structure.all_bits
        model = self.model_structure.z3_model
        sem = self.semantics
        if self.arguments is None: # self.arguments is a list of Sentence objects
            # atom = self.prefix_string[0] # borrowing convention from somewhere else
            if self.prefix_string[0] in {'\\top', '\\bot'}:
                operator = self.prefix_sentence[0]
                return operator.find_verifiers_and_falsifiers()
            if self.prefix_string[0].isalnum():
                # TODO: fix definition so that [0] is not needed below
                # M: why?
                # B: I think this is actually great how it is; sorta forgot
                # about the idea that all prefix_sentences are lists including
                # sentence letters. that still seems like a good convention
                # print("LETTER", self.prefix_sentence)
                sentence_letter = self.prefix_sentence[0]
                V = {
                    bit for bit in all_bits
                    if model.evaluate(sem.verify(bit, sentence_letter))
                }
                F = {
                    bit for bit in all_bits
                    if model.evaluate(sem.falsify(bit, sentence_letter))
                }
                return V, F
            raise ValueError(
                f"Their is no proposition for {self.prefix_string[0]}."
            )
        operator = self.prefix_operator
        arguments = [all_sentences[key] for key in self.arguments]
        return operator.find_verifiers_and_falsifiers(*arguments, self.eval_world)

    def truth_value_at(self, world):
        """Checks if there is a verifier or falsifier in world and not both."""
        semantics = self.model_structure.model_constraints.semantics
        z3_model = self.model_structure.z3_model
        ver_witness = None
        fal_witness = None
        exists_verifier = False
        exists_falsifier = False
        for ver_bit in self.verifiers:
            if z3_model.evaluate(semantics.is_part_of(ver_bit, world)):
                ver_witness = ver_bit
                exists_verifier = True
                break
        for fal_bit in self.falsifiers:
            if z3_model.evaluate(semantics.is_part_of(fal_bit, world)):
                fal_witness = fal_bit
                exists_falsifier = True
                break
        # print( # NOTE: a warning is preferable to raising an error
        #     f"WARNING: the world {bitvec_to_substates(world)} contains both:\n "
        #     f"  The verifier {bitvec_to_substates(ver_witness)}; and"
        #     f"  The falsifier {bitvec_to_substates(fal_witness)}."
        # )
        if exists_verifier == exists_falsifier:
            # TODO: convert from bits to states below
            print( # NOTE: a warning is preferable to raising an error
                f"WARNING: the world {index_to_substate(world)} contains both:\n "
                f"  The verifier {index_to_substate(ver_witness)}; and"
                f"  The falsifier {index_to_substate(fal_witness)}."
            )
            # if exists_verifier:
            #     raise ValueError(
            #         f"The world {world} has both a verifier and falsifier "
            #         f"for {self.name}. Something has gone wrong."
            #     )
            # raise ValueError(
            #     f"The world {world} has neither a verifier nor falsifier "
            #     f"for {self.name}. Something has gone wrong."
            # )
        return exists_verifier

    # M: eventually, we need to add a condition on unilateral or bilateral semantics
    # so that one set vs two is printed (one for unilateral, two for bilateral)
    # B: got it. i was thinking that in Proposition, the user can say what a
    # proposition is and how it gets printed. so maybe the following gets moved?
    def print_proposition(self, eval_world, indent_num=0):
        N = self.model_structure.model_constraints.semantics.N
        truth_value = self.truth_value_at(eval_world)
        possible = self.model_structure.model_constraints.semantics.possible
        z3_model = self.model_structure.z3_model
        ver_states = {
            bitvec_to_substates(bit, N)
            for bit in self.verifiers
            if z3_model.evaluate(possible(bit)) or self.print_impossible
        }
        ver_prints = pretty_set_print(ver_states) if ver_states else "∅"
        fal_states = {
            bitvec_to_substates(bit, N)
            for bit in self.falsifiers
            if z3_model.evaluate(possible(bit)) or self.print_impossible
        }
        # temporary fix on unary/binary issue below (the 'is None' bit)
        fal_prints = pretty_set_print(fal_states) if fal_states is not None else "∅"
        world_state = bitvec_to_substates(eval_world, N)
        RED = "\033[31m"
        GREEN = "\033[32m"
        RESET = "\033[0m"
        FULL = "\033[37m"
        PART = "\033[33m"
        if indent_num == 1:
            if truth_value:
                FULL = GREEN
                PART = GREEN
            if not truth_value:
                FULL = RED
                PART = RED
            if truth_value is None:
                world_state = bitvec_to_substates(eval_world, N)
                print(
                    f"\n{RED}WARNING:{RESET}"
                    f"{self} is neither true nor false at {world_state}.\n"
                )
        print(
            f"{'  ' * indent_num}{FULL}|{self}| = < {ver_prints}, {fal_prints} >{RESET}"
            f"  {PART}({truth_value} in {world_state}){RESET}"
        )



###############################################################################
############################ EXTENSIONAL OPERATORS ############################
###############################################################################


class AndOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder
        args are prefix_sentences (ie things of the third kind) I think, def 2nd or 3rd kind
        """
        sem = self.semantics
        return z3.And(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return z3.Or(sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world))

    def extended_verify(self, state, leftarg, rightarg, eval_world):
        y = z3.BitVec("ex_ver_y", self.semantics.N)
        z = z3.BitVec("ex_ver_z", self.semantics.N)
        return z3.And(
            self.semantics.fusion(y, z) == state,
            self.semantics.extended_verify(y, leftarg, eval_world),
            self.semantics.extended_verify(z, rightarg, eval_world),
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
        print(f"{left_sent_obj} has type {type(left_sent_obj)}")
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        return sem.product(Y_V, Z_V), sem.coproduct(Y_F, Z_F)
    

class OrOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        print(f"true_at input types: {type(leftarg), type(eval_world)}")
        sem = self.semantics
        return z3.Or(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return z3.And(sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world))

    def extended_verify(self, state, leftarg, rightarg, eval_world):
        print(f"extended_verify input types: {type(leftarg), type(eval_world), type(eval_world)}")
        return z3.Or(
            self.semantics.extended_verify(state, leftarg, eval_world),
            self.semantics.extended_verify(state, rightarg, eval_world),
            self.semantics.extended_verify(
                state,
                [AndOperator(self.semantics), leftarg, rightarg], 
                eval_world),
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_world):
        y = z3.BitVec("ex_fal_y", self.semantics.N)
        z = z3.BitVec("ex_fal_z", self.semantics.N)
        return Exists(
            [y, z],
            z3.And(
                state == self.semantics.fusion(y, z),
                self.semantics.extended_falsify(y, leftarg, eval_world),
                self.semantics.extended_falsify(z, rightarg, eval_world),
            ),
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj):
        sem = self.semantics
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        return sem.coproduct(Y_V, Z_V), sem.product(Y_F, Z_F)
    

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
    

class ConditionalOperator(syntactic.DefinedOperator):

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [OrOperator, [NegationOperator, leftarg], rightarg]


class BiconditionalOperator(syntactic.DefinedOperator):

    name = "\\leftrightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        right_to_left = [ConditionalOperator, leftarg, rightarg]
        left_to_right = [ConditionalOperator, rightarg, leftarg]
        return [AndOperator, right_to_left, left_to_right]


################################################################################
############################## EXTREMAL OPERATORS ##############################
################################################################################


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

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj):
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if Y_V == Z_V and Y_F == Z_F:
            return {self.semantics.null_bit}, set()
        return set(), {self.semantics.null_bit}
    

class DefGroundOperator(syntactic.DefinedOperator):

    name = "\\ground"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [IdentityOperator, [OrOperator, leftarg, rightarg], rightarg]


class DefEssenceOperator(syntactic.DefinedOperator):

    name = "\\essence"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [IdentityOperator, [AndOperator, leftarg, rightarg], rightarg]


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
                    Exists( # HARD TO REMOVE
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
            Exists( # REMOVABLE
                x,
                z3.And(
                    sem.extended_verify(x, leftarg, eval_world),
                    z3.Not(sem.extended_verify(x, rightarg, eval_world))
                )
            ),
            Exists( # REMOVABLE
                [x, y],
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_world),
                    sem.extended_falsify(y, rightarg, eval_world),
                    z3.Not(sem.extended_falsify(sem.fusion(x, y), rightarg, eval_world))
                ),
            ),
            Exists( # REMOVABLE
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

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj):
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if coproduct(Y_V, Z_V) == Z_V and product(Y_F, Z_F) == Z_F:
            return {self.semantics.null_bit}, set()
        return set(), {self.semantics.null_bit}


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
                    Exists( # HARD TO REMOVE
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
            Exists( # REMOVABLE
                [x, y],
                z3.And(
                    sem.extended_verify(x, leftarg, eval_world),
                    sem.extended_verify(y, rightarg, eval_world),
                    z3.Not(sem.extended_verify(sem.fusion(x, y), rightarg, eval_world))
                ),
            ),
            Exists( # REMOVABLE
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
            Exists( # REMOVABLE
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

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj):
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if product(Y_V, Z_V) == Z_V and coproduct(Y_F, Z_F) == Z_F:
            return {self.semantics.null_bit}, set()
        return set(), {self.semantics.null_bit}
    


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
        # NOTE: add constraint which requires state to be the null_bit
        return self.true_at(leftarg, rightarg, eval_world) # M: I think this is right?
    
    def extended_falsify(self, state, leftarg, rightarg, eval_world):
        # NOTE: add constraint which requires state to be the null_bit
        return self.false_at(leftarg, rightarg, eval_world)

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_world):
        # NOTE: leftprop
        # if the left proposition is true:
        #     return 
        # for verifier in leftprop's verifiers:
        #     if verifier is compatile
        # self.prefix_sentence = 
        leftarg, rightarg = left_sent_obj.prefix_sentence, right_sent_obj.prefix_sentence
        eval_at_model = left_sent_obj.proposition.model_structure.z3_model.evaluate
        if bool(eval_at_model(self.true_at(leftarg, rightarg, eval_world))):
            return {self.semantics.null_bit}, set()
        if not bool(eval_at_model(self.true_at(leftarg, rightarg, eval_world))):
            return set(), {self.semantics.null_bit}
        raise ValueError()
        # print(left_sent_obj.proposition.model_structure.z3_model.evaluate(self.true_at))
        # raise ValueError
        # # if left_sent_obj.proposition.model_structure.z3_model
        # # if bool()
        # # print(left_sent_obj)
        # if false: # ie if leftprop is false
        #     return set(), {self.semantics.null_bit}
        # if true:
        #     return {self.semantics.null_bit}, set()



