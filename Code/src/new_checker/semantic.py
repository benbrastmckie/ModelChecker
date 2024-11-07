import z3

# NOTE: go in API
from model_builder import (
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
        self.frame_constraints = [
            ForAll(
                [x, y],
                z3.Implies(z3.And(self.possible(y), self.is_part_of(x, y)), self.possible(x)),
            ),
            self.is_world(self.main_world),
            z3.Not(self.possible(self.full_bit)),
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

    def true_at(self, prefix_object, eval_world):
        """
        prefix_object is always a list, eval world a BitVector
        prefix_object is the third kind of prefix_object
        """
        if str(prefix_object[0]).isalnum():
            sentence_letter = prefix_object[0]
            x = z3.BitVec("t_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.verify(x, sentence_letter)))
        operator = prefix_object[0]
        assert not isinstance(operator, type), "operator should be an instance of a class"
        args = prefix_object[1:]
        return operator.true_at(*args, eval_world)

    def false_at(self, prefix_object, eval_world):
        if str(prefix_object[0]).isalnum():
            sentence_letter = prefix_object[0]
            x = z3.BitVec("f_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.falsify(x, sentence_letter)))
        operator = prefix_object[0]
        assert not isinstance(operator, type), "operator should be an instance of a class"
        args = prefix_object[1:]
        return operator.false_at(*args, eval_world)
    
    def extended_verify(self, state, prefix_object, eval_world):
        if isinstance(prefix_object, syntactic.Operator):
            # B: I don't think this ever gets called DISCUSS
            print("TEST CHANGE")
            return prefix_object.extended_verify(state, eval_world)
        if str(prefix_object[0]).isalnum():
            return self.verify(state, prefix_object[0])
        op, args = prefix_object[0], prefix_object[1:]
        return op.extended_verify(state, *args, eval_world)
    
    def extended_falsify(self, state, prefix_object, eval_world):
        if isinstance(prefix_object, syntactic.Operator):
            # B: I don't think this ever gets called DISCUSS
            print("TEST CHANGE")
            return prefix_object.extended_falsify(state, eval_world)
        if str(prefix_object[0]).isalnum():
            return self.falsify(state, prefix_object[0])
        op, args = prefix_object[0], prefix_object[1:]
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

    def __init__(self, sentence_obj, model_structure, eval_world='main'):
        """TODO"""

        super().__init__(sentence_obj, model_structure)
        self.eval_world = model_structure.main_world if eval_world == 'main' else eval_world
        self.verifiers, self.falsifiers = self.find_proposition()
        

    def __eq__(self, other):
        return (
            self.verifiers == other.verifiers
            and self.falsifiers == other.falsifiers
            and self.name == other.name
            # and str(self.prefix_object) == str(other.prefix_object)
        )

    # TODO: check logic and doc strings
    def proposition_constraints(self, atom):
        """
        Generates Z3 constraints for a sentence letter including the classical
        constraints and optionally the non-null, contingent, and disjoint
        constraints depending on the user settings."""
        semantics = self.semantics
        # TODO: move copies into subfunctions renaming variables for readable
        # unsat_core
        x, y, z = z3.BitVecs("prop_x prop_y prop_z", semantics.N)
        # y = z3.BitVec("prop_y", semantics.N)
        # z = z3.BitVec("prop_z", semantics.N)

        def get_classical_constraints():
            """The classical_constraints rule out truth_value gaps and gluts."""
            return [
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

        def get_non_null_constraints():
            """The non_null_constraints are important to avoid trivializing
            the disjoin_constraints, but are entailed by the contingent_constraints."""
            return [
                z3.Not(semantics.verify(0, atom)),
                z3.Not(semantics.falsify(0, atom)),
            ]

        def get_contingent_constraints():
            """The contingent_constraints entail the non_null_constraints."""
            return [
                Exists(
                    x,
                    z3.And(semantics.possible(x), semantics.verify(x, atom))
                ),
                Exists(
                    y,
                    z3.And(semantics.possible(y), semantics.falsify(y, atom))
                ),
            ]

        # # OLD
        # if self.disjoint:
        #     z = z3.BitVec("prop_z", semantics.N)
        #     for other_atom in self.sentence_letters:
        #         if not other_atom is atom:
        #             disjoin_constraints = [
        #                 ForAll(
        #                     [x, y],
        #                     z3.Implies(
        #                         z3.And(
        #                             semantics.non_null_part_of(x, y),
        #                             z3.Or(
        #                                 semantics.verify(y, atom),
        #                                 semantics.falsify(y, atom)
        #                             )
        #                         ),
        #                         ForAll(
        #                             z,
        #                             z3.Implies(
        #                                 z3.Or(
        #                                     semantics.verify(z, other_atom),
        #                                     semantics.falsify(z, other_atom)
        #                                 ),
        #                                 z3.Not(semantics.is_part_of(x, z))
        #                             )
        #                         )
        #                     )
        #                 )
        #             ]
        #             constraints.extend(disjoin_constraints)
        #             constraints += non_null_constraints
        #             # NOTE: non_null_constraints are important to avoid
        #             # trivializing the disjoin_constraints

        # TODO: fix
        def get_disjoint_constraints():
            """The non_null_constraints are included in disjoin_constraints."""
            disjoint_constraints = []
            for other_atom in self.sentence_letters:
                if other_atom is not atom:
                    disjoint_constraints.append(
                        ForAll(
                            [x, y],
                            z3.Implies(
                                z3.And(
                                    semantics.non_null_part_of(x, y),
                                    z3.Or(
                                        semantics.verify(y, atom),
                                        semantics.falsify(y, atom),
                                    ),
                                ),
                                ForAll(
                                    z,
                                    z3.Implies(
                                        z3.Or(
                                            semantics.verify(z, other_atom),
                                            semantics.falsify(z, other_atom)
                                        ),
                                        z3.Not(semantics.is_part_of(x, z)),
                                    )
                                )
                            )
                        )
                    )
            return disjoint_constraints

        # Start collecting constraints
        constraints = get_classical_constraints()
        # Constraints based on settings
        if self.disjoint:
            constraints.extend(get_disjoint_constraints())
            constraints.extend(get_non_null_constraints())
        if self.contingent:
            constraints.extend(get_contingent_constraints())
        elif self.non_null and not self.disjoint:
            constraints.extend(get_non_null_constraints())
        return constraints


    def find_proposition(self):
        """takes self, returns the V, F tuple
        used in find_verifiers_and_falsifiers"""
        all_bits = self.model_structure.all_bits
        model = self.model_structure.z3_model
        sem = self.semantics
        if self.arguments is None: # self.arguments is a list of Sentence objects
            atom = self.prefix_sentence[0]
            if atom in {'\\top', '\\bot'}:
                operator = self.prefix_operator
                return operator.find_verifiers_and_falsifiers()
            if atom.isalnum():
                sentence_letter = self.prefix_object[0]
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
                f"Their is no proposition for {atom}."
            )
        operator = self.prefix_operator
        # the reason it doesn't work is because this the fake sentences
        # have subsentences that are not updated at all

        # for arg in self.arguments:

        #     assert arg in self.model_structure.all_sentences, self.arguments
        # this above isn't true in normal cases though... not sure what the issue is
        return operator.find_verifiers_and_falsifiers(*self.arguments, self.eval_world)

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
        # TODO: build empty set into pretty_set_print
        ver_prints = pretty_set_print(ver_states) if ver_states else "∅"
        fal_states = {
            bitvec_to_substates(bit, N)
            for bit in self.falsifiers
            if z3_model.evaluate(possible(bit)) or self.print_impossible
        }
        # temporary fix on unary/binary issue below (the 'is None' bit)
        # B: why not like the comment below? DISCUSS
        # fal_prints = pretty_set_print(fal_states) if fal_states else "∅"
        # TODO: build empty set into pretty_set_print
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
