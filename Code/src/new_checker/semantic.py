import z3

# NOTE: go in API
from model_builder import (
    PropositionDefaults,
    SemanticDefaults,
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


class Semantics(SemanticDefaults):
    """Includes the semantic primitives, semantic definitions, frame
    constraints, truth and falsity theories, and premise/conclusion behavior."""

    def __init__(self, N):

        # Initialize the superclass to set defaults
        super().__init__(N)

        # Define the Z3 primitives
        self.verify = z3.Function("verify", z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())
        self.falsify = z3.Function("falsify", z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())
        self.possible = z3.Function("possible", z3.BitVecSort(N), z3.BoolSort())
        self.main_world = z3.BitVec("w", N)

        # Define the frame constraints
        x, y = z3.BitVecs("frame_x frame_y", N)
        possibility_downard_closure = ForAll(
            [x, y],
            z3.Implies(z3.And(self.possible(y), self.is_part_of(x, y)), self.possible(x)),
        )
        is_main_world = self.is_world(self.main_world)
        impossible_full_bit = z3.Not(self.possible(self.full_bit))

        # Set frame constraints
        self.frame_constraints = [
            possibility_downard_closure,
            is_main_world,
            impossible_full_bit,
        ]

        # Define invalidity conditions
        self.premise_behavior = self.true_at
        self.conclusion_behavior = self.false_at

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
        operator, args = prefix_object[0], prefix_object[1:]
        assert not isinstance(operator, type), "operator should be an instance of a class"
        return operator.true_at(*args, eval_world)

    def false_at(self, prefix_object, eval_world):
        if str(prefix_object[0]).isalnum():
            sentence_letter = prefix_object[0]
            x = z3.BitVec("f_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.falsify(x, sentence_letter)))
        operator, args = prefix_object[0], prefix_object[1:]
        assert not isinstance(operator, type), "operator should be an instance of a class"
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

        def get_classical_constraints():
            x, y = z3.BitVecs("cl_prop_x cl_prop_y", semantics.N)
            """The classical_constraints rule out truth_value gaps and gluts."""
            verifier_fusion_closure = ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.verify(x, atom), semantics.verify(y, atom)),
                    semantics.verify(semantics.fusion(x, y), atom),
                ),
            )
            falsifier_fusion_closure = ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.falsify(x, atom), semantics.falsify(y, atom)),
                    semantics.falsify(semantics.fusion(x, y), atom),
                ),
            )
            no_glut = ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.verify(x, atom), semantics.falsify(y, atom)),
                    z3.Not(semantics.compatible(x, y)),
                ),
            )
            no_gap = ForAll(
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
            )
            return [
                verifier_fusion_closure,
                falsifier_fusion_closure,
                no_glut,
                no_gap
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
            x, y = z3.BitVecs("ct_prop_x ct_prop_y", semantics.N)
            possible_verifier = Exists(
                x,
                z3.And(semantics.possible(x), semantics.verify(x, atom))
            )
            possible_falsifier = Exists(
                y,
                z3.And(semantics.possible(y), semantics.falsify(y, atom))
            )
            return [
                possible_verifier,
                possible_falsifier,
            ]

        # TODO: fix
        def get_disjoint_constraints():
            """The non_null_constraints are included in disjoin_constraints."""
            x, y, z = z3.BitVecs("dj_prop_x dj_prop_y dj_prop_z", semantics.N)
            disjoint_constraints = []
            for other_atom in self.sentence_letters:
                if other_atom is not atom:
                    other_disjoint_atom = ForAll(
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
                    disjoint_constraints.append(other_disjoint_atom)
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
        if exists_verifier == exists_falsifier:
            # TODO: convert from bits to states below
            print( # NOTE: a warning is preferable to raising an error
                f"WARNING: the world {index_to_substate(world)} contains both:\n "
                f"  The verifier {index_to_substate(ver_witness)}; and"
                f"  The falsifier {index_to_substate(fal_witness)}."
            )
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
        fal_states = {
            bitvec_to_substates(bit, N)
            for bit in self.falsifiers
            if z3_model.evaluate(possible(bit)) or self.print_impossible
        }
        ver_prints = pretty_set_print(ver_states)
        fal_prints = pretty_set_print(fal_states)
        world_state = bitvec_to_substates(eval_world, N)
        # DISCUSS: move colors into hidden_helpers? or a similar file with useful helpers? 
        # B: that sounds like a great idea 
        # M: ik we discussed smth like that earlier. I think it'd be good to have one file
        # for helpers not useful to users and one with helpers/things (these would be candidates)
        # useful to users
        # B: also sounds like a great idea 
        RED, GREEN, RESET, FULL, PART = "\033[31m", "\033[32m", "\033[0m", "\033[37m", "\033[33m"
        if indent_num == 1:
            FULL, PART = (GREEN, GREEN) if truth_value else (RED, RED)
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
