"""
contains all semantic functions
"""

from z3 import (
    sat,
    Exists,
    ForAll,
    Implies,
    Or,
    Not,
    Solver,
    And,
    BitVec,
)
from syntax import Prefix

# from sympy import symbols, Or, And, Implies, Not, to_cnf

"""
this file defines the functions needed to generate Z3 constraints from
input_sentences in infix form.
"""

# def bit_vec_length():
#     from test_complete import N
#     return N
# N = bit_vec_length()


# NOTE: we used to have it where we declared a fixed set of variables.
# a, b, c = BitVecs("a b c", N)
# r, s, t = BitVecs("r s t", N)
# u, v, w = BitVecs("u v w", N)
# x, y, z = BitVecs("x y z", N)

# NOTE: variables are now declared inside each function where they are used.
# QUESTIONS: is there a clear reason to prefer one way over the other?
# is it possible/desirable to avoid use of 'Exists' entirely?


def make_constraints(verify, falsify, possible, N, w):
    def non_null_verify(bit_s, atom):
        """bit_s verifies atom and is not the null state"""
        return And(Not(bit_s == 0), verify(bit_s, atom))

    def non_null_falsify(bit_s, atom):
        """bit_s verifies atom and is not the null state"""
        return And(Not(bit_s == 0), falsify(bit_s, atom))

    def non_triv_verify(bit_s, atom):
        """bit_s verifies atom and is not the null state"""
        return And(non_null_verify(bit_s, atom), possible(bit_s))

    def non_triv_falsify(bit_s, atom):
        """bit_s verifies atom and is not the null state"""
        return And(non_null_falsify(bit_s, atom), possible(bit_s))

    def fusion(bit_s, bit_t):
        """the result of taking the maximum for each index in bit_s and bit_t"""
        return bit_s | bit_t

    def is_part_of(bit_s, bit_t):
        """the fusion of bit_s and bit_t is identical to bit_t"""
        return fusion(bit_s, bit_t) == bit_t

    def compatible(bit_x, bit_y):
        """the fusion of bit_x and bit_y is possible"""
        return possible(fusion(bit_x, bit_y))

    def maximal(bit_w):
        """bit_w includes all compatible states as parts."""
        x = BitVec("max_dummy", N)
        return ForAll(
            x,
            Implies(
                compatible(x, bit_w),
                is_part_of(x, bit_w),
            ),
        )

    def is_world(bit_w):
        """bit_w is both possible and maximal."""
        return And(
            possible(bit_w),
            maximal(bit_w),
        )

    def max_compatible_part(bit_x, bit_w, bit_y):
        """bit_x is the biggest part of bit_w that is compatible with bit_y."""
        z = BitVec("max_part_dummy", N)
        return And(
            is_part_of(bit_x, bit_w),
            compatible(bit_x, bit_y),
            ForAll(
                z,
                Implies(
                    And(
                        is_part_of(z, bit_w), compatible(z, bit_y), is_part_of(bit_x, z)
                    ),
                    bit_x == z,
                ),
            ),
        )

    def is_alternative(bit_u, bit_y, bit_w):
        """
        bit_u is a world that is the alternative that results from imposing state bit_y on world bit_w.
        """
        z = BitVec("alt_dummy", N)
        return And(
            is_world(bit_u),
            is_part_of(bit_y, bit_u),
            Exists(z, And(is_part_of(z, bit_u), max_compatible_part(z, bit_w, bit_y))),
        )

    # NOTE: should throw error if boxright occurs in X
    def extended_verify(state, ext_sent, evaluate=False):
        """X is in prefix form. Same for extended_falsify"""
        if len(ext_sent) == 1:
            # print(state,ext_sent,type(state),type(ext_sent))
            return verify(state, ext_sent[0])
        op = ext_sent[0]
        if "boxright" in op:
            raise ValueError(f"The sentence {ext_sent} is not extensional.")
        if "neg" in op:
            return extended_falsify(state, ext_sent[1])
        Y = ext_sent[1]  # should be a list itself
        Z = ext_sent[2]  # should be a list itself
        if "wedge" in op:
            y = BitVec("ex_ver_dummy_y", N)
            z = BitVec("ex_ver_dummy_z", N)
            if evaluate is True:
                return And(
                    fusion(y, z) == state, extended_verify(y, Y), extended_verify(z, Z)
                )
            return Exists(
                [y, z],
                And(
                    fusion(y, z) == state, extended_verify(y, Y), extended_verify(z, Z)
                ),
            )
        if "vee" in op:
            return Or(
                extended_verify(state, Y),
                extended_verify(state, Z),
                extended_verify(state, ["wedge", Y, Z]),
            )
        if "leftrightarrow" in op:
            return Or(
                extended_verify(state, ["wedge", Y, Z]),
                extended_falsify(state, ["vee", Y, Z]),
            )
        if "rightarrow" in op:
            return Or(
                extended_falsify(state, Y),
                extended_verify(state, Z),
                extended_verify(state, ["wedge", ["neg", Y], Z]),
            )
        raise ValueError(
            f"Something went wrong in extended_verify in evaluating the operator {op} in [{op}, {Y}, {Z}]"
        )

    def extended_falsify(state, ext_sent):
        if len(ext_sent) == 1:
            return falsify(state, ext_sent[0])
        op = ext_sent[0]
        if "boxright" in op:
            raise ValueError(f"The sentence {ext_sent} is not extensional.")
        if "neg" in op:
            return extended_verify(state, ext_sent[1])
        Y = ext_sent[1]
        Z = ext_sent[2]
        if "wedge" in op:
            return Or(
                extended_falsify(state, Y),
                extended_falsify(state, Z),
                extended_falsify(state, ["vee", Y, Z]),
            )
        y = BitVec("ex_fal_dummy_y", N)
        z = BitVec("ex_fal_dummy_z", N)
        # both used in vee and rightarrow cases, but usage is mutually exclusive so can define up here
        if "vee" in op:
            return Exists(
                [y, z],
                And(
                    state == fusion(y, z),
                    extended_falsify(y, Y),
                    extended_falsify(z, Z),
                ),
            )
        if "leftrightarrow" in op:
            return Or(
                extended_verify(state, ["wedge", Y, ["neg", Z]]),
                extended_falsify(state, ["vee", Y, ["neg", Z]]),
            )
        if "rightarrow" in op:
            return Exists(
                [y, z],
                And(
                    state == fusion(y, z), extended_verify(y, Y), extended_falsify(z, Z)
                ),
            )
        raise ValueError(
            f"Something went wrong in extended_verify in evaluating the operator {op} in [{op}, {Y}, {Z}]"
        )

    # NOTE: the true_at/false-at definitions are bilateral to accommodate the fact
    # that the exhaustivity constraint is not included in the definition of props
    # this should avoid the need for specific clauses for (un)negated CFs
    # TODO: linter says all or none of the returns should be an expression
    def true_at(sentence, world):
        """sentence is a sentence in prefix notation"""
        x = BitVec("t_dummy_x", N)
        u = BitVec("t_dummy_u", N)
        if len(sentence) == 1:
            sent = sentence[0]
            return Exists(x, And(is_part_of(x, world), verify(x, sent)))
        op = sentence[0]
        if "neg" in op:
            return false_at(sentence[1], world)
        Y = sentence[1]
        Z = sentence[2]
        if "wedge" in op:
            return And(true_at(Y, world), true_at(Z, world))
        if "vee" in op:
            return Or(true_at(Y, world), true_at(Z, world))
        if "leftrightarrow" in op:
            return Or(
                And(true_at(Y, world), true_at(Z, world)),
                And(false_at(Y, world), false_at(Z, world)),
            )
        if "rightarrow" in op:
            return Or(false_at(Y, world), true_at(Z, world))
        if "boxright" in op:
            return ForAll(
                [x, u],
                Implies(
                    And(extended_verify(x, Y), is_alternative(u, x, world)),
                    true_at(Z, u),
                ),
            )

    # TODO: linter says all or none of the returns should be an expression
    def false_at(sentence, world):
        """X is a sentence in prefix notation"""
        x = BitVec("f_dummy_x", N)
        u = BitVec("f_dummy_u", N)
        if len(sentence) == 1:
            sent = sentence[0]
            return Exists(x, And(is_part_of(x, world), falsify(x, sent)))
        op = sentence[0]
        if "neg" in op:
            return true_at(sentence[1], world)
        Y = sentence[1]
        Z = sentence[2]
        if "wedge" in op:
            return Or(false_at(Y, world), false_at(Z, world))
        if "vee" in op:
            return And(false_at(Y, world), false_at(Z, world))
        if "leftrightarrow" in op:
            return Or(
                And(true_at(Y, world), false_at(Z, world)),
                And(false_at(Y, world), true_at(Z, world)),
            )
        if "rightarrow" in op:
            return And(true_at(Y, world), false_at(Z, world))
        if "boxright" in op:
            return Exists(
                [x, u],
                And(extended_verify(x, Y), is_alternative(u, x, world), false_at(Z, u)),
            )

    def prop_const(atom):
        """
        atom is a proposition since its verifiers and falsifiers are closed under
        fusion respectively, and the verifiers and falsifiers for atom are
        incompatible (exclusivity). NOTE: exhaustivity crashes Z3 so left off.
        """
        x = BitVec("prop_dummy_x", N)
        y = BitVec("prop_dummy_y", N)
        sent_to_prop = [
            Exists(x, non_triv_verify(x, atom)),
            Exists(y, non_triv_falsify(y, atom)),
            ForAll(
                [x, y],
                Implies(
                    And(verify(x, atom), verify(y, atom)), verify(fusion(x, y), atom)
                ),
            ),
            ForAll(
                [x, y],
                Implies(
                    And(falsify(x, atom), falsify(y, atom)), falsify(fusion(x, y), atom)
                ),
            ),
            ForAll(
                [x, y],
                Implies(
                    And(falsify(x, atom), falsify(y, atom)), falsify(fusion(x, y), atom)
                ),
            ),
            ForAll(
                [x, y],
                Implies(And(verify(x, atom), falsify(y, atom)), Not(compatible(x, y))),
            ),
            # ForAll( #exhaustivity
            #     x,
            #     Implies(
            #         possible(x),
            #         Exists(
            #             y,
            #             And(
            #                 compatible(x,y),
            #                 Or(verify(y, atom), falsify(y, atom)),
            #             ),
            #         ),
            #     ),
            # ),
        ]
        return sent_to_prop

    def find_frame_constraints():
        """find the constraints that depend only on the sentence letters
        returns a list of Z3 constraints"""
        x = BitVec("frame_dummy_x", N)
        y = BitVec("frame_dummy_y", N)
        z = BitVec("frame_dummy_z", N)
        frame_constraints = [
            ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
            ForAll([x, y], Exists(z, fusion(x, y) == z)),
            is_world(w),
        ]
        return frame_constraints

    # def add_general_constraints(solv, input_sentence_letters):
    #     """adds the constraints that go in every solver"""
    #     possible_part = ForAll(
    #         [x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))
    #     )
    #     solv.add(possible_part)
    #     print(f"\nPossibility constraint:\n {possible_part}\n")
    #     # NOTE: seems to slightly slow things down with no obvious gains but I'm
    #     # still unsure if this is needed or not. would be good to confirm.
    #     fusion_closure = ForAll([x, y], Exists(z, fusion(x, y) == z))
    #     solv.add(fusion_closure)
    #     print(f"Fusion constraint:\n {fusion_closure}\n")
    #     world_const = is_world(w)
    #     solv.add(world_const)
    #     print(f"World constraint: {world_const}")
    #     for sent_letter in input_sentence_letters:
    #         print(f"\nSentence {sent_letter} yields the general constraints:\n")
    #         for const in prop_const(sent_letter):
    #             solv.add(const)
    #             print(f"{const}\n")

    def find_model_constraints(prefix_sents,input_sentence_letters):
        """find constraints corresponding to the input sentences"""
        prop_constraints = []
        for sent_letter in input_sentence_letters:
            for const in prop_const(sent_letter):
                prop_constraints.append(const)
        input_const = []
        for sentence in prefix_sents:
            sentence_constraint = true_at(sentence, w)
            input_const.append(sentence_constraint)
        model_constraints = prop_constraints + input_const
        return model_constraints

    # def add_input_constraints(solv, prefix_sentences):
    #     """add input-specific constraints to the solver"""
    #     for sentence in prefix_sentences:
    #         print(sentence)
    #         sentence_constraint = true_at(sentence, w)
    #         print(
    #             f"Sentence {sentence} yields the model constraint:\n {sentence_constraint}\n"
    #         )
    #         solv.add(sentence_constraint)

    def is_counterfactual(prefix_sentence):
        """returns a boolean to say whether a given sentence is a counterfactual
        used in find_extensional_subsentences"""
        if len(prefix_sentence) == 1:
            return False
        if len(prefix_sentence) == 2:
            return is_counterfactual(prefix_sentence[1])
        if "boxright" in prefix_sentence[0]:
            return True
        return is_counterfactual(prefix_sentence[1]) or is_counterfactual(
            prefix_sentence[2]
        )

    # TODO: linter says all or none of the returns should be an expression
    def all_subsentences_of_a_sentence(prefix_sentence, progress=False):
        """finds all the subsentence of a prefix sentence
        returns these as a set
        used in find_extensional_subsentences"""
        if progress is False:
            progress = []
        # TODO: linter says cannot access member "append" for type "Literal[True]" Member "append" is unknown
        progress.append(prefix_sentence)
        if len(prefix_sentence) == 1:
            return progress
        if len(prefix_sentence) == 2:
            # TODO: linter says cannot access member "append" for type "Literal[True]" Member "append" is unknown
            return all_subsentences_of_a_sentence(prefix_sentence[1], progress)
        if len(prefix_sentence) == 3:
            # TODO: linter says cannot access member "append" for type "Literal[True]" Member "append" is unknown
            left_subsentences = all_subsentences_of_a_sentence(
                prefix_sentence[1], progress
            )
            # TODO: linter says cannot access member "append" for type "Literal[True]" Member "append" is unknown
            right_subsentences = all_subsentences_of_a_sentence(
                prefix_sentence[2], progress
            )
            all_subsentences = left_subsentences + right_subsentences
            return all_subsentences

    def find_extensional_subsentences(prefix_sentences):
        """finds all the extensional subsentences in a list of prefix sentences
        used in find_all_constraints"""
        # all_subsentences = [all_subsentences_of_a_sentence(sent) for sent in prefix_sentences]
        all_subsentences = []
        for prefix_sent in prefix_sentences:
            # TODO: linter says cannot access member "append" for type "Literal[True]" Member "append" is unknown
            all_subsentences.extend(all_subsentences_of_a_sentence(prefix_sent))
        extensional_subsentences = [
            sent for sent in all_subsentences if not is_counterfactual(sent)
        ]
        return extensional_subsentences

    def repeats_removed(L):
        """takes a list and removes the repeats in it.
        used in find_all_constraints"""
        seen = []
        for obj in L:
            if obj not in seen:
                seen.append(obj)
        return seen

    def sentence_letters_in_compound(prefix_input_sentence):
        """finds all the sentence letters in ONE input sentence. returns a list. WILL HAVE REPEATS
        used in all_sentence_letters"""
        if len(prefix_input_sentence) == 1:  # base case: atomic sentence
            return prefix_input_sentence
        # recursive case: complex sentence as input. Should have max 3 elems (binary operator) in this list, but figured eh why not not check, above code should ensure that never happens
        return_list = []
        for part in prefix_input_sentence[1:]:
            return_list.extend(sentence_letters_in_compound(part))
        return return_list

    def all_sentence_letters(prefix_input_sentences):
        """finds all the sentence letters in a list of input sentences. returns as a list with no repeats (sorted for consistency)
        used in find_all_constraints"""
        sentence_letters = set()
        for input in prefix_input_sentences:
            sentence_letters_in_input = sentence_letters_in_compound(input)
            for sentence_letter in sentence_letters_in_input:
                sentence_letters.add(sentence_letter)
        return list(sentence_letters)
        # sort just to make every output the same, given sets aren't hashable

    def find_all_constraints(infix_input_sentences):
        """find Z3 constraints for input sentences
        input_sents are a list of infix sentences"""
        # prefix_premises = [Prefix(input_sent) for input_sent in infix_premises]  # this works
        # prefix_conclusions = [Prefix(input_sent) for input_sent in infix_conclusions]
        # prefix_sentences = prefix_combine(prefix_premises, prefix_conclusions)
        prefix_sentences = [Prefix(input_sent) for input_sent in infix_input_sentences]
        sentence_letters = all_sentence_letters(prefix_sentences)  # this works
        input_const = find_model_constraints(prefix_sentences, sentence_letters)
        # print(sentence_letters)
        # print([type(let) for let in sentence_letters])
        gen_const = find_frame_constraints()
        const = gen_const + input_const
        raw_ext_subsentences = find_extensional_subsentences(prefix_sentences)
        ext_subsentences = repeats_removed(raw_ext_subsentences)
        return (const, sentence_letters, ext_subsentences)

    return find_all_constraints


def solve_constraints(all_constraints): # all_constraints is a list
    """find model for the input constraints if there is any"""
    solver = Solver()
    solver.add(all_constraints)
    result = solver.check(*[all_constraints])
    if result == sat:
        return (True, solver.model())
    return (False, solver.unsat_core())
