"""
contains all semantic functions
"""

from z3 import (
    sat,
    Exists,
    ForAll,
    Implies,
    Or,
    BitVecs,
    Not,
    Consts,
    Solver,
    And,
)
from prefix_infix import Prefix, all_sentence_letters
# from test_complete import N
from definitions import (
    N,
    fusion,
    is_alternative,
    is_part_of,
    possible,
    is_world,
    AtomSort,
    compatible,
    verify,
    non_null_verify,
    falsify,
    non_null_falsify,
)

# from sympy import symbols, Or, And, Implies, Not, to_cnf

"""
this file defines the functions needed to generate Z3 constraints from
input_sentences in infix form.
"""


# TODO: define function from sentence_letters (sorted with no repeated entries) to declarations of the following form

A, B, C = Consts("A B C", AtomSort)
X, Y, Z = Consts("X Y Z", AtomSort)

# NOTE: for now we may declare a fixed set of variables
# however, it is likely that at some point these definitions will have to be an
# output along with the constraints generated
a, b, c = BitVecs("a b c", N)
r, s, t = BitVecs("r s t", N)
u, v, w = BitVecs("u v w", N)
x, y, z = BitVecs("x y z", N)


def prop_const(atom):
    """
    atom is a proposition since its verifiers and falsifiers are closed under
    fusion respectively, and the verifiers and falsifiers for atom are
    incompatible (exhaustivity). NOTE: exclusivity crashes Z3 so left off.
    """
    sent_to_prop = [
        Exists(x, non_null_verify(x, atom)),
        Exists(y, non_null_falsify(x, atom)),
        ForAll(
            [x, y],
            Implies(And(verify(x, atom), verify(y, atom)), verify(fusion(x, y), atom)),
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
        # ForAll(
        #     x,
        #     Implies(
        #         possible(x),
        #         Exists(
        #             y,
        #             And(
        #                 possible(fusion(x, y)),
        #                 Or(verify(y, atom), falsify(y, atom)),
        #             ),
        #         ),
        #     ),
        # ),
    ]
    return sent_to_prop


def find_frame_constraints(input_sentence_letters):
    """find the constraints that depend only on the sentence letters"""
    frame_constraints = [
        ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
        ForAll([x, y], Exists(z, fusion(x, y) == z)),
        is_world(w),
    ]
    for sent_letter in input_sentence_letters:
        for const in prop_const(sent_letter):
            frame_constraints.append(const)
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


# NOTE: should throw error if boxright occurs in X
def extended_verify(state, ext_sent):
    """X is in prefix form. Same for extended_falsify"""
    if len(ext_sent) == 1:
        # print(state,ext_sent,type(state),type(ext_sent))
        return non_null_verify(state, ext_sent[0])
    op = ext_sent[0]
    if "boxright" in op:
        raise ValueError(f"The sentence {ext_sent} is not extensional.")
    if "neg" in op:
        return extended_falsify(state, ext_sent[1])
    Y = ext_sent[1]  # should be a list itself
    Z = ext_sent[2]  # should be a list itself
    if "wedge" in op:
        return Exists(
            [y, z],
            And(fusion(y, z) == state, extended_verify(y, Y), extended_verify(z, Z)),
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
        return non_null_falsify(state, ext_sent[0])
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
    if "vee" in op:
        return Exists(
            [y, z],
            And(state == fusion(y, z), extended_falsify(y, Y), extended_falsify(z, Z)),
        )
    if "leftrightarrow" in op:
        return Or(
            extended_verify(state, ["wedge", Y, ["neg", Z]]),
            extended_falsify(state, ["vee", Y, ["neg", Z]]),
        )
    if "rightarrow" in op:
        return Exists(
            [y, z],
            And(state == fusion(y, z), extended_verify(y, Y), extended_falsify(z, Z)),
        )
    raise ValueError(
        f"Something went wrong in extended_verify in evaluating the operator {op} in [{op}, {Y}, {Z}]"
    )


# NOTE: the true_at/false-at definitions are bilateral to accommodate the fact
# that the exhaustivity constraint is not included in the definition of props
# this should avoid the need for specific clauses for (un)negated CFs
def true_at(sentence, world):
    """sentence is a sentence in prefix notation"""
    if len(sentence) == 1:
        sent = sentence[0]
        return Exists(x, And(is_part_of(x, world), non_null_verify(x, sent)))
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
                And(extended_verify(x, Y), is_alternative(u, x, world)), true_at(Z, u)
            ),
        )


def false_at(sentence, world):
    """X is a sentence in prefix notation"""
    if len(sentence) == 1:
        sent = sentence[0]
        return Exists(x, And(is_part_of(x, world), non_null_falsify(x, sent)))
    op = sentence[0]
    if "neg" in op:
        return true_at(sentence, world)
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


def find_model_constraints(prefix_sent):
    """find constraints corresponding to the input sentences"""
    input_const = []
    for sentence in prefix_sent:
        sentence_constraint = true_at(sentence, w)
        input_const.append(sentence_constraint)
    return input_const


# def add_input_constraints(solv, prefix_sentences):
#     """add input-specific constraints to the solver"""
#     for sentence in prefix_sentences:
#         print(sentence)
#         sentence_constraint = true_at(sentence, w)
#         print(
#             f"Sentence {sentence} yields the model constraint:\n {sentence_constraint}\n"
#         )
#         solv.add(sentence_constraint)


def find_all_constraints(input_sent):
    """find Z3 constraints for input sentences"""
    prefix_sentences = [Prefix(input_sent) for input_sent in input_sent]  # this works
    input_const = find_model_constraints(prefix_sentences)
    sentence_letters = all_sentence_letters(prefix_sentences)  # this works
    gen_const = find_frame_constraints(sentence_letters)
    const = gen_const + input_const
    return (const, sentence_letters)


def solve_constraints(const):
    """find model for the input constraints if there is any"""
    solver = Solver()
    solver.add(const)
    check = solver.check()
    if check == sat:
        return solver.model()
    return None
