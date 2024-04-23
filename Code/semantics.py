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
from convert_syntax import (
    Prefix,
    all_sentence_letters,
)
from definitions import (
    N,
    w,
    fusion,
    is_alternative,
    is_part_of,
    possible,
    is_world,
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

def prop_const(atom):
    """
    atom is a proposition since its verifiers and falsifiers are closed under
    fusion respectively, and the verifiers and falsifiers for atom are
    incompatible (exhaustivity). NOTE: exclusivity crashes Z3 so left off.
    """
    x =  BitVec('prop_dummy_x', N)
    y =  BitVec('prop_dummy_y', N)
    # a =  BitVec('prop_const_dummy_a', N)
    # b =  BitVec('prop_const_dummy_b', N)
    sent_to_prop = [
        # NOTE: should we include declarations of a and b above to
        # avoid 'Exists' below?
        # non_null_verify(a, atom),
        # non_null_falsify(b, atom),
        Exists(x, non_null_verify(x, atom)),
        Exists(y, non_null_falsify(y, atom)),
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


def find_frame_constraints(input_sentence_letters):
    """find the constraints that depend only on the sentence letters
    returns a list of Z3 constraints"""
    x =  BitVec('frame_dummy_x', N)
    y =  BitVec('frame_dummy_y', N)
    z =  BitVec('frame_dummy_z', N)
    frame_constraints = [
        ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
        ForAll([x, y], Exists(z, fusion(x, y) == z)),
        is_world(w),
    ]
    # for const in prop_const(X):
    #     frame_constraints.append(const)
    # NOTE: above appears to admit models for weakening the antecedent
    # NOTE: also appears to avoid crashing Z3 with the exhaustivity constraint
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
        y =  BitVec('ex_ver_dummy_y', N)
        z =  BitVec('ex_ver_dummy_z', N)
        if evaluate is True:
            return And(fusion(y, z) == state, extended_verify(y, Y), extended_verify(z, Z))
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
    y =  BitVec('ex_fal_dummy_y', N)
    z =  BitVec('ex_fal_dummy_z', N) # both used in vee and rightarrow cases, but usage is mutually exclusive so can define up here
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
# TODO: linter says all or none of the returns should be an expression
def true_at(sentence, world):
    """sentence is a sentence in prefix notation"""
    x = BitVec('t_dummy_x', N)
    u = BitVec('t_dummy_u', N)
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
                And(extended_verify(x, Y), is_alternative(u, x, world)), true_at(Z, u)
            ),
        )


# TODO: linter says all or none of the returns should be an expression
def false_at(sentence, world):
    """X is a sentence in prefix notation"""
    x = BitVec('f_dummy_x', N)
    u = BitVec('f_dummy_u', N)
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


def find_model_constraints(prefix_sents):
    """find constraints corresponding to the input sentences"""
    input_const = []
    for sentence in prefix_sents:
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


def find_all_constraints(infix_input_sentences):
    """find Z3 constraints for input sentences
    input_sents are a list of infix sentences"""
    # prefix_premises = [Prefix(input_sent) for input_sent in infix_premises]  # this works
    # prefix_conclusions = [Prefix(input_sent) for input_sent in infix_conclusions]
    # prefix_sentences = prefix_combine(prefix_premises, prefix_conclusions)
    prefix_sentences = [Prefix(input_sent) for input_sent in infix_input_sentences]
    input_const = find_model_constraints(prefix_sentences)
    sentence_letters = all_sentence_letters(prefix_sentences)  # this works
    # print(sentence_letters)
    # print([type(let) for let in sentence_letters])
    gen_const = find_frame_constraints(sentence_letters)
    const = gen_const + input_const
    ext_subsentences = repeats_removed(find_extensional_subsentences(prefix_sentences))
    return (const, sentence_letters, ext_subsentences)

def repeats_removed(L):
    seen = []
    for obj in L:
        if obj not in seen:
            seen.append(obj)
    return seen

def is_counterfactual(prefix_sentence):
    '''returns a boolean to say whether a given sentence is a counterfactual'''
    if len(prefix_sentence) == 1:
        return False
    if len(prefix_sentence) == 2:
        return is_counterfactual(prefix_sentence[1])
    if 'boxright' in prefix_sentence[0]:
        return True
    return is_counterfactual(prefix_sentence[1]) or is_counterfactual(prefix_sentence[2])


# TODO: linter says all or none of the returns should be an expression
def all_subsentences_of_a_sentence(prefix_sentence, progress=False):
    '''finds all the subsentence of a prefix sentence
    returns these as a set'''
    if progress is False:
        progress = []
    progress.append(prefix_sentence)
    if len(prefix_sentence) == 1:
        return progress
    if len(prefix_sentence) == 2:
        return all_subsentences_of_a_sentence(prefix_sentence[1], progress)
    if len(prefix_sentence) == 3:
        left_subsentences = all_subsentences_of_a_sentence(prefix_sentence[1], progress)
        right_subsentences = all_subsentences_of_a_sentence(prefix_sentence[2], progress)
        all_subsentences = left_subsentences + right_subsentences
        return all_subsentences

def find_extensional_subsentences(prefix_sentences):
    '''finds all the extensional subsentences in a list of prefix sentences'''
    # all_subsentences = [all_subsentences_of_a_sentence(sent) for sent in prefix_sentences]
    all_subsentences = []
    for prefix_sent in prefix_sentences:
        all_subsentences.extend(all_subsentences_of_a_sentence(prefix_sent))
    extensional_subsentences = [sent for sent in all_subsentences if not is_counterfactual(sent)]
    return extensional_subsentences


def solve_constraints(all_constraints): # all_constraints is a list
    """find model for the input constraints if there is any"""
    solver = Solver()
    solver.add(all_constraints)
    result = solver.check(*[all_constraints])
    if result == sat:
        return (True, solver.model())
    # if result == unsat:
    return (False, solver.unsat_core())
    # return (result, None) # NOTE: in what case would you expect this to be triggered?


def infix_combine(prem,con):
    '''combines the premises with the negation of the conclusion(s).
    premises are infix sentences, and so are the conclusions'''
    # if prem is None:
    #     prem = []
    input_sent = prem
    for sent in con:
        neg_sent = '\\neg ' + sent
        input_sent.append(neg_sent)
    return input_sent

def prefix_combine(prem,con):
    '''combines the premises with the negation of the conclusion(s).
    premises are prefix sentences, and so are the conclusions'''
    # if prem is None:
    #     prem = []
    input_sent = prem
    neg_conclusion_sents = [['\\neg ', sent] for sent in con]
    input_sent.extend(neg_conclusion_sents)
    return input_sent
