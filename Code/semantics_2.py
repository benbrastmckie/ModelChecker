from z3 import (
    # Solver,
    # sat,
    # simplify,
    Exists,
    ForAll,
    Implies,
    Or,
    BitVec,
    BitVecs,
    Not,
    DeclareSort,
    Consts,
    Solver,
    BoolSort,
    BitVecSort,
    Function,
    And,
)

from definitions import (
    N,
    fusion,
    is_alternative,
    is_part_of,
    possible,
    is_world,
    AtomSort,
    proposition,
    verify,
    non_null_verify,
    falsify,
    non_null_falsify,
    # alternative,
)

# from sympy import symbols, Or, And, Implies, Not, to_cnf

"""
this file defines the functions needed to generate Z3 constraints from
input_sentences in infix form.
"""


# TODO: use prefix definitions to move from input_sentences to prefix_sentences and sentence_letters

# TODO: define function from sentence_letters (sorted with no repeated entries) to declarations of the following form

A, B, C = Consts("A B C", AtomSort)
X, Y, Z = Consts("X Y Z", AtomSort)

# NOTE: for the time being, I will declare the following
# not sure if it's right to include strings 'boxright', 'vee', etc
prefix_sentences = [
    ["boxright", [A], ["vee", [B], [C]]],
    ["neg", ["boxright", [A], [B]]],
    ["neg", ["boxright", [A], [C]]],
]
sentence_letters = [A, B, C]

# NOTE: for now we may declare a fixed set of variables
# however, it is likely that at some point these definitions will have to be an
# output along with the constraints generated
a, b, c = BitVecs("a b c", N)
r, s, t = BitVecs("r s t", N)
uu, vv, w = BitVecs("u v w", N)
xx, yy, zz = BitVecs("x y z", N)


def add_general_constraints(solver):
    '''adds the constraints that go in every solver'''
    solver.add(ForAll(X, proposition(X)))
    solver.add(ForAll([xx, yy], Implies(And(possible(xx), is_part_of(xx, yy)), possible(yy))))
    solver.add(is_world(w))

# NOTE: should throw error if boxright occurs in X
def extended_verify(state, ext_sent):
    """X is in prefix form. Same for extended_falsify"""
    if len(ext_sent) == 1:
        # print(state,ext_sent,type(state),type(ext_sent))
        return verify(state, ext_sent[0])
    op = ext_sent[0]
    if "boxright" in op:
        raise ValueError(f"The sentence {ext_sent} is not extensional.")
    if "neg" in op:
        return extended_falsify(state, ext_sent[1])
    Y = ext_sent[1]
    Z = ext_sent[2]
    if "wedge" in op:
        y = BitVec('dummy',N)
        z = BitVec('dummy',N)
        return And(state == fusion(y, z), extended_verify(y, Y), extended_verify(z, Z))
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
        return falsify(state, ext_sent)
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
        y = BitVec('dummy',N)
        z = BitVec('dummy',N)
        return And(state == fusion(y, z), extended_falsify(y, Y), extended_falsify(z, Z))
    if "leftrightarrow" in op:
        return Or(
            extended_verify(state, ["wedge", Y, ["neg", Z]]),
            extended_falsify(state, ["vee", Y, ["neg", Z]]),
        )
    if "rightarrow" in op:
        y = BitVec('dummy',N)
        z = BitVec('dummy',N)
        return And(state == fusion(y, z), extended_verify(y, Y), extended_falsify(z, Z))
    raise ValueError(
        f"Something went wrong in extended_verify in evaluating the operator {op} in [{op}, {Y}, {Z}]"
    )


# NOTE: the true_at/false-at definitions are bilatteral to accommodate the fact
# that the exhaustivity constraint is not included in the definition of props
# this should avoid the need for specific clauses for (un)negated CFs
def true_at(sentence, world):
    """sentence is a sentence in prefix notation"""
    if len(sentence) == 1:
        sent = sentence[0]
        x = BitVec('dummy',N)
        return And(is_part_of(x, world), verify(x, sent))
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
            [xx, uu],
            Implies(
                And(extended_verify(xx, Y), is_alternative(uu, xx, world)), true_at(Z, uu)
            ),
        )


def false_at(sentence, world):
    """X is a sentence in prefix notation"""
    if len(sentence) == 1:
        sent = sentence[0]
        x = BitVec('dummy',N)
        return And(is_part_of(x, world), falsify(x, sent))
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
        x = BitVec('dummy',N)
        u = BitVec('dummy',N)
        return And(extended_verify(x, Y), is_alternative(u, x, world), false_at(Z, u))

def add_input_constraints(solver, prefix_sentences):
    '''add input-specific constraints to the solver'''
    for sentence in prefix_sentences:
        solver.add(true_at(sentence, w))