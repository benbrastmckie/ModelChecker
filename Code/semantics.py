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

'''
this file defines the functions needed to generate Z3 constraints from
input_sentences in infix form.
'''


# TODO: use prefix definitions to move from input_sentences to prefix_sentences and sentence_letters

# TODO: define function from sentence_letters (sorted with no repeated entries) to declarations of the following form

A, B, C = Consts('A B C', AtomSort)
X, Y, Z = Consts('X Y Z', AtomSort)

# NOTE: for the time being, I will declare the following
# not sure if it's right to include strings 'boxright', 'vee', etc
prefix_sentences = [['boxright', A, ['vee', B, C]], ['neg', ['boxright', A, B]], ['neg', ['boxright', A, C]]]
sentence_letters = [A, B, C]

# NOTE: for now we may declare a fixed set of variables
# however, it is likely that at some point these definitions will have to be an
# output along with the constraints generated
a, b, c = BitVecs("a b c", N)
r, s, t = BitVecs("r s t", N)
u, v, w = BitVecs("u v w", N)
x, y, z = BitVecs("x y z", N)


# # NOTE: would this replace the definition of proposition in `definitions.py` at some point?
# def proposition(atomic_sentence):
#     """requires a sentence letter to be a proposition"""
#     return (
#         ForAll([x,y], Implies(And(verify(x,atomic_sentence), verify(y,atomic_sentence)), verify(fusion(x,y),atomic_sentence))),
#         ForAll([x,y], Implies(And(falsify(x,atomic_sentence), falsify(y,atomic_sentence)), falsify(fusion(x,y),atomic_sentence))),
#         ForAll([x,y], Implies(And(verify(x,atomic_sentence), falsify(y,atomic_sentence)), Not(possible(fusion(x,y))))),
#         # ForAll(x, Implies(possible(x), Exists(y, And(possible(fusion(x,y)), Or(verify(y,atomic_sentence), falsify(y,atomic_sentence)))))),
#         # B: we need to leave this last condition off until we know why it is crashing z3
#     )
# NOTE: why not use the definition of proposition in definitions.py?
# for S in sentence_letters:
#     for proposition_constraint in proposition(S):
#         solver.add(proposition_constraint)

solver = Solver()

# TODO: check that this makes sense in place of the commented out alternative
# above. maybe I missed what the idea was supposed to be
# NOTE: alternatively we could use a for-loop through sentence_letters here
# might be worth experimenting with: could this fix the fact that ver_bits
# are not currently closed under fusion?
solver.add(ForAll(X, proposition(X)))

# TEST PRINT
# print (solver.check())
# model = solver.model()
# print (model)
# print ("interpretation assigned to AtomSort:")
# print (model[AtomSort])

# frame constraints
solver.add(ForAll([x,y], Implies(And(possible(x), is_part_of(x,y)), possible(y))))

# evaluation constraints
solver.add(is_world(w))


def true_at(X, w):
    '''X is a sentence in prefix notation'''
    if len(X) == 1:
        return Exists(x, And(is_part_of(x,w), verify(x,A)))
    op = X[0]
    if 'neg' in op:
        return false_at(X, w)
    Y = X[1]
    Z = X[2]
    if 'wedge' in op:
        return And(true_at(Y, w), true_at(Z, w))
    if 'vee' in op:
        return Or(true_at(Y, w), true_at(Z, w))
    if 'leftrightarrow' in op:
        return Or(And(true_at(Y, w), true_at(Z, w)), And(false_at(Y, w), false_at(Z, w)))
    if 'rightarrow' in op:
        return Or(false_at(Y, w), true_at(Z, w))
    if 'boxright' in op:
        return ForAll([x,u], Implies(And(extended_verify(x, Y), is_alternative(u, x, w)), true_at(u, Z)))

def false_at(X, w):
    '''X is a sentence in prefix notation'''
    if len(X) == 1:
        return Exists(x, And(is_part_of(x,w), falsify(x,A)))
    op = X[0]
    if 'neg' in op:
        return true_at(X, w)
    Y = X[1]
    Z = X[2]
    if 'wedge' in op:
        return And(true_at(Y, w), true_at(Z, w))
    if 'vee' in op:
        return Or(true_at(Y, w), true_at(Z, w))
    if 'leftrightarrow' in op:
        return Or(And(true_at(Y, w), true_at(Z, w)), And(Not(true_at(Y, w)), Not(true_at(Z, w))))
    if 'rightarrow' in op:
        return Or(Not(true_at(Y, w)), true_at(Z, w))
    if 'boxright' in op:
        return ForAll([x,u], Implies(And(extended_verify(x,Y),alternative(x, w,u)), true_at(u,Z)))

for sentence in prefix_sentences:
    solver.add(true_at(sentence, w))







# M: we could redefine this function to take as input the output of tokenize in prefix_infix, I think. Do we want?
# B: this says of a sentence X (of any complexity) that it is true at w.
# we will want to pass it sentences in prefix notation, but it is of very general utility.
# for this reason I'm thinking that it deserves to be its own function.
# but maybe I missed your question?
def Semantics(X, w): # LINT: all or none of the return statements should be an expression
    '''sentence X is true at world w'''
    if X[0] in sentence_letters:
        # B: should 'list' be 'sentence_letters'?
        return Exists([x], And(verify(x,X), is_part_of(x,w)))
        # B: better would be to use open sentences but then we need to keep
        # track of which constants have been used. I'm confused why Exists()
        # claims don't seem to give good results.
    if 'neg' in X[0] and 'boxright' not in X[1][0]:
        return Not(Semantics(X, w[1]))
    if 'wedge' in X[0]:
        return And(Semantics(X, w[1]),Semantics(X, w[2]))
    if 'vee' in X[0]:
        return Or(Semantics(X, w[1]),Semantics(X, w[2]))
    if 'boxright' in X[0]:
        return ForAll([s, v], Implies(And(extended_verify(s,X[1]), is_alternative(v, s, w)), Semantics(v,X[2])))
    if 'neg' in X[0] and 'boxright' in X[1][0]:
        return Exists([s, v], And(extended_verify(s,X[1]), is_alternative(v, s, w), Not(Semantics(v,X[2]))))
    else:
        return print("Input Error")
    # B: there are some issues with existential quantifiers that I don't fully understand
    # might be better to just use new constants


# NOTE: should throw error if boxright occurs in X
def extended_verify(x,X):
    '''X is in prefix form. Same for extended_falsify'''
    if len(X) == 1:
        return verify(x,X)
    op = X[0]
    if 'neg' in op:
        if 'boxright' in X[1][0]:
            raise ValueError(f"Problem with sentences: {X}, {X[1]}, {X[1][0]}")
        return extended_falsify(x,X[1])
    Y = X[1]
    Z = X[2]
    if 'wedge' in op:
        return Exists([y,z], And(x == fusion(y,z), extended_verify(y,Y), extended_verify(z,Z)))
    if 'vee' in op:
        return Or(extended_verify(x,Y), extended_verify(x,Z), extended_verify(x,['wedge', Y, Z]))
    if 'leftrightarrow' in op:
        return Or(extended_verify(x,['wedge', Y, Z]), extended_falsify(x,['vee', Y, Z]))
    if 'rightarrow' in op:
        return Or(extended_falsify(x,Y), extended_verify(x,Z), extended_verify(x,['wedge', ['neg', Y], Z]))
    raise ValueError(f'something went up in extended_verify, most likely operation not found: {op}')

def extended_falsify(x,X):
    if len(X) == 1:
        return falsify(x,X)
    op = X[0]
    if 'neg' in op:
        return extended_verify(x,X[1])
    Y = X[1]
    Z = X[2]
    if 'wedge' in op:
        return Or(extended_falsify(x,Y), extended_falsify(x,Z), extended_falsify(x,['wedge', Y, Z]))
    if 'vee' in op:
        return Exists([y,z], And(x == fusion(y,z), extended_falsify(y,Y), extended_falsify(z,Z)))
    if 'leftrightarrow' in op:
        return Or(extended_verify(x,['wedge', Y, ['neg', Z]]), extended_falsify(x, ['vee', ['neg', Y], Z]))
    if 'rightarrow' in op:
        return Exists([y,z], And(x == fusion(y,z), extended_verify(y,Y), extended_falsify(z, Z)))
    raise ValueError(f'something went up in extended_falsify, most likely operation not found: {op}')
