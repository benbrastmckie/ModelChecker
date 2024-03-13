from z3 import (
    # Solver,
    # sat,
    # simplify,
    Exists,
    ForAll,
    Implies,
    Or,
    BitVec,
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
    is_part_of,
    possible,
    is_world,
    alternative,
)

# NOTE: I think this makes atomic_sentence, Y have the sort Atoms... not sure this is useful
AtomSort = DeclareSort('AtomSort')
A, B = Consts('A B', AtomSort)

# NOTE: N is defined in states.md
x = BitVec("x", N)
y = BitVec("y", N)
z = BitVec("z", N)
w = BitVec("w", N)
u = BitVec("u", N)

# NOTE: want 'verify' to be a function from a bitvector and sentence to a truth-value
verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())

def proposition(atomic_sentence):
    """requires a sentence letter to be a proposition"""
    return (
        ForAll([x,y], Implies(And(verify(x,atomic_sentence), verify(y,atomic_sentence)), verify(fusion(x,y),atomic_sentence))),
        ForAll([x,y], Implies(And(falsify(x,atomic_sentence), falsify(y,atomic_sentence)), falsify(fusion(x,y),atomic_sentence))),
        ForAll([x,y], Implies(And(verify(x,atomic_sentence), falsify(y,atomic_sentence)), Not(possible(fusion(x,y))))),
        # ForAll(x, Implies(possible(x), Exists(y, And(possible(fusion(x,y)), Or(verify(y,atomic_sentence), falsify(y,atomic_sentence)))))),
        # B: we need to leave this last condition off until we know why it is crashing z3
    )

solver = Solver()

sentence_letters = [A, B]
for S in sentence_letters:
    for proposition_constraint in proposition(S):
        solver.add(proposition_constraint)

print (solver.check())
model = solver.model()
print (model)
print ("interpretation assigned to AtomSort:")
print (model[AtomSort])


# frame constraints
solver.add(ForAll([x,y], Implies(And(possible(x), is_part_of(x,y)), possible(y))))

# evaluation constraints
solver.add(is_world(w))

def Alternatives(u,w,X):
    '''
    Given a world w and sentence X, the function Alternatives(u,w,X) yields the following Z3 constraints:
        verify(x,X) and is_part_of(x,u)
        is_part_of(y,w), compatible(y,x), and is_part_of(y,u)
        for any z, if is_part_of(z,w), compatible(z,x), and is_part_of(y,z), then y = z
    '''
    pass #TODO

# M: we could redefine this function to take as input the output of tokenize in prefix_infix, I think. Do we want?
# B: this says of a sentence X (of any complexity) that it is true at w.
# we will want to pass it sentences in prefix notation, but it is of very general utility.
# for this reason I'm thinking that it deserves to be its own function.
# but maybe I missed your question?
def Semantics(w,X): # LINT: all or none of the return statements should be an expression
    '''sentence X is true at world w'''
    if isinstance(X[0],list):
        # B: should 'list' be 'sentence_letters'?
        return Exists([x], And(verify(x,X), is_part_of(x,w)))
        # B: better would be to use open sentences but then we need to keep
        # track of which constants have been used. I'm confused why Exists()
        # claims don't seem to give good results.
    if 'neg' in X[0] and 'boxright' not in X[1][0]:
        return Not(Semantics(w,X[1]))
    if 'wedge' in X[0]:
        return And(Semantics(w,X[1]),Semantics(w,X[2]))
    if 'vee' in X[0]:
        return Or(Semantics(w,X[1]),Semantics(w,X[2]))
    if 'boxright' in X[0]:
        return ForAll([s, v], Implies(And(extended_verify(s,X[1]), is_alternative(v, s, w)), Semantics(v,X[2])))
    if 'neg' in X[0] and 'boxright' not in X[1][0]:
        return Exists([s, v], And(extended_verify(s,X[1]), is_alternative(v, s, w), Not(Semantics(v,X[2]))))
    else:
        return print("Input Error")
    # B: this looks good, though there are some issues with existential quantifiers that I don't fully understand
    # might be better to just use new constants


def extended_verify(x,X):
    '''X is in prefix form. Same for extended_falsify'''
    if len(X) == 1:
        return verify(x,X)
    op = X[0]
    if 'neg' in op:
        return extended_falsify(x,X[1])
    Y = X[1]
    Z = X[2]
    if 'wedge' in op:
        return Exists([y,z], And(x == fusion(y,z), extended_verify(y,Y), extended_verify(z,Z)))
    elif 'vee' in op:
        return Or(extended_verify(x,Y), extended_verify(x,Z), extended_verify(x,['wedge', Y, Z]))
    elif 'leftrightarrow' in op:
        return Or(extended_verify(x,['wedge', Y, Z]), extended_falsify(x,['vee', Y, Z]))
    elif 'rightarrow' in op:
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
    elif 'vee' in op:
        return Exists([y,z], And(x == fusion(y,z), extended_falsify(y,Y), extended_falsify(z,Z)))
    elif 'leftrightarrow' in op:
        return Or(extended_verify(x,['wedge', Y, ['neg', Z]]), extended_falsify(x, ['vee', ['neg', Y], Z]))
    elif 'rightarrow' in op:
        return Exists([y,z], And(x == fusion(y,z), extended_verify(y,Y), extended_falsify(z, Z)))
    raise ValueError(f'something went up in extended_falsify, most likely operation not found: {op}')

def true(w,X):
    '''X is in prefix function'''
    if len(X) == 1:
        return Exists(x, And(is_part_of(x,w), verify(x,A)))
    op = X[0]
    if 'neg' in op:
        return Not(true(w,X))
    Y = X[1]
    Z = X[2]
    if 'wedge' in op:
        return And(true(w,Y), true(w,Z))
    if 'vee' in op:
        return Or(true(w,Y), true(w,Z))
    if 'leftrightarrow' in op:
        return Or(And(true(w,Y), true(w,Z)), And(Not(true(w,Y)), Not(true(w,Z))))
    if 'rightarrow' in op:
        return Or(Not(true(w,Y)), true(w,Z))
    if 'boxright' in op:
        ForAll([x,u], Implies(And(extended_verify(x,Y),alternative(w,x,u)), true(u,Z)))
