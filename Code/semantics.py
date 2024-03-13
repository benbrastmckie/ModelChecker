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
    return (
        ForAll([x,y], Implies(And(verify(x,atomic_sentence), verify(y,atomic_sentence)), verify(fusion(x,y),atomic_sentence))),
        ForAll([x,y], Implies(And(falsify(x,atomic_sentence), falsify(y,atomic_sentence)), falsify(fusion(x,y),atomic_sentence))),
        ForAll([x,y], Implies(And(verify(x,atomic_sentence), falsify(y,atomic_sentence)), Not(possible(fusion(x,y))))),
        ForAll(x, Implies(possible(x), Exists(y, And(possible(fusion(x,y)), Or(verify(y,atomic_sentence), falsify(y,atomic_sentence)))))),
    )

solver = Solver()

sentence_letters = [] # NOTE: adding A, B these seemed to crash the model
for S in sentence_letters:
    for proposition_constraint in proposition(S):
        solver.add(proposition_constraint)

print (solver.check())
model = solver.model()
print (model)
print ("interpretation assigned to AtomSort:")
print (model[AtomSort])


# frame constraints
ForAll([x,y], Implies(And(possible(x), fusion(x,y) == x), possible(y)))
# QUESTION: why not use is_part_of?

# evaluation constraints
# not sure how to proceed. How are we making worlds?
ForAll(w,Implies(is_world(w), possible(w)))
    # made an is_world Function (ie, not python function but Z3 Function) in states.py
ForAll([x,w], Implies(And(is_world(w), possible(x), possible(fusion(x,w))), fusion(x,w) == w))
    # added implicit is_world(w) constraint
    # the last evaluation constraint is already accounted for in the for loop above
    # B: why not use is_part_of here?
    # B: can is_world be defined in states.md in a manner similar to is_part_of?
    # B: or perhaps equivalence can be required with the following:
ForAll(w, Implies(And(possible(w),
                      ForAll(x, Implies(possible(fusion(x,w)),
                                        is_part_of(x,w)))),
                  is_world(w)))

def Alternatives(u,w,X):
    '''
    Given a world w and sentence X, the function Alternatives(u,w,X) yields the following Z3 constraints:
        verify(x,X) and is_part_of(x,u)
        is_part_of(y,w), compatible(y,x), and is_part_of(y,u)
        for any z, if is_part_of(z,w), compatible(z,x), and is_part_of(y,z), then y = z
    '''
    pass #TODO
    # M: what do you have in mind in terms of regimentation when you write "where"? have some thoughts in my notebook
    # B: fixed, though it might make more sense to define a function from possible_bits and sentence_letters to alternative_bits

# M: we could redefine this function to take as input the output of tokenize in prefix_infix, I think. Do we want?
# B: this says of an extensional sentence X (of any complexity) that it is true at w.
# we will want to pass it sentences in prefix_infix notation, but it is of very general utility.
# for this reason I'm thinking that it deserves to be its own function. but maybe I missed your question?

def Semantics(w,X): 
    '''sentence X is true at world w'''
    if 'neg' in X[0]:
        return Not(Semantics(w,X[1]))
    elif 'wedge' in X[0]:
        return And(Semantics(w,X[1]),Semantics(w,X[2]))
    elif 'vee' in X[0]:
        return Or(Semantics(w,X[1]),Semantics(w,X[2]))
    elif 'boxright' in X[0]:
        pass
        # M: what if box or boxright occur in Y?
        # B: we will need clauses for those that employ extended_verify/extended_falsify
        # the cleanest may be to think of the final elif as 'counterfactual or atomic'
        # and replace verify with extended_verify... let's chat more about this
    elif 'box' in X[0]:
        pass
        # M: what if box or boxright occur in Y?
    elif isinstance(X[0],list): # atomic
        return Exists([x], And(verify(x,X), is_part_of(x,w))) 
    # M: can you check that I am interpreting this right? I think an existential is missing in the strat doc for this
    # B: this looks good, though there are some issues with existential quantifiers that I don't fully understand
    # might be better to just use new constants

    # B: these seem to be shaping up nicely!

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
