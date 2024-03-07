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
    poss,
    is_world,
)

# NOTE: I think this makes atomic_sentence, Y have the sort Atoms... not sure this is useful
AtomSort = DeclareSort('AtomSort')
A, B = Consts('A B', AtomSort)

# NOTE: N is defined in states.md
x = BitVec("x", N)
y = BitVec("y", N)
z = BitVec("z", N)
w = BitVec("w", N)

# NOTE: want 'verify' to be a function from a bitvector and sentence to a truth-value
verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())

def proposition(atomic_sentence):
    return (
        ForAll([x,y], Implies(And(verify(x,atomic_sentence), verify(y,atomic_sentence)), verify(fusion(x,y),atomic_sentence))),
        ForAll([x,y], Implies(And(falsify(x,atomic_sentence), falsify(y,atomic_sentence)), falsify(fusion(x,y),atomic_sentence))),
        ForAll([x,y], Implies(And(verify(x,atomic_sentence), falsify(y,atomic_sentence)), Not(poss(fusion(x,y))))),
        ForAll(x, Implies(poss(x),
                          Exists(y, And(poss(fusion(x,y)), Or(verify(y,atomic_sentence), falsify(y,atomic_sentence)))))),
        # M: what do you have in mind in terms of regimentation when you write "where"?
        # B: Fixed this both here and in the Strategies.md
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
ForAll([x,y], Implies(And(poss(x), fusion(x,y) == x), poss(y)))
# QUESTION: why not use is_part_of?

# evaluation constraints
# not sure how to proceed. How are we making worlds?
ForAll(w,Implies(is_world(w), poss(w)))
    # made an is_world Function (ie, not python function but Z3 Function) in states.py
ForAll([x,w], Implies(And(is_world(w), poss(x), poss(fusion(x,w))), fusion(x,w) == w))
    # added implicit is_world(w) constraint
    # the last evaluation constraint is already accounted for in the for loop above
    # B: why not use is_part_of here?
    # B: can is_world be defined in states.md in a manner similar to is_part_of?
    # B: or perhaps equivalence can be required with the following:
ForAll(w, Implies(And(poss(w),
                      ForAll(x, Implies(poss(fusion(x,w)),
                                        is_part_of(x,w)))),
                  is_world(w)))

def Alternatives(u,w,X):
    '''
    Given a world w and sentence X, the function Alternatives(u,w,X) yields the following Z3 constraints:
        State(x) where Verify(x,X) and fusion(x,u) = u.
        State(y) where fusion(y,w) = w and fusion(y,u) = u.
        If State(z), fusion(z,w) = w, Possible(fusion(x,z)), and fusion(y,z) = z, then y = z.
    '''
    pass #TODO
    # M to B: what do you have in mind in terms of regimentation when you write "where"? have some thoughts in my notebook


def Semantics(w,X): # we could redefine this function to take as input the output of tokenize in prefix_infix, I think. Do we want?
    '''w is a world, X is a sentence'''
    if 'neg' in X[0]:
        return Not(Semantics(w,X[1]))
    elif 'wedge' in X[0]:
        return And(Semantics(w,X[1]),Semantics(w,X[2]))
    elif 'vee' in X[0]:
        return Or(Semantics(w,X[1]),Semantics(w,X[2]))
    elif 'boxright' in X[0]:
        pass
        # what if box or boxright occur in Y?
    elif 'box' in X[0]:
        pass
        # what if box or boxright occur in Y?
    elif isinstance(X[0],list): # atomic
        return Exists([x], And(verify(x,X), fusion(x,w) == w)) # Ben, can you check that I am interpreting this right? I think an existential is missing in the strat doc for this
    
# also missing general constraints at very bottom of Strategies
# issue with these is that verify is constructed to take in AtomSorts, and complex sentences are lists, not AtomSorts. 
    # B: That makes sense. I think I sorted this out in the Strategies.md doc. Let me know what you think.
