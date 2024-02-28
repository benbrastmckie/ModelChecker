from z3 import *
from states import *

# NOTE: I think this makes X, Y have the sort Atoms... not sure this is useful
AtomSort = DeclareSort('Atom')
X, Y = Consts('X Y', AtomSort) 

# NOTE: want 'verify' to be a function that takes a bitvector and sentence as input and a truth-value as output
verify = Function("verify", BitVecSort(8), AtomSort, BoolSort()) 
falsify = Function("falsify", BitVecSort(8), AtomSort, BoolSort())

def proposition(X):
    return (
        ForAll([x,y], Implies(And(verify(x,X), verify(y,X)), verify(fusion(x,y),X))),
        ForAll([x,y], Implies(And(falsify(x,X), falsify(y,X)), falsify(fusion(x,y),X))),
        ForAll([x,y], Implies(And(verify(x,X), falsify(y,X)), Not(possible(fusion(x,y))))),
        ForAll([x,y], Implies(possible(x), And(possible(fusion(x,y)), Or(verify(y,X), falsify(y,X))))),
        # M to B: what do you have in mind in terms of regimentation when you write "where"?
        #not sure if I'm doing 4 right, couldn't find 5
    )

solver = Solver()

sentence_letters = []
for X in sentence_letters:
    for proposition_constraint in proposition(X):
        solver.add(proposition_constraint)


# frame constraints
ForAll([x,y], Implies(And(possible(x), fusion(x,y) == x), possible(y)))

# evaluation constraints
# not sure how to proceed. How are we making worlds?

def Alternatives(u,w,X):
    '''Given a world w and sentence X, the function Alternatives(u,w,X) yields the following Z3 constraints:
            State(x) where Verify(x,X) and fusion(x,u) = u.
            State(y) where fusion(y,w) = w and fusion(y,u) = u.
            If State(z), fusion(z,w) = w, Possible(fusion(x,z)), and fusion(y,z) = z, then y = z.'''
    pass #TODO
    # M to B: what do you have in mind in terms of regimentation when you write "where"?



def Semantics(w,X):
    '''w is a world, X is a sentence'''
    if 'neg' in X[0]:
        return Not(Semantics(w,X[1]))
    elif 'wedge' in X[0]:
        return And(Semantics(w,X[1]),Semantics(s,X[2]))
    elif 'vee' in X[0]:
        return Or(Semantics(w,X[1]),Semantics(s,X[2]))
    elif 'boxright' in X[0]:
        pass
        # what if box or boxright occur in Y?
    elif 'box' in X[0]:
        pass
        # what if box or boxright occur in Y?
    elif isinstance(X[0],list): # atomic
        return Exists([x], (verify(x,X), fusion(x,w) == w)) # Ben, can you check that I am interpreting this right? I think an existential is missing in the strat doc for this
    
# also missing general constraints at very bottom of Strategies