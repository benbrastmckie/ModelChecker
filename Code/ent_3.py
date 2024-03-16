# AIM: provide a concrete model that can be used to abstract from to build model generator functions
from z3 import *
from definitions import *
from print import *

# TODO: eventually replace sentence_letters with something more general
sentence_letters = [A, B, C]

solver = Solver()

solver.add(
    # FRAME CONSTRAINTS:
    ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
    # every part of a possible state is possible
    ForAll([x, y], Exists(z, fusion(x, y) == z)),
    # states are closed under fusion

    # MODEL CONSTRAINT
    ForAll(X, proposition(X)),
    # every X of AtomSort is a proposition
    is_world(w),
    # there is a world w

    ForAll(
        [a, v],
        Implies(
            And(verify(a, A), is_alternative(v, a, w)),
            Exists(t, And(
                is_part_of(t, v),
                verify(t, B),
            )),
        ),
    ),
    # A => B is true in w

    ForAll(
        [b, v],
        Implies(
            And(Exists([y,z], And(b == fusion(y,z), verify(y,A), verify(z,B))), is_alternative(u, b, w)),
            Exists(t, And(
                is_part_of(t, u),
                verify(t, C),
            )),
        ),
    ),
    # (A & B) => C is true in w

    non_null_verify(c,A),
    is_alternative(r,c,w),
    is_part_of(s,r),
    falsify(s,C),
    # ~(A => C) is true in w 
)













if solver.check() == sat:
    print("\nThere is a model of:")
    print("A => B")
    print("(A & B) => C")
    print("~(A => C)")
    model = solver.model()
    print_states(model)
    print_evaluation(model, sentence_letters)
    print_propositions(model, sentence_letters)
else:
    print("\nThere are no models of:\n")
    print("A => B")
    print("(A & B) => C")
    print("~(A => C)")