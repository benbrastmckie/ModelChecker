# AIM: provide a concrete model that can be used to abstract from to build model generator functions
from z3 import (
    BitVecVal,
    sat,
    Exists,
    ForAll,
    Implies,
    Solver,
    And,
    Not,
    Or,
)

from definitions import (
    N,
    a,
    b,
    c,
    is_proper_part_of,
    non_null_falsify,
    non_null_verify,
    r,
    s,
    t,
    u,
    v,
    w,
    x,
    y,
    z,
    A,
    B,
    C,
    X,
    fusion,
    is_part_of,
    is_world,
    possible,
    verify,
    falsify,
    is_alternative,
    proposition,
)

from print import print_evaluation, print_propositions, print_states

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
    ForAll(X, proposition(X)),  # every X of AtomSort is a proposition
    # proposition(A),
    # proposition(B),
    # proposition(C),

    # TODO: it should be possible to satisfy these constraints
    # does't seem to be creating any alt_worlds

    # EVAL CONSTRAINTS

    # there is a world w
    is_world(w),

    # A is true in w
    is_part_of(a, w),
    verify(a, A),

    # B is true in w
    is_part_of(b, w),
    verify(b, B),

    # C is true in w
    is_part_of(c, w),
    verify(c, C),

    # A, ~B, C are true in u
    falsify(s, B),
    is_part_of(a, u),
    is_part_of(s, u),
    is_part_of(c, u),
    is_alternative(u,s,w),

    # A, B, ~C are true in v
    falsify(t, C),
    is_part_of(a, v),
    is_part_of(b, v),
    is_part_of(t, v),
    is_alternative(v,t,w),

)

if solver.check() == sat:
    model = solver.model()
    print("\nThere is a model of:")
    print("A, B, C, ~(A => B), ~(A => C)")
    print_states(model)
    print_evaluation(model, sentence_letters)
    print_propositions(model, sentence_letters)
else:
    print("\nThere are no models of:")
    print("A, B, C, ~(A => B), ~(A => C)\n")
