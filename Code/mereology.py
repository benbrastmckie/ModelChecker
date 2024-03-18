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
sentence_letters = [A, B]

solver = Solver()

solver.add(

    # FRAME CONSTRAINTS:
    ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
    # every part of a possible state is possible
    ForAll([x, y], Exists(z, fusion(x, y) == z)),
    # states are closed under fusion

    # MODEL CONSTRAINT
    ForAll(X, proposition(X)),  # every X of AtomSort is a proposition

    # TODO: right now there seems to be a world that is a proper part of another.

    # EVAL CONSTRAINTS
    is_world(w),
    # there is a world w
    is_proper_part_of(a, w),
    non_null_verify(a, A),
    Not(non_null_verify(a, B)),
    # A is true in w
    is_proper_part_of(b, w),
    non_null_verify(b, B),
    Not(non_null_verify(b, A)),
    # B is true in w
    is_world(u),
    # there is a world w
    is_proper_part_of(s, u),
    non_null_verify(s, A),
    # A is true in w
    is_proper_part_of(t, u),
    non_null_verify(t, B),
    # B is true in w

)

if solver.check() == sat:
    model = solver.model()
    print("\nThere is a model of:")
    print("A, B are true in w")
    print_states(model)
    print_evaluation(model, sentence_letters)
    print_propositions(model, sentence_letters)
else:
    print("\nThere are no models of:")
    print("A, B, A => B\n")
