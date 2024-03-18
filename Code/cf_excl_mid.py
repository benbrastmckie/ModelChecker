# AIM: provide a concrete model that can be used to abstract from to build model generator functions
from z3 import (
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
    a,
    b,
    c,
    is_atomic,
    non_null_falsify,
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
    is_proper_part_of,
    non_null_verify,
)

# import multiprocessing

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
    ForAll(X, proposition(X)),
    # every X of AtomSort is a proposition
    is_world(w),
    # there is a world w
    is_proper_part_of(c, w),
    # is_part_of(c, w),
    non_null_falsify(c, A),
    # \neg A in w
    # something remains unchanged
    ForAll(
        [s, v],
        Implies(
            And(verify(s, A), is_alternative(v, s, w)),
            Exists(t, And(
                is_part_of(t, v),
                Or(
                    verify(t, B), # should this be s or t?
                    verify(t, C), # should this be s or t?
                    Exists(
                        [a, b],
                        And(
                            t == fusion(a, b), # should this be s or t?
                            verify(a, B),
                            verify(b, C),
                        ),
                    ),
                ),
            )),
        ),
    ),
    # A \boxright B \vee C in w
    non_null_verify(a, A),
    is_alternative(u, a, w),
    is_proper_part_of(b, u),
    # is_part_of(b, u),
    non_null_falsify(b, B),
    # \neg(A \boxright B) in w
    non_null_verify(s, A),
    is_alternative(v, s, w),
    is_proper_part_of(t, v),
    # is_part_of(t, v),
    non_null_falsify(t, C),
    # \neg(A \boxright C)
)


if solver.check() == sat:
    print("\nThere is a model of:")
    print("A => B v C")
    print("~(A => B)")
    print("~(A => C)")
    model = solver.model()
    print_states(model)
    print_evaluation(model, sentence_letters)
    print_propositions(model, sentence_letters)
else:
    print("\nThere are no models of:\n")
    print("A => B v C")
    print("~(A => B)")
    print("~(A => C)\n")
