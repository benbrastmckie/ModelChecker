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
    # Y,
    fusion,
    is_part_of,
    world,
    possible,
    verify,
    falsify,
    is_alternative,
    compatible_part,
    alternative,
    proposition,
    maximal,
    Equivalent,
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
    # ForAll([x, y], Equivalent(parthood(x, y),is_part_of(x,y))),
    # states are closed under fusion
    ForAll(
        w,
        Equivalent(
            world(w),
            And(possible(w), maximal(w)),
        ),
    ),
    ForAll(
        [u, y],
        Equivalent(  # TODO: replace with Z3 equiv if any?
            alternative(u, y, w),
            And(
                world(u),
                is_part_of(y, u),
                Exists(z, And(is_part_of(z, u), compatible_part(z, w, y))),
            ),
        ),
    ),
    # MODEL CONSTRAINT
    ForAll(X, proposition(X)),  # every X of AtomSort is a proposition
    # EVAL CONSTRAINTS
    world(w),  # there is a world w
    ForAll(  # A \vee B \boxright C
        [s, v],
        Implies(
            And(
                Or(
                    verify(s, A),
                    verify(s, B),
                    Exists(
                        [a, b],
                        And(
                            s == fusion(a, b),
                            verify(a, A),
                            verify(b, B),
                        ),
                    ),
                ),
                is_alternative(v, s, w),
            ),
            Exists(t, And(is_part_of(t, v), verify(t, C))),
        ),
    ),

    verify(r, A),
    is_alternative(v, r, w),
    Exists(t, And(is_part_of(t, v), falsify(t, C))),
)

if solver.check() == sat:
    model = solver.model()
    print("\nThere are models of:\n")
    print("A v B => C")
    print("~(A => C)")
    print("~(B => C)")
    print_states(model)
    print_evaluation(model, sentence_letters)
    print_propositions(model, sentence_letters)
else:
    print("\nThere are no models of:\n")
    print("A v B => C")
    print("~(A => C)")
    print("~(B => C)\n")
