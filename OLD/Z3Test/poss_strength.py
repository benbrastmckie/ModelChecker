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
    compatible,
    d,
    e,
    f,
    g,
    h,
    i,
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
    is_world,
    possible,
    verify,
    falsify,
    is_alternative,
    proposition,
)

from Code.OLD.print import print_evaluation, print_propositions, print_states

# TODO: eventually replace sentence_letters with something more general
sentence_letters = [A, B, C]

solver = Solver()

solver.add(

    # FRAME CONSTRAINTS:
    ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
    # every part of a possible state is possible
    ForAll([x, y], Exists(z, fusion(x, y) == z)),
    # states are closed under fusion

    # NOTE: the current output suggests that that w is not an A-alternative to
    # itself even though A is true in w
    # TODO: declared alternative with definition and recheck

    # MODEL CONSTRAINT

    # every X of AtomSort is a proposition
    ForAll(X, proposition(X)),

    # there is a world w
    is_world(w),
    # NOTE: couldn't get these two constraints to add without crashing
    # ForAll(x, Implies(is_part_of(x, w), Not(verify(x, A)))),
    # is_part_of(h, w),
    # falsify(h, A),
    # is_part_of(i, w),
    # falsify(i, C),

    # A \boxright C
    ForAll(
        [s, v],
        Implies(
            And(verify(s, A), is_alternative(v, s, w)),
            Exists(t, And(
                is_part_of(t, v),
                verify(t, C),
            )),
        ),
    ),

    # # \neg(A \boxright \neg B)
    # verify(a, A),
    # is_alternative(u, a, w),
    # is_part_of(b, u),
    # verify(b, B),
    # # verify(a,A),
    # # verify(b,B),
    # # compatible(a,b),

    # \neg(A \wedge B \boxright C)
    c == fusion(d, e),
    verify(d, A),
    verify(e, B),
    is_alternative(v, c, w),
    is_part_of(f, v),
    falsify(f, C),
)


if solver.check() == sat:
    print("\nThere is a model of:")
    print("A => C")
    print("~(A => ~B)")
    print("~(A & B => C)")
    model = solver.model()
    print_states(model)
    print_evaluation(model, sentence_letters)
    print_propositions(model, sentence_letters)
else:
    print("\nThere are no models of:\n")
    print("A => C")
    print("~(A => ~B)")
    print("~(A & B => C)\n")
