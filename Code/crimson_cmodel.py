# AIM: provide a concrete model that can be used to abstract from to build model generator functions
from z3 import (
    # Solver,
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
    X,
    fusion,
    is_part_of,
    world,
    is_world,
    possible,
    verify,
    falsify,
    is_alternative,
    compatible_part,
    alternative,
    proposition,
    maximal,
    Equivalent,
    parthood,
)

from print import print_model

sentence_letters = [A, B]

solver = Solver()

solver.add(
    # FRAME CONSTRAINTS:
    ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
    # every part of a possible state is possible
    ForAll([x, y], Exists(z, fusion(x, y) == z)),
    # states are closed under fusion
    ForAll([x, y], Equivalent(parthood(x, y),is_part_of(x,y))),
    # states are closed under fusion
    ForAll(w, Equivalent(
        world(w),
        # is_world(w),  # NOTE: ditto to NOTE for is_alternative below
        And(possible(w), maximal(w))
    )),
    ForAll(
        [u, y],
        Equivalent(  # TODO: replace with Z3 equiv if any?
            alternative(u, y, w),
            # is_alternative(u, y, w),
            # NOTE: making constraints on alternative() explicit here could
            # make things easier to tweak and keep track of rather than having
            # two similar sounding terms, one defined and one primitive
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
    is_part_of(s, w),  # s is a part of w
    verify(s, A),  # s verifies A
    is_part_of(t, w),  # t is part of w
    verify(t, B),  # t verifies B

    # CF constraints: it is not true that, if A were the case, B would be the case
    verify(y, A),
    is_alternative(u, y, w),
    Exists(b, And(is_part_of(b, u), falsify(b, B))),

    # NOTE: although the above is equivalent to the below modulo exhaustivity
    # the latter produces truth-value gaps (see issue on github)

    # ForAll(b, Implies(is_part_of(b, u), Not(verify(b, B)))),

        # NOTE: replacing the CF constraints above with the below produces
        # models with no A-alternatives to w despite what the constraint would
        # seem to require. However, adding the constraint 'falsify(z, B)'
        # populates A-alternatives. I'm not sure why this is.

    # Not(  # in w, it is not the case that if A were true then B would be true
    #     ForAll(
    #         [a, v],
    #         Implies(
    #             And(verify(a, A), is_alternative(v, a, w)),
    #             Exists(b, And(is_part_of(b, v), verify(b, B))),
    #         ),
    #     ),
    # ),

)

if solver.check() == sat:
    model = solver.model()
    print_model(model, sentence_letters)
else:
    print("\nThere are no models.\n")