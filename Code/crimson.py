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
    non_null_verify,
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

    # EVAL CONSTRAINTS
    is_world(w),
    # there is a world w
    is_part_of(a, w),
    non_null_verify(a, A),
    # A is true in w
    is_part_of(b, w),
    non_null_verify(b, B),
    # B is true in w

    # non_null_verify(c, A),
    # is_alternative(u, c, w),
    # is_part_of(s, u),
    # falsify(s, B),
    # # ~(A => B) is true in w
    #
    # NOTE: although the above is equivalent to the below modulo exhaustivity
    # the latter produces truth-value gaps (see issue on github)


        # NOTE: replacing the CF constraints above with the below produces
        # models with no A-alternatives to w despite what the constraint would
        # seem to require. However, adding the constraint 'falsify(z, B)'
        # populates A-alternatives. I'm not sure why this is.

    # Exists(
    #     [a, v],
    #     And(verify(a, A), is_alternative(v, a, w),
    #         ForAll(b, Or(
    #             Not(is_part_of(b, v)),
    #             Not(verify(b, B))
    #             ),
    #         ),
    #     )
    # ),

    # Exists(
    #     [a, v],
    #     And(verify(a, A), is_alternative(v, a, w),
    #         Exists(b, Implies(
    #             is_part_of(b, v),
    #             falsify(b, B)
    #         )),
    #     )
    # ),

    Not(  # in w, it is not the case that if A were true then B would be true
        ForAll(
            [a, v],
            Implies(
                And(verify(a, A), is_alternative(v, a, w)),
                Exists(b, And(is_part_of(b, v), verify(b, B))),
            ),
        ),
    ),

)

# print(type(bit_fusion(BitVecVal(5,5),BitVecVal(2,5))))
# print(bit_fusion(BitVecVal(5,5),BitVecVal(2,5)).sort())


if solver.check() == sat:
    model = solver.model()
    print("\nThere is a model of:")
    print("A, B, ~(A => B)")
    print_states(model)
    print_evaluation(model, sentence_letters)
    print_propositions(model, sentence_letters)
else:
    print("\nThere are no models of:")
    print("A, B, A => B\n")
