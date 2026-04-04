#!/usr/bin/env python3
"""Investigate nested quantifiers as root cause of native quantifier issues.

Key insight: The is_alternative function in LogosSemantics ITSELF contains
an Exists quantifier:

    def is_alternative(self, state_u, state_y, state_w):
        z = z3.BitVec("alt_z", self.N)
        return z3.And(
            self.is_world(state_u),
            self.is_part_of(state_y, state_u),
            Exists(
                [z],
                z3.And(
                    self.is_part_of(z, state_u),
                    self.max_compatible_part(z, state_w, state_y)
                )
            )
        )

And is_world(state_u) contains maximal(state_u) which has a ForAll:

    def maximal(self, state_w):
        x = z3.BitVec("max_x", self.N)
        return ForAll(
            x,
            z3.Implies(
                self.compatible(x, state_w),
                self.is_part_of(x, state_w),
            ),
        )

So the counterfactual truth condition:
    ForAll([x, u], Implies(verify(x) & is_alternative(u, x, w), consequent(u)))

Actually expands to:
    ForAll([x, u], Implies(
        verify(x) & And(
            is_world(u),  # Contains ForAll (maximal)
            is_part_of(y, u),
            Exists([z], ...)  # Nested existential
        ),
        consequent(u)
    ))

This creates a deeply nested quantifier structure:
    ForAll [x,u] -> ForAll [max_x] (from is_world)
                 -> Exists [z] (from is_alternative)

HYPOTHESIS: The nesting of quantifiers is the root cause.
- Finitary: All quantifiers are expanded to ground terms, no nesting
- Native: Creates nested quantified formulas that Z3 struggles with
"""

import os
import sys

# Ensure local src is prioritized
src_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'src'))
sys.path.insert(0, src_path)

import z3


def test_nested_quantifier_problem():
    """Test that nested quantifiers cause the issue."""

    print("=" * 70)
    print("TESTING NESTED QUANTIFIER HYPOTHESIS")
    print("=" * 70)

    N = 2

    # Uninterpreted functions
    possible = z3.Function("possible", z3.BitVecSort(N), z3.BoolSort())
    part_of = z3.Function("part_of", z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())
    compatible = z3.Function("compatible", z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())
    verify = z3.Function("verify", z3.BitVecSort(N), z3.BoolSort())
    true_at = z3.Function("true_at", z3.BitVecSort(N), z3.BoolSort())

    x = z3.BitVec("x", N)
    u = z3.BitVec("u", N)
    w = z3.BitVec("w", N)
    max_x = z3.BitVec("max_x", N)

    # Define maximal(u) using ForAll
    def maximal(state):
        return z3.ForAll([max_x], z3.Implies(compatible(max_x, state), part_of(max_x, state)))

    # Define is_world(u) = possible(u) & maximal(u)
    def is_world(state):
        return z3.And(possible(state), maximal(state))

    # Simple alternative predicate (without the Exists for now)
    is_alt_simple = z3.Function("is_alt", z3.BitVecSort(N), z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())

    # Base constraints - establish a simple model
    base = z3.And(
        w == z3.BitVecVal(0, N),
        # States 0,1 are possible
        possible(z3.BitVecVal(0, N)),
        possible(z3.BitVecVal(1, N)),
        z3.Not(possible(z3.BitVecVal(2, N))),
        z3.Not(possible(z3.BitVecVal(3, N))),
        # Everything is part of itself
        part_of(z3.BitVecVal(0, N), z3.BitVecVal(0, N)),
        part_of(z3.BitVecVal(1, N), z3.BitVecVal(1, N)),
        part_of(z3.BitVecVal(2, N), z3.BitVecVal(2, N)),
        part_of(z3.BitVecVal(3, N), z3.BitVecVal(3, N)),
        # Compatible with self
        compatible(z3.BitVecVal(0, N), z3.BitVecVal(0, N)),
        compatible(z3.BitVecVal(1, N), z3.BitVecVal(1, N)),
        # Antecedent verified by state 1
        verify(z3.BitVecVal(1, N)),
        z3.Not(verify(z3.BitVecVal(0, N))),
        z3.Not(verify(z3.BitVecVal(2, N))),
        z3.Not(verify(z3.BitVecVal(3, N))),
        # World 1 is alternative via state 1 from world 0
        is_alt_simple(z3.BitVecVal(1, N), z3.BitVecVal(1, N), z3.BitVecVal(0, N)),
    )

    print("\nTest 1: Flat structure (no nested quantifiers)")
    print("-" * 70)

    # Without is_world constraint in the formula
    cf_flat = z3.ForAll([x, u], z3.Implies(
        z3.And(verify(x), is_alt_simple(u, x, w)),
        true_at(u)
    ))

    s1 = z3.Solver()
    s1.add(base)
    s1.add(cf_flat)
    result1 = s1.check()
    print(f"  Flat ForAll (no is_world check): {result1}")
    if result1 == z3.sat:
        m = s1.model()
        print(f"  true_at(1) = {m.evaluate(true_at(z3.BitVecVal(1, N)))}")

    print("\nTest 2: With is_world constraint (contains nested ForAll)")
    print("-" * 70)

    # With is_world in the precondition
    cf_nested = z3.ForAll([x, u], z3.Implies(
        z3.And(verify(x), is_world(u), is_alt_simple(u, x, w)),
        true_at(u)
    ))

    s2 = z3.Solver()
    s2.add(base)
    s2.add(cf_nested)
    result2 = s2.check()
    print(f"  Nested ForAll (with is_world): {result2}")
    if result2 == z3.sat:
        m = s2.model()
        print(f"  true_at(1) = {m.evaluate(true_at(z3.BitVecVal(1, N)))}")

    print("\nTest 3: With is_world expanded (maximal as ForAll)")
    print("-" * 70)

    # Explicit nesting
    cf_explicit_nested = z3.ForAll([x, u], z3.Implies(
        z3.And(
            verify(x),
            possible(u),
            z3.ForAll([max_x], z3.Implies(compatible(max_x, u), part_of(max_x, u))),  # maximal
            is_alt_simple(u, x, w)
        ),
        true_at(u)
    ))

    s3 = z3.Solver()
    s3.add(base)
    s3.add(cf_explicit_nested)
    result3 = s3.check()
    print(f"  Explicit nested ForAll: {result3}")
    if result3 == z3.sat:
        m = s3.model()
        print(f"  true_at(1) = {m.evaluate(true_at(z3.BitVecVal(1, N)))}")

    print("\nTest 4: Finitary expansion (no quantifiers)")
    print("-" * 70)

    # Expand everything to ground formulas
    def maximal_ground(state_val):
        return z3.And([
            z3.Implies(compatible(z3.BitVecVal(i, N), state_val), part_of(z3.BitVecVal(i, N), state_val))
            for i in range(4)
        ])

    cf_ground = z3.And([
        z3.Implies(
            z3.And(
                verify(z3.BitVecVal(i, N)),
                possible(z3.BitVecVal(j, N)),
                maximal_ground(z3.BitVecVal(j, N)),
                is_alt_simple(z3.BitVecVal(j, N), z3.BitVecVal(i, N), w)
            ),
            true_at(z3.BitVecVal(j, N))
        )
        for i in range(4) for j in range(4)
    ])

    s4 = z3.Solver()
    s4.add(base)
    s4.add(cf_ground)
    result4 = s4.check()
    print(f"  Ground formula (no quantifiers): {result4}")
    if result4 == z3.sat:
        m = s4.model()
        print(f"  true_at(1) = {m.evaluate(true_at(z3.BitVecVal(1, N)))}")

    print("\n" + "=" * 70)
    print("ANALYSIS")
    print("=" * 70)

    print(f"""
Results comparison:
  - Flat structure (no nesting):      {result1}
  - With is_world (nested ForAll):    {result2}
  - Explicit nested ForAll:           {result3}
  - Ground formula (no quantifiers):  {result4}

If the nested versions differ from the ground version, we've found the root cause!
""")

    return result1, result2, result3, result4


def test_deep_nesting():
    """Test how depth of nesting affects Z3's behavior."""

    print("\n" + "=" * 70)
    print("TESTING NESTING DEPTH EFFECT")
    print("=" * 70)

    N = 2
    P = z3.Function("P", z3.BitVecSort(N), z3.BoolSort())

    # Variables
    x1 = z3.BitVec("x1", N)
    x2 = z3.BitVec("x2", N)
    x3 = z3.BitVec("x3", N)

    # Constraint: P is true for 0 and 1, false for 2 and 3
    P_constraint = z3.And(
        P(z3.BitVecVal(0, N)),
        P(z3.BitVecVal(1, N)),
        z3.Not(P(z3.BitVecVal(2, N))),
        z3.Not(P(z3.BitVecVal(3, N))),
    )

    print("\nDepth 1: ForAll x1: P(x1)")
    s1 = z3.Solver()
    s1.add(P_constraint)
    s1.add(z3.ForAll([x1], P(x1)))
    print(f"  Result: {s1.check()}")  # Should be UNSAT (P(2) false)

    print("\nDepth 1: ForAll x1: (x1 < 2) => P(x1)")
    s2 = z3.Solver()
    s2.add(P_constraint)
    s2.add(z3.ForAll([x1], z3.Implies(z3.ULT(x1, 2), P(x1))))
    print(f"  Result: {s2.check()}")  # Should be SAT

    print("\nDepth 2: ForAll x1: ForAll x2: (x1 < 2 & x2 < 2) => P(x1)")
    s3 = z3.Solver()
    s3.add(P_constraint)
    s3.add(z3.ForAll([x1], z3.ForAll([x2], z3.Implies(z3.And(z3.ULT(x1, 2), z3.ULT(x2, 2)), P(x1)))))
    print(f"  Result: {s3.check()}")

    print("\nDepth 2 (combined): ForAll [x1, x2]: (x1 < 2 & x2 < 2) => P(x1)")
    s4 = z3.Solver()
    s4.add(P_constraint)
    s4.add(z3.ForAll([x1, x2], z3.Implies(z3.And(z3.ULT(x1, 2), z3.ULT(x2, 2)), P(x1))))
    print(f"  Result: {s4.check()}")


def test_alternating_quantifiers():
    """Test alternating quantifier issues."""

    print("\n" + "=" * 70)
    print("TESTING ALTERNATING QUANTIFIERS (ForAll-Exists)")
    print("=" * 70)

    N = 2
    R = z3.Function("R", z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())
    P = z3.Function("P", z3.BitVecSort(N), z3.BoolSort())

    x = z3.BitVec("x", N)
    y = z3.BitVec("y", N)

    # Setup: R(0,1) and R(1,0) are true, P(0) and P(1) are true
    setup = z3.And(
        R(z3.BitVecVal(0, N), z3.BitVecVal(1, N)),
        R(z3.BitVecVal(1, N), z3.BitVecVal(0, N)),
        P(z3.BitVecVal(0, N)),
        P(z3.BitVecVal(1, N)),
    )

    print("\nFormula: ForAll x: Exists y: R(x,y) => P(y)")
    print("(Should be SAT if for all x, there exists y with R(x,y) => P(y))")

    # Native
    formula_native = z3.ForAll([x], z3.Exists([y], z3.Implies(R(x, y), P(y))))
    s1 = z3.Solver()
    s1.add(setup)
    s1.add(formula_native)
    result1 = s1.check()
    print(f"  Native ForAll-Exists: {result1}")

    # Ground
    formula_ground = z3.And([
        z3.Or([
            z3.Implies(R(z3.BitVecVal(i, N), z3.BitVecVal(j, N)), P(z3.BitVecVal(j, N)))
            for j in range(4)
        ])
        for i in range(4)
    ])
    s2 = z3.Solver()
    s2.add(setup)
    s2.add(formula_ground)
    result2 = s2.check()
    print(f"  Ground expansion: {result2}")


def test_with_mbqi_tactics():
    """Test different MBQI tactics for nested quantifiers."""

    print("\n" + "=" * 70)
    print("TESTING Z3 TACTICS FOR NESTED QUANTIFIERS")
    print("=" * 70)

    N = 2
    possible = z3.Function("possible", z3.BitVecSort(N), z3.BoolSort())
    compatible = z3.Function("compatible", z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())
    part_of = z3.Function("part_of", z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())
    verify = z3.Function("verify", z3.BitVecSort(N), z3.BoolSort())
    true_at = z3.Function("true_at", z3.BitVecSort(N), z3.BoolSort())
    is_alt = z3.Function("is_alt", z3.BitVecSort(N), z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())

    x = z3.BitVec("x", N)
    u = z3.BitVec("u", N)
    w = z3.BitVec("w", N)
    max_x = z3.BitVec("max_x", N)

    base = z3.And(
        w == z3.BitVecVal(0, N),
        possible(z3.BitVecVal(0, N)),
        possible(z3.BitVecVal(1, N)),
        z3.Not(possible(z3.BitVecVal(2, N))),
        z3.Not(possible(z3.BitVecVal(3, N))),
        verify(z3.BitVecVal(1, N)),
        z3.Not(verify(z3.BitVecVal(0, N))),
        z3.Not(verify(z3.BitVecVal(2, N))),
        z3.Not(verify(z3.BitVecVal(3, N))),
        is_alt(z3.BitVecVal(1, N), z3.BitVecVal(1, N), z3.BitVecVal(0, N)),
    )

    cf_nested = z3.ForAll([x, u], z3.Implies(
        z3.And(
            verify(x),
            possible(u),
            z3.ForAll([max_x], z3.Implies(compatible(max_x, u), part_of(max_x, u))),
            is_alt(u, x, w)
        ),
        true_at(u)
    ))

    print("\nNested quantifier formula with different solvers:")

    # Default
    s1 = z3.Solver()
    s1.add(base)
    s1.add(cf_nested)
    result1 = s1.check()
    print(f"  Default solver: {result1}")

    # With MBQI
    s2 = z3.Solver()
    s2.set("smt.mbqi", True)
    s2.add(base)
    s2.add(cf_nested)
    result2 = s2.check()
    print(f"  With MBQI: {result2}")

    # With qi.lazy_threshold
    s3 = z3.Solver()
    s3.set("smt.qi.lazy_threshold", 0)
    s3.add(base)
    s3.add(cf_nested)
    result3 = s3.check()
    print(f"  With qi.lazy_threshold=0: {result3}")

    # Using simplify tactic first
    try:
        goal = z3.Goal()
        goal.add(base)
        goal.add(cf_nested)
        t = z3.Tactic('simplify')
        simplified = t(goal)
        print(f"\n  Simplified goal ({len(simplified)} subgoal(s)):")
        for subgoal in simplified:
            print(f"    {len(subgoal)} assertions")
    except Exception as e:
        print(f"  Simplify tactic error: {e}")


def main():
    # Test nested quantifier hypothesis
    results = test_nested_quantifier_problem()

    # Test nesting depth
    test_deep_nesting()

    # Test alternating quantifiers
    test_alternating_quantifiers()

    # Test MBQI tactics
    test_with_mbqi_tactics()

    print("\n" + "=" * 70)
    print("FINAL CONCLUSION")
    print("=" * 70)
    print("""
ROOT CAUSE ANALYSIS:

The model checker's semantic functions use quantifiers internally:
- is_world(u) calls maximal(u) which contains ForAll
- is_alternative(u,y,w) contains Exists
- max_compatible_part also uses quantifiers

When these are called within operator definitions like CounterfactualOperator:
    ForAll([x,u], Implies(verify(x) & is_alternative(u,x,w), consequent(u)))

The result is NESTED QUANTIFIERS:
    ForAll [x,u] -> ForAll [max_x] -> Exists [z]

This creates a complex quantified formula that:
1. Z3's quantifier instantiation may not fully explore
2. The alternation (ForAll-ForAll-Exists) is computationally hard
3. Finite domain information isn't being leveraged effectively

SOLUTION OPTIONS:

1. KEEP FINITARY DEFAULT: The safest option for correctness
   - Finitary expands ALL quantifiers to ground formulas
   - No nested quantifiers, pure bitvector solving
   - Guaranteed to explore all finite domain values

2. ADD QUANTIFIER PATTERNS: If native quantifiers are desired
   - Add :pattern annotations to guide instantiation
   - May help but not guaranteed to work for all cases

3. USE FINITE MODEL FINDING: Alternative approach
   - Configure Z3 to use finite model finding strategies
   - May help with the finite bitvector domain

4. HYBRID APPROACH: Based on problem type
   - Theorems (UNSAT expected): Native quantifiers work fine
   - Countermodels (SAT expected): Use finitary to guarantee model finding

The fundamental issue is that SMT solvers treat quantified formulas as
potentially infinite even when the domain (bitvectors) is finite.
""")


if __name__ == "__main__":
    main()
