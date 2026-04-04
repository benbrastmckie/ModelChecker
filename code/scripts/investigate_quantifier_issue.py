#!/usr/bin/env python3
"""Investigate root cause of native quantifier UNSAT issue.

This script isolates and examines why native z3.ForAll/Exists quantifiers
return UNSAT for satisfiable problems that finitary enumeration solves correctly.

The key hypothesis is that native quantifiers quantify over ALL possible bitvector
values (0..2^N-1), not just the states that satisfy domain constraints like
possible(x) or is_world(x). Without explicit domain restriction in the quantifier
body, the solver may find spurious counterexamples in impossible states.
"""

import os
import sys

# Ensure local src is prioritized
src_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'src'))
sys.path.insert(0, src_path)

import z3


def demonstrate_quantifier_difference():
    """Demonstrate the semantic difference between finitary and native quantifiers."""

    print("=" * 70)
    print("DEMONSTRATION: Native vs Finitary Quantifier Semantics")
    print("=" * 70)

    N = 2  # Small bitvector size for clarity

    # Create a domain predicate - only some bitvector values are "valid"
    domain = z3.Function("domain", z3.BitVecSort(N), z3.BoolSort())

    # Create an uninterpreted function we want to check
    P = z3.Function("P", z3.BitVecSort(N), z3.BoolSort())

    x = z3.BitVec("x", N)

    # Constraint: Only bitvector values 0 and 1 are in the domain
    domain_constraint = z3.And(
        domain(z3.BitVecVal(0, N)),
        domain(z3.BitVecVal(1, N)),
        z3.Not(domain(z3.BitVecVal(2, N))),
        z3.Not(domain(z3.BitVecVal(3, N))),
    )

    # P is true for all values in the domain
    P_in_domain = z3.And(
        P(z3.BitVecVal(0, N)),
        P(z3.BitVecVal(1, N)),
    )

    # P is FALSE for values outside the domain
    P_outside = z3.And(
        z3.Not(P(z3.BitVecVal(2, N))),
        z3.Not(P(z3.BitVecVal(3, N))),
    )

    print("\nSetup:")
    print("  N = 2 (bitvectors 0,1,2,3)")
    print("  domain = {0, 1} (only 0 and 1 are 'valid' states)")
    print("  P(0) = True, P(1) = True (P holds for all domain elements)")
    print("  P(2) = False, P(3) = False (P false outside domain)")
    print()

    # Test 1: Unrestricted native ForAll
    print("-" * 70)
    print("TEST 1: Unrestricted native ForAll(x, P(x))")
    print("-" * 70)
    s1 = z3.Solver()
    s1.add(domain_constraint)
    s1.add(P_in_domain)
    s1.add(P_outside)
    # Native ForAll over ALL bitvectors - expects P(x) for x=0,1,2,3
    s1.add(z3.ForAll([x], P(x)))
    result1 = s1.check()
    print(f"  ForAll(x, P(x)): {result1}")
    print("  Expected: UNSAT (P(2) and P(3) are false)")
    print()

    # Test 2: Domain-restricted native ForAll
    print("-" * 70)
    print("TEST 2: Domain-restricted native ForAll(x, domain(x) => P(x))")
    print("-" * 70)
    s2 = z3.Solver()
    s2.add(domain_constraint)
    s2.add(P_in_domain)
    s2.add(P_outside)
    # Native ForAll with domain restriction
    s2.add(z3.ForAll([x], z3.Implies(domain(x), P(x))))
    result2 = s2.check()
    print(f"  ForAll(x, domain(x) => P(x)): {result2}")
    print("  Expected: SAT (only checks P for domain elements)")
    print()

    # Test 3: Finitary enumeration (explicit)
    print("-" * 70)
    print("TEST 3: Finitary enumeration: And(P(0), P(1)) [domain only]")
    print("-" * 70)
    s3 = z3.Solver()
    s3.add(domain_constraint)
    s3.add(P_in_domain)
    s3.add(P_outside)
    # Finitary: only check domain elements
    s3.add(z3.And(P(z3.BitVecVal(0, N)), P(z3.BitVecVal(1, N))))
    result3 = s3.check()
    print(f"  And(P(0), P(1)): {result3}")
    print("  Expected: SAT (only checks P for domain elements)")
    print()

    # Summary
    print("=" * 70)
    print("ANALYSIS:")
    print("=" * 70)
    print("""
The key difference:

1. Native ForAll(x, P(x)) quantifies over ALL 2^N bitvector values.
   If P is false for ANY value (even outside the intended domain), it's UNSAT.

2. Native ForAll(x, domain(x) => P(x)) restricts to domain elements.
   Values outside the domain vacuously satisfy the implication.

3. Finitary enumeration only generates conjuncts for specific values,
   effectively implementing restricted quantification.

When the model checker uses native quantifiers without domain restriction,
it checks properties over ALL bitvector values, not just the "possible"
or "world" states. This causes formulas that are satisfiable over the
intended domain to appear unsatisfiable.
""")

    return result1, result2, result3


def investigate_model_checker_formulas():
    """Investigate how model checker formulas are structured."""

    print("\n" + "=" * 70)
    print("INVESTIGATION: Model Checker Formula Structure")
    print("=" * 70)

    # Import model checker components
    from model_checker.utils.z3_helpers import (
        set_quantifier_mode, get_quantifier_mode,
        ForAll as mc_ForAll, Exists as mc_Exists,
        _finitary_forall, _native_forall
    )

    N = 2
    x = z3.BitVec("test_x", N)

    # Create a simple formula
    P = z3.Function("P", z3.BitVecSort(N), z3.BoolSort())
    formula = P(x)

    print("\nModel checker ForAll implementations:")
    print()

    # Finitary version
    finitary_result = _finitary_forall([x], formula)
    print(f"Finitary ForAll([x], P(x)):")
    print(f"  {finitary_result}")
    print()

    # Native version
    native_result = _native_forall([x], formula)
    print(f"Native ForAll([x], P(x)):")
    print(f"  {native_result}")
    print()

    print("Observation: Finitary explicitly enumerates P(0) & P(1) & P(2) & P(3)")
    print("            Native uses z3.ForAll which quantifies over 0..2^N-1")


def investigate_counterfactual_formula():
    """Investigate the counterfactual formula structure."""

    print("\n" + "=" * 70)
    print("INVESTIGATION: Counterfactual Conditional Formula")
    print("=" * 70)

    print("""
From code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py:

CounterfactualOperator.true_at():
    return ForAll(
        [x, u],
        z3.Implies(
            z3.And(
                semantics.extended_verify(x, leftarg, eval_point),
                semantics.is_alternative(u, x, eval_point["world"])
            ),
            semantics.true_at(rightarg, semantics.with_world(eval_point, u)),
        ),
    )

This formula says:
  For all states x and worlds u:
    IF (x verifies the antecedent AND u is an alternative world via x)
    THEN the consequent is true at u

The key insight: The formula uses z3.Implies with domain predicates
(extended_verify and is_alternative) as the antecedent.

With FINITARY enumeration:
  - We enumerate ALL 2^N values for x and ALL 2^N values for u
  - For each (x,u) pair, we generate: Implies(preconditions, consequent)
  - Values where preconditions are false contribute trivially true conjuncts
  - This is semantically correct!

With NATIVE ForAll:
  - Z3 quantifies over all bitvector values
  - The Implies structure should work identically
  - BUT: The quantifier instantiation may not find counterexamples
         when they exist in corner cases

THE ROOT CAUSE IS NOT domain restriction - it's quantifier instantiation!
""")


def investigate_sat_vs_unsat():
    """Investigate why SAT cases fail but UNSAT cases work."""

    print("\n" + "=" * 70)
    print("INVESTIGATION: Why SAT Cases Fail with Native Quantifiers")
    print("=" * 70)

    print("""
Observation from benchmark results:
- Theorems (expecting UNSAT): Both finitary and native return UNSAT correctly
- Countermodels (expecting SAT): Finitary returns SAT, native returns UNSAT

For UNSAT cases (theorems):
  - We need to prove: ForAll constraints hold
  - If finitary finds all conjuncts true, the formula is SAT
  - If native ForAll is satisfied, the formula is SAT
  - Both methods agree: the overall problem is UNSAT (no countermodel)

For SAT cases (countermodels):
  - We need to find: A model where premises true and conclusions false
  - Finitary: generates explicit conjuncts, solver finds satisfying assignment
  - Native: ForAll formula must be satisfied by ALL bitvector values

The problem: When we try to find a countermodel, we add constraints like:
  ForAll([x,u], Implies(precondition(x,u), consequent(x,u)))

For finitary: This becomes a large conjunction. If there's an (x,u) where
              precondition is true, consequent must be true. But the
              solver can assign values to make this work.

For native: The solver must find an assignment where the ForAll holds
           for EVERY possible instantiation. The quantifier elimination
           or instantiation strategy may conclude UNSAT prematurely.

HYPOTHESIS: Native quantifiers with bitvector variables use different
           solving strategies than ground bitvector formulas. The quantifier
           solver may not fully explore the finite domain, or may use
           approximations that lead to spurious UNSAT results.
""")


def test_simple_countermodel_case():
    """Test a simplified countermodel scenario."""

    print("\n" + "=" * 70)
    print("TEST: Simplified Countermodel Scenario")
    print("=" * 70)

    N = 2

    # Create predicates
    possible = z3.Function("possible", z3.BitVecSort(N), z3.BoolSort())
    verify_A = z3.Function("verify_A", z3.BitVecSort(N), z3.BoolSort())
    is_alt = z3.Function("is_alt", z3.BitVecSort(N), z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())
    true_B = z3.Function("true_B", z3.BitVecSort(N), z3.BoolSort())

    x = z3.BitVec("x", N)
    u = z3.BitVec("u", N)
    w = z3.BitVec("w", N)  # main world

    # Setup: w=0 is the main world, 0 and 1 are possible worlds
    setup = z3.And(
        w == z3.BitVecVal(0, N),
        possible(z3.BitVecVal(0, N)),
        possible(z3.BitVecVal(1, N)),
        z3.Not(possible(z3.BitVecVal(2, N))),
        z3.Not(possible(z3.BitVecVal(3, N))),
    )

    # A is verified by state 1
    verify_constraint = z3.And(
        verify_A(z3.BitVecVal(1, N)),
        z3.Not(verify_A(z3.BitVecVal(0, N))),
        z3.Not(verify_A(z3.BitVecVal(2, N))),
        z3.Not(verify_A(z3.BitVecVal(3, N))),
    )

    # World 1 is an alternative to world 0 via state 1
    alt_constraint = z3.And(
        is_alt(z3.BitVecVal(1, N), z3.BitVecVal(1, N), z3.BitVecVal(0, N)),
        # No other alternatives
    )

    # Countermodel scenario: B is true at world 0, but FALSE at world 1
    # This means: A boxright B should be FALSE (there's an alternative where B fails)
    B_constraint = z3.And(
        true_B(z3.BitVecVal(0, N)),
        z3.Not(true_B(z3.BitVecVal(1, N))),  # Key: B fails at the alternative!
    )

    # The counterfactual formula: ForAll x,u: (verify_A(x) & is_alt(u,x,w)) => true_B(u)
    # This should be FALSE because verify_A(1) & is_alt(1,1,0) is true, but true_B(1) is false

    cf_formula_native = z3.ForAll([x, u], z3.Implies(
        z3.And(verify_A(x), is_alt(u, x, w)),
        true_B(u)
    ))

    # Finitary version: expand to all 16 (x,u) pairs
    cf_formula_finitary = z3.And([
        z3.Implies(
            z3.And(verify_A(z3.BitVecVal(i, N)), is_alt(z3.BitVecVal(j, N), z3.BitVecVal(i, N), w)),
            true_B(z3.BitVecVal(j, N))
        )
        for i in range(4) for j in range(4)
    ])

    print("\nScenario: Trying to find a countermodel to A boxright B")
    print("  Main world: w = 0")
    print("  A is verified by state 1")
    print("  World 1 is an alternative to world 0 via state 1")
    print("  B is true at world 0, FALSE at world 1")
    print("  Expected: A boxright B is FALSE (countermodel exists)")
    print()

    # Test with finitary
    print("-" * 70)
    print("Finitary approach: And over all (x,u) pairs")
    print("-" * 70)
    s_fin = z3.Solver()
    s_fin.add(setup)
    s_fin.add(verify_constraint)
    s_fin.add(alt_constraint)
    s_fin.add(B_constraint)
    s_fin.add(cf_formula_finitary)  # The counterfactual constraint
    result_fin = s_fin.check()
    print(f"  Result: {result_fin}")
    print("  Expected: SAT if we're checking the TRUTH conditions")
    print("            (we're building a model where A boxright B is true)")
    print()

    # Test: What if we want to show A boxright B is FALSE?
    # We need Exists x,u: verify_A(x) & is_alt(u,x,w) & NOT true_B(u)
    falsity_formula_native = z3.Exists([x, u], z3.And(
        verify_A(x),
        is_alt(u, x, w),
        z3.Not(true_B(u))
    ))

    falsity_formula_finitary = z3.Or([
        z3.And(
            verify_A(z3.BitVecVal(i, N)),
            is_alt(z3.BitVecVal(j, N), z3.BitVecVal(i, N), w),
            z3.Not(true_B(z3.BitVecVal(j, N)))
        )
        for i in range(4) for j in range(4)
    ])

    print("-" * 70)
    print("Testing falsity of A boxright B (should find a witness)")
    print("-" * 70)

    # Finitary falsity
    s_fin_false = z3.Solver()
    s_fin_false.add(setup)
    s_fin_false.add(verify_constraint)
    s_fin_false.add(alt_constraint)
    s_fin_false.add(B_constraint)
    s_fin_false.add(falsity_formula_finitary)
    result_fin_false = s_fin_false.check()
    print(f"  Finitary Exists: {result_fin_false}")

    # Native falsity
    s_nat_false = z3.Solver()
    s_nat_false.add(setup)
    s_nat_false.add(verify_constraint)
    s_nat_false.add(alt_constraint)
    s_nat_false.add(B_constraint)
    s_nat_false.add(falsity_formula_native)
    result_nat_false = s_nat_false.check()
    print(f"  Native Exists: {result_nat_false}")

    if result_fin_false == z3.sat:
        print("\n  Model (finitary):")
        model = s_fin_false.model()
        print(f"    Found witness where A boxright B is false")

    if result_nat_false == z3.sat:
        print("\n  Model (native):")
        model = s_nat_false.model()
        print(f"    Found witness where A boxright B is false")

    print()
    print("=" * 70)
    print("KEY FINDING:")
    print("=" * 70)
    print("""
Both finitary and native should find the falsity witness!
The issue may be more subtle - in the actual model checker:

1. The domain predicates (possible, verify, is_alt) are uninterpreted
   functions that get constrained by other parts of the problem.

2. When native quantifiers are used, Z3's quantifier instantiation
   may not explore all necessary trigger patterns.

3. The finitary approach always grounds all combinations explicitly,
   which guarantees exploration of all relevant cases.

The real investigation needs to look at the actual Z3 formulas
generated by the model checker with print_z3=True.
""")


def main():
    print("=" * 70)
    print("Native Quantifier UNSAT Root Cause Investigation")
    print("=" * 70)

    # Run investigations
    demonstrate_quantifier_difference()
    investigate_model_checker_formulas()
    investigate_counterfactual_formula()
    investigate_sat_vs_unsat()
    test_simple_countermodel_case()

    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)
    print("""
The root cause of native quantifiers returning UNSAT for SAT problems:

1. DOMAIN RESTRICTION HYPOTHESIS (Partially Correct):
   - Native ForAll quantifies over all 2^N bitvector values
   - However, the model checker already uses Implies to restrict domain
   - This is NOT the primary cause

2. QUANTIFIER INSTANTIATION HYPOTHESIS (More Likely):
   - Z3's quantifier handling uses trigger-based instantiation
   - Complex nested structures with uninterpreted functions may not
     generate appropriate triggers
   - The finitary approach avoids this by grounding all combinations

3. FINITE DOMAIN HANDLING (Most Likely Root Cause):
   - Z3 knows bitvectors are finite but may use approximations
   - For SAT queries with quantifiers, Z3 may conclude UNSAT without
     full exploration of the finite domain
   - CVC5 has similar behavior (both return UNSAT incorrectly)

RECOMMENDED SOLUTIONS:

1. Keep finitary as default for small domains (N <= 4)
2. For larger domains, add explicit finite domain hints:
   - Use quantifier patterns/triggers
   - Consider mbqi (model-based quantifier instantiation)
   - Add :qid and :skolemid attributes

3. Test with finite model finding options in Z3/CVC5

4. Consider hybrid: use native for proving UNSAT (theorems),
   finitary for finding SAT (countermodels)
""")


if __name__ == "__main__":
    main()
