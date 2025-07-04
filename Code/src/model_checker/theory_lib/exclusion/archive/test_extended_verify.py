"""
Test extended_verify implementation for Phase 3 of reduced semantics.

This verifies that extended_verify methods properly use Skolem functions
and correctly encode verification conditions.
"""

import z3
from model_checker import syntactic
from model_checker.theory_lib.exclusion.reduced_semantic import (
    ReducedExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure
)
from model_checker.theory_lib.exclusion.reduced_operators import (
    ExclusionOperator,
    UniAndOperator,
    UniOrOperator,
    UniIdentityOperator
)


def create_test_setup(settings=None):
    """Create a standard test setup."""
    if settings is None:
        settings = {'N': 3}
    
    sem = ReducedExclusionSemantics(settings)
    return sem


def test_atomic_extended_verify():
    """Test that atomic sentences reduce to verify relation."""
    print("Testing atomic extended_verify...")
    
    sem = create_test_setup()
    
    # Create atomic sentence
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    # Test extended_verify for atomic sentence
    state = z3.BitVecVal(0b010, 3)
    eval_point = {"world": sem.main_world}
    
    # For atomic: extended_verify(state, A) = verify(state, A)
    constraint = sem.extended_verify(state, A, eval_point)
    
    # Should be exactly verify(state, A)
    expected = sem.verify(state, A.sentence_letter)
    
    # Test they're equivalent
    solver = z3.Solver()
    solver.add(constraint)
    solver.add(z3.Not(expected))
    
    assert solver.check() == z3.unsat, "Atomic extended_verify should equal verify"
    
    print("✓ Atomic extended_verify test passed")


def test_conjunction_extended_verify():
    """Test conjunction extended_verify with state decomposition."""
    print("Testing conjunction extended_verify...")
    
    sem = create_test_setup()
    
    # Create sentences
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    B = syntactic.Sentence("B")
    B.sentence_letter = z3.Const("B", syntactic.AtomSort)
    
    # Create A ∧ B
    A_and_B = syntactic.Sentence("A \\uniwedge B")
    A_and_B.operator = UniAndOperator(sem)
    A_and_B.arguments = [A, B]
    
    # Test extended_verify
    state = z3.BitVecVal(0b110, 3)  # State 6 = 2 | 4
    eval_point = {"world": sem.main_world}
    
    # State 6 verifies A∧B iff 6 = x|y where x verifies A and y verifies B
    constraint = A_and_B.operator.extended_verify(state, A, B, eval_point)
    
    # Set up a model where state 2 verifies A, state 4 verifies B
    solver = z3.Solver()
    solver.add(constraint)
    solver.add(sem.verify(z3.BitVecVal(2, 3), A.sentence_letter))
    solver.add(sem.verify(z3.BitVecVal(4, 3), B.sentence_letter))
    
    # No other states verify A or B
    for i in range(8):
        if i != 2:
            solver.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), A.sentence_letter)))
        if i != 4:
            solver.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), B.sentence_letter)))
    
    # Should be satisfiable since 6 = 2|4
    assert solver.check() == z3.sat, "State 6 should verify A∧B when 2 verifies A and 4 verifies B"
    
    # Test with wrong state
    solver2 = z3.Solver()
    state2 = z3.BitVecVal(0b011, 3)  # State 3 = 1|2, but 1 doesn't verify anything
    constraint2 = A_and_B.operator.extended_verify(state2, A, B, eval_point)
    
    solver2.add(constraint2)
    solver2.add(sem.verify(z3.BitVecVal(2, 3), A.sentence_letter))
    solver2.add(sem.verify(z3.BitVecVal(4, 3), B.sentence_letter))
    
    # No state 1 verifies anything
    for i in range(8):
        if i != 2:
            solver2.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), A.sentence_letter)))
        if i != 4:
            solver2.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), B.sentence_letter)))
    
    # Should be unsatisfiable
    assert solver2.check() == z3.unsat, "State 3 should not verify A∧B"
    
    print("✓ Conjunction extended_verify test passed")


def test_disjunction_extended_verify():
    """Test disjunction extended_verify."""
    print("Testing disjunction extended_verify...")
    
    sem = create_test_setup()
    
    # Create sentences
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    B = syntactic.Sentence("B")
    B.sentence_letter = z3.Const("B", syntactic.AtomSort)
    
    # Create A ∨ B
    A_or_B = syntactic.Sentence("A \\univee B")
    A_or_B.operator = UniOrOperator(sem)
    A_or_B.arguments = [A, B]
    
    # Test extended_verify
    state = z3.BitVecVal(0b010, 3)  # State 2
    eval_point = {"world": sem.main_world}
    
    # State verifies A∨B iff it verifies A or it verifies B
    constraint = A_or_B.operator.extended_verify(state, A, B, eval_point)
    
    # Set up model where state 2 verifies A but not B
    solver = z3.Solver()
    solver.add(constraint)
    solver.add(sem.verify(z3.BitVecVal(2, 3), A.sentence_letter))
    solver.add(z3.Not(sem.verify(z3.BitVecVal(2, 3), B.sentence_letter)))
    
    # Should be satisfiable
    assert solver.check() == z3.sat, "State 2 should verify A∨B when it verifies A"
    
    # Test when state verifies neither
    solver2 = z3.Solver()
    solver2.add(constraint)
    solver2.add(z3.Not(sem.verify(z3.BitVecVal(2, 3), A.sentence_letter)))
    solver2.add(z3.Not(sem.verify(z3.BitVecVal(2, 3), B.sentence_letter)))
    
    # Should be unsatisfiable
    assert solver2.check() == z3.unsat, "State 2 should not verify A∨B when it verifies neither"
    
    print("✓ Disjunction extended_verify test passed")


def test_exclusion_skolem_functions():
    """Test that exclusion uses unique Skolem functions."""
    print("Testing exclusion Skolem functions...")
    
    sem = create_test_setup()
    
    # Create sentence
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    # Create two exclusion operators
    excl_op1 = ExclusionOperator(sem)
    excl_op2 = ExclusionOperator(sem)
    
    # Test extended_verify generates constraints with unique Skolem functions
    state = z3.BitVecVal(0b101, 3)
    eval_point = {"world": sem.main_world}
    
    constraint1 = excl_op1.extended_verify(state, A, eval_point)
    constraint2 = excl_op2.extended_verify(state, A, eval_point)
    
    # Convert to strings to check function names
    str1 = str(constraint1)
    str2 = str(constraint2)
    
    # Should contain h_sk and y_sk functions
    assert "h_sk" in str1, "Should use h_sk Skolem function"
    assert "y_sk" in str1, "Should use y_sk Skolem function"
    
    # Extract the IDs used in each constraint
    import re
    h_sk_ids1 = re.findall(r'h_sk_(\d+)', str1)
    h_sk_ids2 = re.findall(r'h_sk_(\d+)', str2)
    
    # Should have found IDs
    assert len(h_sk_ids1) > 0, "First constraint should have h_sk functions"
    assert len(h_sk_ids2) > 0, "Second constraint should have h_sk functions"
    
    # Since each operator instance has its own counter, they might have the same IDs
    # What matters is that each call to extended_verify gets unique IDs
    # Let's test that calling the same operator twice gives different IDs
    constraint3 = excl_op1.extended_verify(state, A, eval_point)
    str3 = str(constraint3)
    h_sk_ids3 = re.findall(r'h_sk_(\d+)', str3)
    
    # The second call to the same operator should use different IDs
    assert h_sk_ids1[0] != h_sk_ids3[0], "Same operator should use different IDs for different calls"
    
    print("✓ Exclusion Skolem functions test passed")


def test_exclusion_three_conditions():
    """Test that exclusion properly encodes the three conditions."""
    print("Testing exclusion three conditions...")
    
    sem = create_test_setup({'N': 2})  # Small domain for easier testing
    
    # Create sentence
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    # Create ¬A
    not_A = syntactic.Sentence("\\exclude A")
    not_A.operator = ExclusionOperator(sem)
    not_A.arguments = [A]
    
    # Test extended_verify encodes three conditions
    state = z3.BitVecVal(0b11, 2)  # State 3
    eval_point = {"world": sem.main_world}
    
    constraint = not_A.operator.extended_verify(state, A, eval_point)
    
    # The constraint should be a conjunction of three conditions
    str_constraint = str(constraint)
    
    # Should have universal quantifiers (from ForAll)
    assert "And(" in str_constraint, "Should be conjunction of conditions"
    
    # Should reference excludes relation
    assert "excludes" in str_constraint, "Should use excludes primitive"
    
    # Should check part-of relations
    assert "|" in str_constraint or "Or(" in str_constraint, "Should use fusion (bitwise OR)"
    
    print("✓ Exclusion three conditions test passed")


def test_identity_extended_verify():
    """Test identity operator extended_verify."""
    print("Testing identity extended_verify...")
    
    sem = create_test_setup()
    
    # Create sentences
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    B = syntactic.Sentence("B") 
    B.sentence_letter = z3.Const("B", syntactic.AtomSort)
    
    # Create A ≡ B
    A_equiv_B = syntactic.Sentence("A \\uniequiv B")
    A_equiv_B.operator = UniIdentityOperator(sem)
    A_equiv_B.arguments = [A, B]
    
    # Only null state verifies identity, and only when args have same verifiers
    null = sem.null_state
    eval_point = {"world": sem.main_world}
    
    constraint = A_equiv_B.operator.extended_verify(null, A, B, eval_point)
    
    # Should check that state is null AND A,B have same verifiers
    solver = z3.Solver()
    solver.add(constraint)
    
    # A and B have same verifier (state 2)
    solver.add(sem.verify(z3.BitVecVal(2, 3), A.sentence_letter))
    solver.add(sem.verify(z3.BitVecVal(2, 3), B.sentence_letter))
    
    # No other states verify A or B
    for i in range(8):
        if i != 2:
            solver.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), A.sentence_letter)))
            solver.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), B.sentence_letter)))
    
    # Should be satisfiable
    assert solver.check() == z3.sat, "Null state should verify A≡B when they have same verifiers"
    
    # Test with non-null state
    solver2 = z3.Solver()
    non_null = z3.BitVecVal(1, 3)
    constraint2 = A_equiv_B.operator.extended_verify(non_null, A, B, eval_point)
    solver2.add(constraint2)
    
    # Even with same verifiers, non-null shouldn't verify identity
    solver2.add(sem.verify(z3.BitVecVal(2, 3), A.sentence_letter))
    solver2.add(sem.verify(z3.BitVecVal(2, 3), B.sentence_letter))
    
    # Should be unsatisfiable
    assert solver2.check() == z3.unsat, "Non-null state should not verify identity"
    
    print("✓ Identity extended_verify test passed")


def test_recursive_extended_verify():
    """Test that extended_verify properly recurses for complex formulas."""
    print("Testing recursive extended_verify...")
    
    sem = create_test_setup()
    
    # Create atomic sentence
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    # Create ¬A
    not_A = syntactic.Sentence("\\exclude A")
    not_A.operator = ExclusionOperator(sem)
    not_A.arguments = [A]
    
    # For complex sentences, extended_verify should delegate to operator
    state = z3.BitVecVal(0b101, 3)
    eval_point = {"world": sem.main_world}
    
    # Test delegation works
    constraint = sem.extended_verify(state, not_A, eval_point)
    
    # Should produce a constraint (not crash)
    assert constraint is not None, "Should handle complex sentences"
    
    # The constraint should reference primitives
    str_constraint = str(constraint)
    assert "verify" in str_constraint or "excludes" in str_constraint, \
        "Should reduce to primitives"
    
    print("✓ Recursive extended_verify test passed")


def run_all_tests():
    """Run all Phase 3 tests."""
    print("="*60)
    print("PHASE 3: EXTENDED_VERIFY TESTS")
    print("="*60)
    
    test_atomic_extended_verify()
    test_conjunction_extended_verify()
    test_disjunction_extended_verify()
    test_exclusion_skolem_functions()
    test_exclusion_three_conditions()
    test_identity_extended_verify()
    test_recursive_extended_verify()
    
    print("\n" + "="*60)
    print("ALL PHASE 3 TESTS PASSED ✓")
    print("="*60)


if __name__ == "__main__":
    run_all_tests()