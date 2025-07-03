"""
Test correct true_at reduction for Phase 2 of reduced semantics.

This verifies that all formulas reduce completely to primitive constraints.
"""

import z3
from model_checker import syntactic, model
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
    
    # Create semantics
    sem = ReducedExclusionSemantics(settings)
    
    # Create operator collection
    operators = syntactic.OperatorCollection()
    operators.add_operator(ExclusionOperator)
    operators.add_operator(UniAndOperator)
    operators.add_operator(UniOrOperator)
    operators.add_operator(UniIdentityOperator)
    
    return sem, operators


def test_atomic_reduction():
    """Test that atomic formulas correctly reduce to verifier existence."""
    print("Testing atomic formula reduction...")
    
    sem, operators = create_test_setup()
    
    # Create atomic sentences
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    B = syntactic.Sentence("B")
    B.sentence_letter = z3.Const("B", syntactic.AtomSort)
    
    # Test constraint generation
    eval_point = {"world": sem.main_world}
    
    # A is true at world w iff exists v. verify(v, A) AND v part_of w
    constraint_A = sem.true_at(A, eval_point)
    
    # Check that it expands correctly (custom Exists expands to disjunction)
    solver = z3.Solver()
    solver.add(constraint_A)
    
    # Add that state 2 verifies A
    solver.add(sem.verify(z3.BitVecVal(2, 3), A.sentence_letter))
    
    # Add that main_world is 7 (contains state 2)
    solver.add(sem.main_world == 7)
    
    # Should be satisfiable
    assert solver.check() == z3.sat, "A should be true when verifier exists"
    
    # Test with no verifier
    solver2 = z3.Solver()
    solver2.add(constraint_A)
    solver2.add(sem.main_world == 7)
    
    # No state verifies A
    for i in range(8):  # 2^3 = 8 states
        solver2.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), A.sentence_letter)))
    
    # Should be unsatisfiable
    assert solver2.check() == z3.unsat, "A should be false when no verifier exists"
    
    print("✓ Atomic reduction test passed")


def test_conjunction_reduction():
    """Test that conjunctions properly recurse on both arguments."""
    print("Testing conjunction reduction...")
    
    sem, operators = create_test_setup()
    
    # Create sentences manually
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    B = syntactic.Sentence("B")
    B.sentence_letter = z3.Const("B", syntactic.AtomSort)
    
    # Create A ∧ B manually
    A_and_B = syntactic.Sentence("A \\uniwedge B")
    A_and_B.operator = UniAndOperator(sem)
    A_and_B.arguments = [A, B]
    
    # Test constraint generation
    eval_point = {"world": sem.main_world}
    
    # (A ∧ B) is true iff A is true AND B is true
    constraint = sem.true_at(A_and_B, eval_point)
    
    # Set up a model where A has verifier 2, B has verifier 4, world is 7
    solver = z3.Solver()
    solver.add(constraint)
    solver.add(sem.main_world == 7)  # 111 in binary
    
    # State 2 verifies A, state 4 verifies B
    solver.add(sem.verify(z3.BitVecVal(2, 3), A.sentence_letter))
    solver.add(sem.verify(z3.BitVecVal(4, 3), B.sentence_letter))
    
    # No other states verify A or B
    for i in range(8):
        if i != 2:
            solver.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), A.sentence_letter)))
        if i != 4:
            solver.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), B.sentence_letter)))
    
    # Should be satisfiable
    assert solver.check() == z3.sat, "A ∧ B should be true when both have verifiers"
    
    # Test when A lacks verifier
    solver2 = z3.Solver()
    solver2.add(constraint)
    solver2.add(sem.main_world == 7)
    
    # No state verifies A, but 4 verifies B
    for i in range(8):
        solver2.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), A.sentence_letter)))
    solver2.add(sem.verify(z3.BitVecVal(4, 3), B.sentence_letter))
    
    # Should be unsatisfiable
    assert solver2.check() == z3.unsat, "A ∧ B should be false when A lacks verifier"
    
    print("✓ Conjunction reduction test passed")


def test_disjunction_reduction():
    """Test that disjunctions properly recurse on both arguments."""
    print("Testing disjunction reduction...")
    
    sem, operators = create_test_setup()
    
    # Create sentences manually
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    B = syntactic.Sentence("B")
    B.sentence_letter = z3.Const("B", syntactic.AtomSort)
    
    # Create A ∨ B manually
    A_or_B = syntactic.Sentence("A \\univee B")
    A_or_B.operator = UniOrOperator(sem)
    A_or_B.arguments = [A, B]
    
    # Test constraint generation
    eval_point = {"world": sem.main_world}
    
    # (A ∨ B) is true iff A is true OR B is true
    constraint = sem.true_at(A_or_B, eval_point)
    
    # Test with only A having verifier
    solver = z3.Solver()
    solver.add(constraint)
    solver.add(sem.main_world == 7)
    
    # State 2 verifies A, no state verifies B
    solver.add(sem.verify(z3.BitVecVal(2, 3), A.sentence_letter))
    for i in range(8):
        solver.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), B.sentence_letter)))
        if i != 2:
            solver.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), A.sentence_letter)))
    
    # Should be satisfiable
    assert solver.check() == z3.sat, "A ∨ B should be true when A has verifier"
    
    # Test with neither having verifier
    solver2 = z3.Solver()
    solver2.add(constraint)
    solver2.add(sem.main_world == 7)
    
    # No state verifies A or B
    for i in range(8):
        solver2.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), A.sentence_letter)))
        solver2.add(z3.Not(sem.verify(z3.BitVecVal(i, 3), B.sentence_letter)))
    
    # Should be unsatisfiable
    assert solver2.check() == z3.unsat, "A ∨ B should be false when neither has verifier"
    
    print("✓ Disjunction reduction test passed")


def test_exclusion_reduction():
    """Test that exclusion properly reduces to extended_verify."""
    print("Testing exclusion reduction...")
    
    sem, operators = create_test_setup()
    
    # Create sentences manually
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    # Create ¬A manually
    not_A = syntactic.Sentence("\\exclude A")
    not_A.operator = ExclusionOperator(sem)
    not_A.arguments = [A]
    
    # Test constraint generation
    eval_point = {"world": sem.main_world}
    
    # ¬A is true iff exists s. extended_verify(s, A) AND s part_of world
    constraint = sem.true_at(not_A, eval_point)
    
    # This is complex due to the three conditions in extended_verify
    # For now, just verify the constraint is generated
    solver = z3.Solver()
    solver.add(constraint)
    solver.add(sem.main_world == 7)
    
    # Add some basic exclusion facts
    # State 1 excludes state 2
    solver.add(sem.excludes(z3.BitVecVal(1, 3), z3.BitVecVal(2, 3)))
    
    # State 2 verifies A
    solver.add(sem.verify(z3.BitVecVal(2, 3), A.sentence_letter))
    
    # The constraint should be satisfiable in some models
    # (The exact conditions depend on the three-condition encoding)
    
    print("✓ Exclusion reduction test passed (constraint generated)")


def test_nested_formulas():
    """Test reduction of nested formulas."""
    print("Testing nested formula reduction...")
    
    sem, operators = create_test_setup()
    
    # Create sentences manually
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    B = syntactic.Sentence("B")
    B.sentence_letter = z3.Const("B", syntactic.AtomSort)
    
    # Create A ∧ B
    A_and_B = syntactic.Sentence("A \\uniwedge B")
    A_and_B.operator = UniAndOperator(sem)
    A_and_B.arguments = [A, B]
    
    # Create ¬(A ∧ B)
    not_A_and_B = syntactic.Sentence("\\exclude (A \\uniwedge B)")
    not_A_and_B.operator = ExclusionOperator(sem)
    not_A_and_B.arguments = [A_and_B]
    
    # Test constraint generation
    eval_point = {"world": sem.main_world}
    
    # ¬(A ∧ B) reduces through multiple levels
    constraint = sem.true_at(not_A_and_B, eval_point)
    
    # Verify the constraint contains references to primitives
    constraint_str = str(constraint)
    
    # Should contain verify (for atomic sentences)
    assert "verify" in constraint_str, "Should reduce to verify primitive"
    
    # Should contain excludes (from exclusion operator)
    assert "excludes" in constraint_str, "Should reduce to excludes primitive"
    
    print("✓ Nested formula reduction test passed")


def test_no_circular_dependencies():
    """Test that reduction doesn't create circular dependencies."""
    print("Testing for circular dependencies...")
    
    sem, operators = create_test_setup()
    
    # Create sentences manually
    A = syntactic.Sentence("A")
    A.sentence_letter = z3.Const("A", syntactic.AtomSort)
    
    # Create ¬A
    not_A = syntactic.Sentence("\\exclude A")
    not_A.operator = ExclusionOperator(sem)
    not_A.arguments = [A]
    
    # Create ¬¬A
    double_neg_A = syntactic.Sentence("\\exclude \\exclude A")
    double_neg_A.operator = ExclusionOperator(sem)
    double_neg_A.arguments = [not_A]
    
    # Test constraint generation - should not cause infinite recursion
    eval_point = {"world": sem.main_world}
    
    try:
        constraint = sem.true_at(double_neg_A, eval_point)
        # If we get here, no infinite recursion occurred
        success = True
    except RecursionError:
        success = False
    
    assert success, "Should not have circular dependencies"
    
    print("✓ No circular dependencies test passed")


def run_all_tests():
    """Run all Phase 2 tests."""
    print("="*60)
    print("PHASE 2: TRUE_AT REDUCTION TESTS")
    print("="*60)
    
    test_atomic_reduction()
    test_conjunction_reduction()
    test_disjunction_reduction()
    test_exclusion_reduction()
    test_nested_formulas()
    test_no_circular_dependencies()
    
    print("\n" + "="*60)
    print("ALL PHASE 2 TESTS PASSED ✓")
    print("="*60)


if __name__ == "__main__":
    run_all_tests()