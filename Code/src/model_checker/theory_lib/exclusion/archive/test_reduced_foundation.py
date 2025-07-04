"""
Test the foundation of reduced semantics implementation.

This tests Phase 1: ensuring basic semantic primitives work correctly.
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


def test_semantic_primitives():
    """Test that only two Z3 primitives are declared."""
    print("Testing semantic primitives...")
    
    settings = {'N': 3}
    sem = ReducedExclusionSemantics(settings)
    
    # Check that verify and excludes are Z3 functions
    assert isinstance(sem.verify, z3.FuncDeclRef), "verify should be a Z3 function"
    assert isinstance(sem.excludes, z3.FuncDeclRef), "excludes should be a Z3 function"
    
    # Check that fusion and is_part_of work correctly
    x = z3.BitVec('x', 3)
    y = z3.BitVec('y', 3)
    
    # Test fusion
    fusion_result = sem.fusion(z3.BitVecVal(0b010, 3), z3.BitVecVal(0b101, 3))
    assert z3.simplify(fusion_result) == z3.BitVecVal(0b111, 3), "fusion should be bitwise OR"
    
    # Test is_part_of
    # 010 is part of 111
    part_constraint = sem.is_part_of(z3.BitVecVal(0b010, 3), z3.BitVecVal(0b111, 3))
    solver = z3.Solver()
    solver.add(part_constraint)
    assert solver.check() == z3.sat, "010 should be part of 111"
    
    # 101 is not part of 010
    not_part_constraint = sem.is_part_of(z3.BitVecVal(0b101, 3), z3.BitVecVal(0b010, 3))
    solver = z3.Solver()
    solver.add(not_part_constraint)
    assert solver.check() == z3.unsat, "101 should not be part of 010"
    
    print("✓ Semantic primitives test passed")


def test_operator_structure():
    """Test that operators are properly structured."""
    print("Testing operator structure...")
    
    settings = {'N': 3}
    sem = ReducedExclusionSemantics(settings)
    
    # Create operator instances
    excl_op = ExclusionOperator(sem)
    and_op = UniAndOperator(sem)
    or_op = UniOrOperator(sem)
    id_op = UniIdentityOperator(sem)
    
    # Check operator attributes
    assert excl_op.name == "\\exclude", "Exclusion operator name"
    assert excl_op.arity == 1, "Exclusion operator arity"
    
    assert and_op.name == "\\uniwedge", "Conjunction operator name"
    assert and_op.arity == 2, "Conjunction operator arity"
    
    assert or_op.name == "\\univee", "Disjunction operator name"
    assert or_op.arity == 2, "Disjunction operator arity"
    
    assert id_op.name == "\\uniequiv", "Identity operator name"
    assert id_op.arity == 2, "Identity operator arity"
    
    print("✓ Operator structure test passed")


def test_atomic_formula_reduction():
    """Test that atomic formulas reduce to verifier existence."""
    print("Testing atomic formula reduction...")
    
    settings = {'N': 3}
    sem = ReducedExclusionSemantics(settings)
    
    # Create an atomic sentence properly
    A = syntactic.Sentence("A")
    # For atomic sentences, we need to set sentence_letter
    A.sentence_letter = z3.Const(A.name, syntactic.AtomSort)
    
    # Test true_at for atomic sentence
    eval_point = {"world": z3.BitVecVal(0b111, 3)}
    constraint = sem.true_at(A, eval_point)
    
    # The constraint should be an existential quantification
    # It should expand to a disjunction over all possible states
    solver = z3.Solver()
    solver.add(constraint)
    
    # Add a constraint that state 0b010 verifies A
    solver.add(sem.verify(z3.BitVecVal(0b010, 3), A.sentence_letter))
    
    # This should be satisfiable
    assert solver.check() == z3.sat, "Should find a model where A is true"
    
    # Test extended_verify for atomic sentence
    state = z3.BitVecVal(0b010, 3)
    verify_constraint = sem.extended_verify(state, A, eval_point)
    
    # This should directly return verify(state, A)
    expected = sem.verify(state, A.sentence_letter)
    # Can't directly compare Z3 expressions, so test behavior
    solver2 = z3.Solver()
    solver2.add(verify_constraint)
    solver2.add(z3.Not(expected))
    assert solver2.check() == z3.unsat, "extended_verify should reduce to verify for atomic"
    
    print("✓ Atomic formula reduction test passed")


def test_no_operator_specific_logic():
    """Test that semantic functions don't contain operator-specific logic."""
    print("Testing modularity...")
    
    settings = {'N': 3}
    sem = ReducedExclusionSemantics(settings)
    
    # Create mock sentence objects to test delegation
    class MockSentence:
        def __init__(self, is_atomic=False, has_operator=False):
            self.sentence_letter = z3.Const("A", syntactic.AtomSort) if is_atomic else None
            self.operator = MockOperator(sem) if has_operator else None
            self.arguments = []
    
    class MockOperator:
        def __init__(self, semantics):
            self.semantics = semantics
            self.called_true_at = False
            self.called_extended_verify = False
            
        def true_at(self, *args):
            self.called_true_at = True
            return z3.BoolVal(True)
            
        def extended_verify(self, state, *args):
            self.called_extended_verify = True
            return z3.BoolVal(True)
    
    # Test atomic sentence - should not delegate
    atomic_sent = MockSentence(is_atomic=True, has_operator=False)
    eval_point = {"world": z3.BitVecVal(0b111, 3)}
    
    result = sem.true_at(atomic_sent, eval_point)
    assert result is not None, "Atomic sentence should produce constraint"
    
    # Test complex sentence - should delegate to operator
    complex_sent = MockSentence(is_atomic=False, has_operator=True)
    
    result = sem.true_at(complex_sent, eval_point)
    assert complex_sent.operator.called_true_at, "Should delegate to operator.true_at"
    
    # Test extended_verify delegation
    state = z3.BitVecVal(0b010, 3)
    
    # Atomic case
    result = sem.extended_verify(state, atomic_sent, eval_point)
    assert result is not None, "Atomic extended_verify should work"
    
    # Complex case
    complex_sent2 = MockSentence(is_atomic=False, has_operator=True)
    result = sem.extended_verify(state, complex_sent2, eval_point)
    assert complex_sent2.operator.called_extended_verify, "Should delegate to operator.extended_verify"
    
    print("✓ Modularity test passed")


def run_all_tests():
    """Run all Phase 1 tests."""
    print("="*60)
    print("PHASE 1: FOUNDATION TESTS")
    print("="*60)
    
    test_semantic_primitives()
    test_operator_structure()
    test_atomic_formula_reduction()
    test_no_operator_specific_logic()
    
    print("\n" + "="*60)
    print("ALL PHASE 1 TESTS PASSED ✓")
    print("="*60)


if __name__ == "__main__":
    run_all_tests()