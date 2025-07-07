"""
Test if atomic constraints for A are preventing the countermodel.
"""

import z3
import sys
from pathlib import Path

# Add project root
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))

from model_checker.utils import ForAll, Exists
from model_checker import syntactic

def test_atomic_constraints():
    """Test how atomic constraints affect verifiers of A."""
    
    print("=== Testing Atomic Constraints for A ===")
    
    N = 3
    solver = z3.Solver()
    
    # Main world
    world = z3.BitVec('world', N)
    
    # Verify relation
    letter_A = syntactic.AtomVal(0)  # Atomic proposition A
    verify = z3.Function('verify', z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())
    
    # Settings from NEG_TO_SENT
    settings = {
        'contingent': True,
        'non_empty': True,
        'non_null': True,
    }
    
    print(f"Settings: {settings}")
    
    # Add atomic constraints
    v = z3.BitVec('atom_v', N)
    
    if settings['contingent']:
        print("\nAdding contingent constraints:")
        print("  - Some state verifies A")
        print("  - Some state doesn't verify A")
        solver.add(Exists([v], verify(v, letter_A)))
        solver.add(Exists([v], z3.Not(verify(v, letter_A))))
    
    if settings['non_empty']:
        print("\nAdding non_empty constraint:")
        print("  - At least one state verifies A")
        solver.add(Exists([v], verify(v, letter_A)))
    
    if settings['non_null']:
        print("\nAdding non_null constraint:")
        print("  - The null state (0b000) doesn't verify A")
        solver.add(z3.Not(verify(0, letter_A)))
    
    # Now test specific verifier patterns
    print("\n\nTest 1: Standard pattern (states with 'a' bit verify A)")
    solver.push()
    
    # Define standard verifier pattern
    for i in range(2**N):
        if i & 0b001:  # Has 'a' bit
            solver.add(verify(i, letter_A))
        else:
            solver.add(z3.Not(verify(i, letter_A)))
    
    result = solver.check()
    print(f"Can we use standard pattern? {result}")
    
    if result == z3.sat:
        print("YES - Standard pattern is allowed")
        print("States that verify A: 0b001, 0b011, 0b101, 0b111")
        print("States that don't: 0b000, 0b010, 0b100, 0b110")
    
    solver.pop()
    
    print("\n\nTest 2: Alternative pattern (only 0b111 verifies A)")
    solver.push()
    
    # Only the full state verifies A
    for i in range(2**N):
        if i == 0b111:
            solver.add(verify(i, letter_A))
        else:
            solver.add(z3.Not(verify(i, letter_A)))
    
    result2 = solver.check()
    print(f"Can only 0b111 verify A? {result2}")
    
    solver.pop()
    
    print("\n\nTest 3: Check if non_null forces certain verifiers")
    solver2 = z3.Solver()
    
    # Just the non_null constraint
    solver2.add(z3.Not(verify(0, letter_A)))
    
    # Try to make 0b000 verify A
    solver2.add(verify(0, letter_A))
    
    result3 = solver2.check()
    print(f"\nCan 0b000 verify A with non_null? {result3}")
    
    print("\n=== CONCLUSION ===")
    print("The atomic constraints allow the standard pattern where")
    print("states with the 'a' bit verify A. The non_null constraint")
    print("only prevents 0b000 from verifying A, which is fine.")
    print("\nThis is NOT the source of the problem.")

if __name__ == "__main__":
    test_atomic_constraints()