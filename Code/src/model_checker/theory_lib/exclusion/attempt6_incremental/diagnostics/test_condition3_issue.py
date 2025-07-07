"""
Test to demonstrate the condition3 issue.
"""

import z3
import sys
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent.parent.parent.parent.parent
sys.path.insert(0, str(project_root))

from model_checker.utils import ForAll, Exists

def test_condition3_issue():
    """Show that condition3 allows world to have extra bits."""
    
    print("=== Testing Condition3 Implementation ===")
    
    N = 3
    world = z3.BitVec('world', N)
    h_sk = z3.Function('h_sk', z3.BitVecSort(N), z3.BitVecSort(N))
    
    # Helper functions
    def is_part_of(x, y):
        return (x | y) == y
    
    def verifies_A(x):
        return (x & 0b001) != 0
    
    solver = z3.Solver()
    
    # Force specific h_sk values: all map to 0b000
    print("Setting all h_sk values to 0b000")
    for v in [0b001, 0b011, 0b101, 0b111]:
        solver.add(h_sk(v) == 0b000)
    
    # Add the actual condition3 from the code
    print("\nAdding condition3 from the actual implementation...")
    
    # Variables for quantification
    x = z3.BitVec('x', N)
    s = z3.BitVec('s', N)
    h_values = z3.BitVec('h_values', N)
    
    # condition3_setup
    condition3_setup = ForAll([h_values],
        z3.Implies(
            Exists([x], z3.And(
                verifies_A(x),
                h_values == h_sk(x)
            )),
            is_part_of(h_values, world)
        )
    )
    
    # condition3_minimal
    condition3_minimal = ForAll([s],
        z3.Implies(
            z3.And(
                ForAll([x], z3.Implies(
                    verifies_A(x),
                    is_part_of(h_sk(x), s)
                )),
                s != world
            ),
            z3.Not(is_part_of(s, world))
        )
    )
    
    solver.add(condition3_setup)
    solver.add(condition3_minimal)
    
    # Test if world can be 0b100 (has extra bits)
    print("\nTest 1: Can world be 0b100 when all h_sk are 0b000?")
    solver.push()
    solver.add(world == 0b100)
    result1 = solver.check()
    print(f"Result: {result1}")
    
    if result1 == z3.sat:
        print("YES! This shows condition3 allows extra bits in world!")
        
        # Verify the fusion would be 0b000
        print("\nThe fusion of all h_sk values would be: 0b000")
        print("But world is allowed to be: 0b100")
        print("This explains why NEG_TO_SENT has no countermodel!")
    solver.pop()
    
    # Test what happens with proper fusion constraint
    print("\n\nTest 2: With proper fusion constraint")
    solver2 = z3.Solver()
    
    # Same h_sk values
    for v in [0b001, 0b011, 0b101, 0b111]:
        solver2.add(h_sk(v) == 0b000)
    
    # Proper fusion constraint
    fusion = h_sk(0b001) | h_sk(0b011) | h_sk(0b101) | h_sk(0b111)
    solver2.add(world == fusion)
    
    solver2.add(world == 0b100)
    result2 = solver2.check()
    print(f"Can world be 0b100 with fusion constraint? {result2}")
    
    print("\n=== CONCLUSION ===")
    print("The condition3 implementation doesn't enforce world = fusion(h_sk)")
    print("It only ensures minimality in a weaker sense")
    print("This prevents finding countermodels where all h_sk values are empty")

if __name__ == "__main__":
    test_condition3_issue()