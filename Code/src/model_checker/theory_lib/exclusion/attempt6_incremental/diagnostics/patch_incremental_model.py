"""
Patch the IncrementalModelStructure to add debugging output.
"""

import sys
from pathlib import Path

# Add paths
sys.path.insert(0, str(Path(__file__).parent.parent))

# Import and patch
from incremental_model import IncrementalModelStructure

# Store original method
original_solve = IncrementalModelStructure.solve_incrementally_pure

def patched_solve(self, max_time):
    """Patched version with debugging output."""
    print("\n=== DEBUGGING solve_incrementally_pure ===")
    
    try:
        import time
        start_time = time.time()
        
        # Set up incremental solver
        self.incremental_solver.reset()
        self.incremental_solver.set_timeout(max_time)
        
        # Phase 1: Add frame constraints
        print("\nPhase 1: Adding frame constraints...")
        if not self._add_frame_constraints():
            print("  ❌ Frame constraints made system UNSAT!")
            return self._create_result(False, None, False, start_time)
        print("  ✓ Frame constraints added successfully")
        
        # Phase 2: Add atomic proposition constraints
        print("\nPhase 2: Adding atomic constraints...")
        if not self._add_atomic_constraints():
            print("  ❌ Atomic constraints made system UNSAT!")
            return self._create_result(False, None, False, start_time)
        print("  ✓ Atomic constraints added successfully")
        
        # Phase 3: Add premise constraints
        print("\nPhase 3: Adding premise constraints...")
        if not self._add_premise_constraints_incremental():
            print("  ❌ Premise constraints made system UNSAT!")
            return self._create_result(False, None, False, start_time)
        print("  ✓ Premise constraints added successfully")
        
        # Phase 4: Add conclusion constraints
        print("\nPhase 4: Adding conclusion constraints...")
        if not self._add_conclusion_constraints_incremental():
            print("  ❌ Conclusion constraints made system UNSAT!")
            return self._create_result(False, None, False, start_time)
        print("  ✓ Conclusion constraints added successfully")
        
        # Final check
        print("\nFinal satisfiability check...")
        final_result = self.incremental_solver.check()
        print(f"Final result: {final_result}")
        
        if final_result == "sat":
            model = self.incremental_solver.model()
            return self._create_result(False, model, True, start_time)
        else:
            return self._create_result(False, None, False, start_time)
            
    except Exception as e:
        print(f"\n❌ Error in solve_incrementally_pure: {e}")
        import traceback
        traceback.print_exc()
        return self._create_result(False, None, False, start_time)

# Apply patch
IncrementalModelStructure.solve_incrementally_pure = patched_solve

print("✓ IncrementalModelStructure patched with debugging output")

# Now run the example
if __name__ == "__main__":
    print("\n=== Running NEG_TO_SENT example with debugging ===")
    
    # Import and run
    sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent.parent))
    
    # Use the command line interface
    import subprocess
    result = subprocess.run([
        sys.executable,
        "/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/dev_cli.py",
        "/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/exclusion/attempt6_incremental/examples.py"
    ], capture_output=True, text=True)
    
    print(result.stdout)
    if result.stderr:
        print("STDERR:", result.stderr)