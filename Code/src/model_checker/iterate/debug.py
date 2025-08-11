"""Debug utilities for iterator development and troubleshooting.

This module provides instrumented versions of iterator classes and utilities
for debugging constraint generation, model building, and iteration issues.
"""

import z3
import sys
from typing import List, Tuple, Any, Optional, Set
from datetime import datetime

from model_checker.iterate.core import BaseModelIterator


class DebugModelIterator(BaseModelIterator):
    """Instrumented iterator for debugging constraint issues.
    
    This class wraps BaseModelIterator with extensive logging and state
    capture to help diagnose iteration problems, particularly issues with
    finding subsequent models.
    """
    
    def __init__(self, build_example):
        """Initialize with debug tracking enabled."""
        super().__init__(build_example)
        self.debug_log = []
        self.constraint_history = []
        self.solver_state_history = []
        self._log_event("INIT", f"Created iterator for {build_example}")
    
    def _log_event(self, event_type: str, details: Any):
        """Log an event with timestamp."""
        timestamp = datetime.now().strftime("%H:%M:%S.%f")[:-3]
        self.debug_log.append({
            "time": timestamp,
            "type": event_type,
            "details": str(details)
        })
        print(f"[{timestamp}] {event_type}: {details}")
    
    def _get_z3_variables(self, expr) -> Set[str]:
        """Extract all Z3 variables from an expression."""
        variables = set()
        
        def collect_vars(e):
            if z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                variables.add(str(e))
            elif z3.is_app(e):
                for i in range(e.num_args()):
                    collect_vars(e.arg(i))
        
        try:
            collect_vars(expr)
        except:
            pass
        
        return variables
    
    def _add_constraint_to_solver(self, constraint):
        """Override to log constraint additions."""
        # Log the constraint
        self._log_event("ADD_CONSTRAINT", {
            "constraint": str(constraint),
            "variables": list(self._get_z3_variables(constraint)),
            "size": len(str(constraint))
        })
        
        # Capture constraint for history
        self.constraint_history.append({
            "iteration": len(self.found_models),
            "constraint": str(constraint),
            "type": "difference" if "Or" in str(constraint) else "other"
        })
        
        # Add to solver
        self.solver.add(constraint)
        
        # Capture solver state
        self._capture_solver_state()
    
    def _capture_solver_state(self):
        """Capture current solver state for analysis."""
        assertions = self.solver.assertions()
        self.solver_state_history.append({
            "iteration": len(self.found_models),
            "num_assertions": len(assertions),
            "assertions": [str(a) for a in assertions[-5:]]  # Last 5 for brevity
        })
    
    def _build_new_model_structure(self, z3_model, attempt_number, total_attempts):
        """Override to log model building."""
        self._log_event("BUILD_MODEL", {
            "attempt": attempt_number,
            "total_attempts": total_attempts,
            "model_id": id(z3_model)
        })
        
        try:
            result = super()._build_new_model_structure(z3_model, attempt_number, total_attempts)
            self._log_event("BUILD_SUCCESS", f"Model built successfully")
            return result
        except Exception as e:
            self._log_event("BUILD_ERROR", f"Error: {e}")
            raise
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Override to log difference calculation."""
        self._log_event("CALC_DIFF", "Calculating differences between models")
        
        differences = super()._calculate_differences(new_structure, previous_structure)
        
        self._log_event("DIFF_RESULT", {
            "num_differences": len(str(differences)),
            "has_differences": bool(differences)
        })
        
        return differences
    
    def _check_isomorphism(self, new_model, existing_models):
        """Override to log isomorphism checks."""
        self._log_event("ISO_CHECK", f"Checking against {len(existing_models)} models")
        
        for i, existing in enumerate(existing_models):
            is_iso = super()._models_are_isomorphic(new_model, existing)
            if is_iso:
                self._log_event("ISO_FOUND", f"Isomorphic to model {i}")
                return existing
        
        self._log_event("ISO_NONE", "No isomorphism found")
        return None
    
    def iterate(self):
        """Override to wrap entire iteration with debugging."""
        self._log_event("ITERATE_START", f"Starting iteration for {self.max_iterations} models")
        
        try:
            results = super().iterate()
            self._log_event("ITERATE_SUCCESS", f"Found {len(results)} models")
            return results
        except Exception as e:
            self._log_event("ITERATE_ERROR", f"Error: {e}")
            raise
        finally:
            self._print_summary()
    
    def _print_summary(self):
        """Print debugging summary."""
        print("\n" + "="*60)
        print("DEBUG SUMMARY")
        print("="*60)
        print(f"Total events logged: {len(self.debug_log)}")
        print(f"Constraints added: {len(self.constraint_history)}")
        print(f"Models found: {len(self.found_models)}")
        print(f"Final solver assertions: {len(self.solver.assertions())}")
        
        # Print constraint types
        constraint_types = {}
        for c in self.constraint_history:
            ctype = c["type"]
            constraint_types[ctype] = constraint_types.get(ctype, 0) + 1
        
        print("\nConstraint types:")
        for ctype, count in constraint_types.items():
            print(f"  {ctype}: {count}")
        
        print("="*60)


class ConstraintComparator:
    """Compare constraints between different iterator runs."""
    
    def __init__(self):
        self.runs = {}
    
    def capture_run(self, name: str, iterator: DebugModelIterator):
        """Capture a run for comparison."""
        self.runs[name] = {
            "constraints": iterator.constraint_history.copy(),
            "events": iterator.debug_log.copy(),
            "solver_states": iterator.solver_state_history.copy(),
            "models_found": len(iterator.found_models)
        }
    
    def compare_runs(self, run1_name: str, run2_name: str) -> List[dict]:
        """Compare two captured runs and return differences."""
        if run1_name not in self.runs or run2_name not in self.runs:
            raise ValueError(f"Missing run data for comparison")
        
        run1 = self.runs[run1_name]
        run2 = self.runs[run2_name]
        
        differences = []
        
        # Compare number of models found
        if run1["models_found"] != run2["models_found"]:
            differences.append({
                "type": "model_count",
                "run1": run1["models_found"],
                "run2": run2["models_found"]
            })
        
        # Compare constraints
        constraints1 = [c["constraint"] for c in run1["constraints"]]
        constraints2 = [c["constraint"] for c in run2["constraints"]]
        
        for i, (c1, c2) in enumerate(zip(constraints1, constraints2)):
            if c1 != c2:
                differences.append({
                    "type": "constraint_mismatch",
                    "index": i,
                    "run1": c1[:100] + "..." if len(c1) > 100 else c1,
                    "run2": c2[:100] + "..." if len(c2) > 100 else c2
                })
        
        # Check for different number of constraints
        if len(constraints1) != len(constraints2):
            differences.append({
                "type": "constraint_count",
                "run1": len(constraints1),
                "run2": len(constraints2)
            })
        
        return differences
    
    def print_comparison(self, run1_name: str, run2_name: str):
        """Print a formatted comparison of two runs."""
        differences = self.compare_runs(run1_name, run2_name)
        
        print(f"\nComparing {run1_name} vs {run2_name}")
        print("="*60)
        
        if not differences:
            print("No differences found - runs are identical")
        else:
            print(f"Found {len(differences)} differences:")
            for i, diff in enumerate(differences, 1):
                print(f"\n{i}. {diff['type']}:")
                if diff["type"] == "model_count":
                    print(f"   {run1_name}: {diff['run1']} models")
                    print(f"   {run2_name}: {diff['run2']} models")
                elif diff["type"] == "constraint_mismatch":
                    print(f"   At index {diff['index']}:")
                    print(f"   {run1_name}: {diff['run1']}")
                    print(f"   {run2_name}: {diff['run2']}")
                elif diff["type"] == "constraint_count":
                    print(f"   {run1_name}: {diff['run1']} constraints")
                    print(f"   {run2_name}: {diff['run2']} constraints")
        
        print("="*60)


def create_minimal_test_case(theory_name: str = "relevance"):
    """Create a minimal test case that reproduces MODEL 2 issues."""
    
    test_code = '''"""Minimal test case for iterator debugging."""

from model_checker.builder.build_module import BuildModule

# Minimal relevance example that should find 2 models
example_str = """
# Settings
iterate = 2

# Syntax  
A prop
B prop

# Logics
{A and B} premise
A conc

# Check: Should find MODEL 1 where A,B true and MODEL 2 where A true, B false
"""

def run_test():
    """Run the minimal test."""
    module = BuildModule({"raw_text": example_str})
    examples = module.valid_examples()
    
    if not examples:
        print("No valid examples found!")
        return
    
    example = examples[0]
    print(f"Running: {example}")
    
    # This should find 2 models
    return module.print_all()

if __name__ == "__main__":
    run_test()
'''
    
    with open("minimal_iterator_test.py", "w") as f:
        f.write(test_code)
    
    print("Created minimal_iterator_test.py")
    return "minimal_iterator_test.py"


# Helper function for debugging specific theories
def debug_theory_iterator(theory_module_path: str, example_name: str):
    """Debug a specific theory's iterator.
    
    Args:
        theory_module_path: Path to theory module (e.g., "logos.relevance") 
        example_name: Name of example to debug (e.g., "REL_CM_1")
    """
    # This would be implemented to load and debug specific examples
    pass