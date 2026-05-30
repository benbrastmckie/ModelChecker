"""Z3 solver adapter - thin passthrough for zero overhead.

This module wraps z3.Solver with a protocol-compatible interface.
The adapter is designed to be as thin as possible to avoid performance
overhead when using Z3 (the default backend).
"""

from typing import Any, List, Dict, Optional
import z3

from .protocols import SolverResult


class Z3SolverAdapter:
    """Wraps z3.Solver with TrackedSolverProtocol-compatible interface.

    This adapter provides:
    - Direct passthrough of z3.Solver methods for zero overhead
    - Tracked assertion support via assert_and_track
    - Unsat core extraction with string labels
    """

    def __init__(self) -> None:
        """Initialize a new Z3 solver adapter."""
        self._solver = z3.Solver()
        self._tracked: Dict[str, Any] = {}  # label -> constraint
        self._configure_quantifier_mode()

    def _configure_quantifier_mode(self) -> None:
        """Configure Z3 for reliable quantifier handling.

        Explicitly sets quantifier instantiation strategy instead of relying
        on auto_config. This prevents Z3 from selecting a strategy that may
        be incomplete for the UFBV fragment used by native quantifiers.

        Memory guard (Task 97, 2026-05-29):
          - max_memory: per-solver memory limit (MB) to prevent OOM kills.
            Set to 4096 MB (4 GB). This directly addresses the OOM kills described
            in task 98 (bimodal theorems with M>=3) by ensuring the solver process
            is hard-stopped rather than killed by the OS at a higher memory usage.

        NOTE: qi.max_instances was tested but causes 'unknown' results on countermodel
        examples that require many quantifier instantiations (BM_CM_2, BM_CM_4).
        Not safe to cap without thorough per-example profiling.
        """
        self._solver.set('auto_config', False)
        self._solver.set('smt.mbqi', True)
        self._solver.set('smt.ematching', True)
        self._solver.set('smt.mbqi.max_iterations', 1000)
        # Task 98 tuning: smt.mbqi.max_cexs limits the number of counterexample candidates
        # MBQI generates per round, bounding ground term growth. Tested at 50 and found
        # safe (no regressions) with no measurable memory reduction for our constraint set.
        # Not added because the benefit is marginal and the max_memory limit is sufficient.
        # If testing again: self._solver.set('smt.mbqi.max_cexs', 50)
        # Memory guard: 4096 MB per solver instance. Prevents OOM kills from unbounded
        # quantifier instantiation. Causes Z3 to return 'unknown' gracefully instead of
        # being killed by the OS. Direct mitigation for task 98 OOM investigation.
        self._solver.set('max_memory', 4096)

    def add(self, constraint: Any) -> None:
        """Add a constraint to the solver.

        Args:
            constraint: A Z3 boolean expression.

        Raises:
            TypeError: If constraint is a CVC5 expression (wrong backend).
        """
        from .type_guards import assert_backend_types
        assert_backend_types(constraint, "z3")
        self._solver.add(constraint)

    def assert_tracked(self, constraint: Any, label: str) -> None:
        """Add a constraint with a tracking label for unsat cores.

        Args:
            constraint: A Z3 boolean expression.
            label: String label for identifying this constraint in unsat cores.

        Raises:
            TypeError: If constraint is a CVC5 expression (wrong backend).
        """
        from .type_guards import assert_backend_types
        assert_backend_types(constraint, "z3")
        # Create a tracking boolean
        track_var = z3.Bool(label)
        self._tracked[label] = constraint
        self._solver.assert_and_track(constraint, track_var)

    def check(self, *assumptions: Any) -> str:
        """Check satisfiability of current constraints.

        Args:
            *assumptions: Optional assumption expressions.

        Returns:
            SolverResult string (sat, unsat, or unknown).
        """
        if assumptions:
            result = self._solver.check(*assumptions)
        else:
            result = self._solver.check()
        return SolverResult.from_z3(result)

    def model(self) -> z3.ModelRef:
        """Get a satisfying model.

        Returns:
            A Z3 model reference.

        Raises:
            z3.Z3Exception: If called when solver is not in sat state.
        """
        return self._solver.model()

    def unsat_core(self) -> List[str]:
        """Get labels of constraints in the unsatisfiable core.

        Returns:
            List of string labels identifying core constraints.
        """
        core = self._solver.unsat_core()
        # Z3 returns BoolRefs that we created as tracking variables
        # We need to convert them back to string labels
        labels = []
        for item in core:
            label = str(item)
            if label in self._tracked:
                labels.append(label)
        return labels

    def push(self) -> None:
        """Push a new scope onto the solver context stack."""
        self._solver.push()

    def pop(self, n: int = 1) -> None:
        """Pop scopes from the solver context stack.

        Args:
            n: Number of scopes to pop.
        """
        self._solver.pop(n)

    def set_timeout(self, ms: int) -> None:
        """Set a timeout for solver operations.

        Args:
            ms: Timeout in milliseconds.
        """
        self._solver.set("timeout", ms)

    def reason_unknown(self) -> str:
        """Get the reason for an unknown result.

        Returns:
            String description of why the solver returned unknown.
        """
        return self._solver.reason_unknown()

    def assertions(self) -> List[Any]:
        """Get all current assertions.

        Returns:
            List of Z3 expressions representing current constraints.
        """
        return list(self._solver.assertions())

    def reset(self) -> None:
        """Reset the solver to its initial state."""
        self._solver.reset()
        self._tracked.clear()

    def set(self, option: str, value: Any) -> None:
        """Set a solver option.

        Args:
            option: Option name.
            value: Option value.
        """
        self._solver.set(option, value)

    @property
    def raw_solver(self) -> z3.Solver:
        """Access the underlying Z3 solver directly.

        This is provided for cases where direct Z3 access is needed,
        but should be used sparingly to maintain backend compatibility.

        Returns:
            The underlying z3.Solver instance.
        """
        return self._solver
