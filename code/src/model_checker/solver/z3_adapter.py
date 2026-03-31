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
