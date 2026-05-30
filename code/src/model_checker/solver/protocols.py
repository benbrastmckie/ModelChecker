"""Protocol definitions for solver abstraction layer.

This module defines Protocol classes for duck-typed solver interfaces.
Protocols allow type checkers to verify compatibility without requiring
inheritance from abstract base classes.
"""

from typing import Protocol, runtime_checkable, Any, List, Optional


@runtime_checkable
class ModelProtocol(Protocol):
    """Protocol for solver model objects that provide evaluation of expressions."""

    def eval(self, expr: Any, model_completion: bool = False) -> Any:
        """Evaluate an expression in this model.

        Args:
            expr: The expression to evaluate.
            model_completion: If True, provide values for unassigned variables.

        Returns:
            The value of the expression in this model.
        """
        ...

    def __getitem__(self, key: Any) -> Any:
        """Get the value assigned to a variable in this model.

        Args:
            key: The variable to look up.

        Returns:
            The value assigned to the variable.
        """
        ...


@runtime_checkable
class SolverProtocol(Protocol):
    """Protocol for SMT solver objects.

    This protocol defines the minimal interface required for solver backends.
    Both Z3 and cvc5 solvers implement this interface.
    """

    def add(self, constraint: Any) -> None:
        """Add a constraint to the solver.

        Args:
            constraint: A boolean constraint expression.
        """
        ...

    def check(self) -> "SolverResult":
        """Check satisfiability of current constraints.

        Returns:
            SolverResult indicating sat, unsat, or unknown.
        """
        ...

    def model(self) -> ModelProtocol:
        """Get a satisfying model (only valid after sat result).

        Returns:
            A model object that can evaluate expressions.
        """
        ...

    def push(self) -> None:
        """Push a new scope onto the solver context stack."""
        ...

    def pop(self, n: int = 1) -> None:
        """Pop scopes from the solver context stack.

        Args:
            n: Number of scopes to pop.
        """
        ...


@runtime_checkable
class TrackedSolverProtocol(SolverProtocol, Protocol):
    """Extended protocol for solvers supporting tracked assertions and unsat cores.

    This extends SolverProtocol with methods for labeling assertions
    and extracting unsatisfiable cores.
    """

    def assert_tracked(self, constraint: Any, label: str) -> None:
        """Add a constraint with a tracking label.

        Args:
            constraint: A boolean constraint expression.
            label: String label for tracking in unsat cores.
        """
        ...

    def unsat_core(self) -> List[str]:
        """Get labels of constraints in the unsatisfiable core.

        Returns:
            List of string labels identifying core constraints.
        """
        ...


class SolverResult:
    """Result of a satisfiability check.

    This class provides string constants for solver results,
    matching both Z3 and cvc5 conventions.
    """

    SAT: str = "sat"
    UNSAT: str = "unsat"
    UNKNOWN: str = "unknown"

    @staticmethod
    def from_z3(result: Any) -> str:
        """Convert a Z3 result object to a SolverResult string.

        Args:
            result: A z3.CheckSatResult object.

        Returns:
            String constant (sat, unsat, or unknown).
        """
        result_str = str(result)
        if result_str == "sat":
            return SolverResult.SAT
        elif result_str == "unsat":
            return SolverResult.UNSAT
        return SolverResult.UNKNOWN

    @staticmethod
    def from_cvc5(result: Any) -> str:
        """Convert a cvc5 result object to a SolverResult string.

        Args:
            result: A cvc5 pythonic result (sat/unsat constant).

        Returns:
            String constant (sat, unsat, or unknown).
        """
        # cvc5.pythonic uses sat/unsat/unknown constants
        result_str = str(result)
        if "sat" in result_str.lower() and "unsat" not in result_str.lower():
            return SolverResult.SAT
        elif "unsat" in result_str.lower():
            return SolverResult.UNSAT
        return SolverResult.UNKNOWN

    @staticmethod
    def is_sat(result: str) -> bool:
        """Check if a result indicates satisfiability.

        Args:
            result: A SolverResult string constant.

        Returns:
            True if result is SAT.
        """
        return result == SolverResult.SAT

    @staticmethod
    def is_unsat(result: str) -> bool:
        """Check if a result indicates unsatisfiability.

        Args:
            result: A SolverResult string constant.

        Returns:
            True if result is UNSAT.
        """
        return result == SolverResult.UNSAT
