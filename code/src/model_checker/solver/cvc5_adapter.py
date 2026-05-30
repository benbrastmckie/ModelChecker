"""cvc5 solver adapter using the pythonic API.

This module wraps cvc5's pythonic interface with a TrackedSolverProtocol-compatible
interface, enabling cvc5 as an alternative backend to Z3.

Key differences from Z3:
- Unsat cores: cvc5 returns formula terms, not labels. We maintain a term-to-label
  mapping to provide Z3-compatible label-based unsat core extraction.
- Model evaluation: cvc5 uses evaluate() or direct indexing, adapter normalizes.
- Timeout: Uses 'tlimit-per' option instead of 'timeout'.
"""

from typing import Any, List, Dict, Optional

from .protocols import SolverResult


class CVC5SolverAdapter:
    """Wraps cvc5.pythonic.Solver with TrackedSolverProtocol-compatible interface.

    This adapter provides:
    - Full pythonic API usage (no mixed base/pythonic calls)
    - Tracked assertion support with label-to-term mapping
    - Unsat core extraction that returns string labels (matching Z3 behavior)
    - Conditional unsat core tracking with diagnostic/performance modes
    """

    def __init__(self, need_unsat_cores: bool = True) -> None:
        """Initialize a new cvc5 solver adapter.

        Args:
            need_unsat_cores: If True, enable unsat core tracking (diagnostic mode).
                If False, disable cores and enable performance optimizations.

        Raises:
            ImportError: If cvc5 package is not installed.
        """
        try:
            from cvc5.pythonic import Solver as CVC5Solver
            self._solver = CVC5Solver()
        except ImportError as e:
            raise ImportError(
                "cvc5 not installed. Install with: pip install cvc5"
            ) from e

        # Store mode for reset() preservation and unsat_core() behavior
        self._need_unsat_cores = need_unsat_cores

        # Configure solver based on mode
        if need_unsat_cores:
            self._configure_diagnostic_mode()
        else:
            self._configure_performance_mode()

        # Label -> constraint mapping for tracked assertions
        self._tracked: Dict[str, Any] = {}
        # id(constraint) -> label for reverse lookup during unsat core
        self._reverse: Dict[int, str] = {}
        # CVC5 term ID -> label for O(1) lookup without string conversion
        self._term_id_to_label: Dict[int, str] = {}
        # String representation -> label fallback for structural matching
        self._str_to_label: Dict[str, str] = {}

    def _configure_diagnostic_mode(self) -> None:
        """Configure solver for diagnostic mode with unsat core tracking enabled."""
        self._solver.set('produce-unsat-cores', 'true')
        # CEGQI (counterexample-guided quantifier instantiation) for BV quantifiers
        self._solver.set('cegqi', 'true')
        self._solver.set('cegqi-bv', 'true')
        self._solver.set('cegqi-full', 'true')

    def _configure_performance_mode(self) -> None:
        """Configure solver for performance mode with optimizations enabled.

        Disables unsat core tracking and enables CVC5-specific optimizations
        that reduce the performance gap with Z3 on UNSAT problems.
        """
        # Task 79 optimizations bundled here for performance mode
        self._solver.set('decision', 'stoponly')
        self._solver.set('bv-eager-eval', 'true')
        # CEGQI (counterexample-guided quantifier instantiation) for BV quantifiers
        self._solver.set('cegqi', 'true')
        self._solver.set('cegqi-bv', 'true')
        self._solver.set('cegqi-full', 'true')

    def add(self, constraint: Any) -> None:
        """Add a constraint to the solver.

        Args:
            constraint: A cvc5 boolean expression.

        Raises:
            TypeError: If constraint is a Z3 expression (wrong backend).
        """
        from .type_guards import assert_backend_types
        assert_backend_types(constraint, "cvc5")
        self._solver.add(constraint)

    def assert_tracked(self, constraint: Any, label: str) -> None:
        """Add a constraint with a tracking label for unsat cores.

        Note: cvc5 pythonic doesn't have assert_and_track like Z3.
        Instead, we track the constraint ourselves and use the check(*assumptions)
        pattern if needed, or match core terms back to labels.

        Args:
            constraint: A cvc5 boolean expression.
            label: String label for identifying this constraint in unsat cores.

        Raises:
            TypeError: If constraint is a Z3 expression (wrong backend).
        """
        from .type_guards import assert_backend_types
        assert_backend_types(constraint, "cvc5")
        self._tracked[label] = constraint
        self._reverse[id(constraint)] = label
        # Layer 2: CVC5 term ID lookup (avoids string conversion)
        if hasattr(constraint, 'get_id'):
            self._term_id_to_label[constraint.get_id()] = label
        # String conversion deferred until unsat_core() is called
        # (CVC5's str() is expensive: ~15ms per term, ~8s total for 523 constraints)
        self._solver.add(constraint)

    def check(self, *assumptions: Any) -> str:
        """Check satisfiability of current constraints.

        Args:
            *assumptions: Optional assumption expressions.

        Returns:
            SolverResult string (sat, unsat, or unknown).
        """
        try:
            from cvc5.pythonic import sat, unsat
        except ImportError:
            sat, unsat = None, None

        if assumptions:
            result = self._solver.check(*assumptions)
        else:
            result = self._solver.check()

        # Handle result conversion
        if sat is not None and result == sat:
            return SolverResult.SAT
        elif unsat is not None and result == unsat:
            return SolverResult.UNSAT
        else:
            # Check string representation
            result_str = str(result).lower()
            if 'sat' in result_str and 'unsat' not in result_str:
                return SolverResult.SAT
            elif 'unsat' in result_str:
                return SolverResult.UNSAT
            return SolverResult.UNKNOWN

    def model(self) -> Any:
        """Get a satisfying model.

        Returns:
            A cvc5 model object.

        Raises:
            RuntimeError: If called when solver is not in sat state.
        """
        return self._solver.model()

    def unsat_core(self) -> List[str]:
        """Get labels of constraints in the unsatisfiable core.

        Note: cvc5's unsat_core() returns actual formula terms.
        We map these back to labels using our tracking dictionaries.

        Returns:
            List of string labels identifying core constraints.
            Returns empty list if unsat cores are disabled (performance mode).
        """
        # Return empty list if cores are disabled (performance mode)
        if not self._need_unsat_cores:
            return []

        try:
            core_terms = self._solver.unsat_core()
        except Exception:
            return []

        # Lazy populate string-to-label mapping only when unsat core is requested
        # (CVC5's str() is expensive: ~15ms per term, so we defer until needed)
        if not self._str_to_label:
            self._str_to_label = {str(c): lbl for lbl, c in self._tracked.items()}

        labels = []
        for term in core_terms:
            # Layer 1: Try direct Python id lookup first
            label = self._reverse.get(id(term))
            if label:
                labels.append(label)
                continue

            # Layer 2: Try CVC5 term ID lookup (avoids string conversion)
            if hasattr(term, 'get_id'):
                label = self._term_id_to_label.get(term.get_id())
                if label:
                    labels.append(label)
                    continue

            # Layer 3: Fallback to string representation matching
            term_str = str(term)
            label = self._str_to_label.get(term_str)
            if label:
                labels.append(label)
                continue

            # Last resort: search tracked constraints for structural match
            for lbl, constraint in self._tracked.items():
                if str(constraint) == term_str:
                    labels.append(lbl)
                    break

        return labels

    def assertions(self) -> Any:
        """Return the list of assertions currently in the solver.

        Returns:
            The assertions from the underlying cvc5 solver.
        """
        return self._solver.assertions()

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
        self._solver.set('tlimit-per', str(ms))

    def reason_unknown(self) -> str:
        """Get the reason for an unknown result.

        Returns:
            String description of why the solver returned unknown.
        """
        try:
            return str(self._solver.reason_unknown())
        except Exception:
            return "unknown"

    def reset(self) -> None:
        """Reset the solver to its initial state.

        Preserves the diagnostic/performance mode configuration.
        """
        try:
            self._solver.reset()
            # Reapply mode configuration after reset
            if self._need_unsat_cores:
                self._configure_diagnostic_mode()
            else:
                self._configure_performance_mode()
        except AttributeError:
            # cvc5 may not have reset, recreate solver
            from cvc5.pythonic import Solver as CVC5Solver
            self._solver = CVC5Solver()
            # Apply mode configuration for new solver
            if self._need_unsat_cores:
                self._configure_diagnostic_mode()
            else:
                self._configure_performance_mode()
        self._tracked.clear()
        self._reverse.clear()
        self._term_id_to_label.clear()
        self._str_to_label.clear()

    def set(self, option: str, value: Any) -> None:
        """Set a solver option.

        Args:
            option: Option name.
            value: Option value.
        """
        self._solver.set(option, str(value))

    @property
    def raw_solver(self) -> Any:
        """Access the underlying cvc5 solver directly.

        This is provided for cases where direct cvc5 access is needed,
        but should be used sparingly to maintain backend compatibility.

        Returns:
            The underlying cvc5.pythonic.Solver instance.
        """
        return self._solver


def cvc5_available() -> bool:
    """Check if cvc5 is available for import.

    Returns:
        True if cvc5 can be imported.
    """
    try:
        import cvc5  # noqa: F401
        return True
    except ImportError:
        return False
