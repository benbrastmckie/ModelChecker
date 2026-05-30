"""Solver backend registry and selection logic.

This module manages solver backend selection with the following priority:
1. CLI flag (--z3, --cvc5)
2. Environment variable (MODEL_CHECKER_SOLVER)
3. Settings configuration
4. Default (z3)
"""

import os
from typing import Optional, Dict, Any, Callable, TYPE_CHECKING

if TYPE_CHECKING:
    from .protocols import TrackedSolverProtocol

# Module-level state for active backend
_active_backend: Optional[str] = None
_cli_override: Optional[str] = None

# Available backends registry
_available_backends: Dict[str, bool] = {}
_backend_factories: Dict[str, Callable[[], "TrackedSolverProtocol"]] = {}


def detect_z3() -> bool:
    """Check if Z3 is available.

    Returns:
        True if z3 package can be imported.
    """
    if "z3" in _available_backends:
        return _available_backends["z3"]
    try:
        import z3  # noqa: F401
        _available_backends["z3"] = True
        return True
    except ImportError:
        _available_backends["z3"] = False
        return False


def detect_cvc5() -> bool:
    """Check if cvc5 is available.

    Returns:
        True if cvc5 package can be imported.
    """
    if "cvc5" in _available_backends:
        return _available_backends["cvc5"]
    try:
        import cvc5  # noqa: F401
        _available_backends["cvc5"] = True
        return True
    except ImportError:
        _available_backends["cvc5"] = False
        return False


def set_cli_backend(backend: str) -> None:
    """Set the solver backend from CLI flag.

    This has highest priority and overrides all other settings.

    Note: For proper cache invalidation when switching backends, use
    lifecycle.set_backend_with_invalidation() instead of calling this
    function directly. This function only sets the backend variable
    without clearing cached expressions.

    Args:
        backend: The backend name ("z3" or "cvc5").

    Raises:
        ValueError: If backend is not a valid name.
    """
    global _cli_override
    if backend not in ("z3", "cvc5"):
        raise ValueError(f"Unknown solver backend: {backend}")
    _cli_override = backend


def clear_cli_backend() -> None:
    """Clear CLI backend override (useful for testing)."""
    global _cli_override
    _cli_override = None


def get_active_backend(settings: Optional[Dict[str, Any]] = None) -> str:
    """Get the active solver backend name.

    Priority order:
    1. CLI flag (set via set_cli_backend)
    2. Environment variable MODEL_CHECKER_SOLVER
    3. Settings configuration (solver key)
    4. Default: "z3"

    Args:
        settings: Optional settings dict with 'solver' key.

    Returns:
        Backend name ("z3" or "cvc5").
    """
    global _active_backend

    # 1. CLI flag has highest priority
    if _cli_override:
        return _cli_override

    # 2. Environment variable
    env_solver = os.environ.get("MODEL_CHECKER_SOLVER")
    if env_solver and env_solver in ("z3", "cvc5"):
        return env_solver

    # 3. Settings configuration
    if settings and "solver" in settings:
        return settings["solver"]

    # 4. Default to z3
    return "z3"


def validate_backend(backend: str) -> None:
    """Validate that the requested backend is available.

    Args:
        backend: The backend name to validate.

    Raises:
        ImportError: If the requested backend is not installed.
        ValueError: If the backend name is unknown.
    """
    if backend == "z3":
        if not detect_z3():
            raise ImportError(
                "Z3 not installed. Install with: pip install z3-solver"
            )
    elif backend == "cvc5":
        if not detect_cvc5():
            raise ImportError(
                "cvc5 not installed. Install with: pip install cvc5"
            )
    else:
        raise ValueError(f"Unknown solver backend: {backend}")


def register_backend_factory(name: str, factory: Callable[[], "TrackedSolverProtocol"]) -> None:
    """Register a solver factory for a backend.

    Args:
        name: Backend name ("z3" or "cvc5").
        factory: Callable that returns a new solver instance.
    """
    _backend_factories[name] = factory


def create_solver(settings: Optional[Dict[str, Any]] = None) -> "TrackedSolverProtocol":
    """Create a solver instance using the active backend.

    Args:
        settings: Optional settings dict for backend selection and mode configuration.
            For CVC5, unsat cores are enabled when print_constraints or print_z3
            is True (diagnostic mode). Otherwise, performance mode is used.

    Returns:
        A solver instance conforming to TrackedSolverProtocol.

    Raises:
        ImportError: If the selected backend is not available.
        RuntimeError: If no factory is registered for the backend.
    """
    backend = get_active_backend(settings)
    validate_backend(backend)

    if backend in _backend_factories:
        return _backend_factories[backend]()

    # Lazy import and registration
    if backend == "z3":
        from .z3_adapter import Z3SolverAdapter
        return Z3SolverAdapter()
    elif backend == "cvc5":
        from .cvc5_adapter import CVC5SolverAdapter
        # Auto-detect if unsat cores are needed from print settings
        # Cores are needed when user wants to see constraint details
        need_unsat_cores = _detect_unsat_core_requirement(settings)
        return CVC5SolverAdapter(need_unsat_cores=need_unsat_cores)

    raise RuntimeError(f"No factory registered for backend: {backend}")


def _detect_unsat_core_requirement(settings: Optional[Dict[str, Any]]) -> bool:
    """Detect if unsat cores are needed based on settings.

    Unsat cores are required when:
    - print_constraints is True (user wants to see constraint details)
    - print_z3 is True (user wants to see Z3/solver output)

    Args:
        settings: Optional settings dict with print flags.

    Returns:
        True if unsat cores should be enabled (diagnostic mode),
        False for performance mode.
    """
    if settings is None:
        return False

    return settings.get('print_constraints', False) or settings.get('print_z3', False)


def list_available_backends() -> Dict[str, bool]:
    """List all known backends and their availability status.

    Returns:
        Dict mapping backend names to availability booleans.
    """
    return {
        "z3": detect_z3(),
        "cvc5": detect_cvc5(),
    }


def reset_registry() -> None:
    """Reset the registry state (useful for testing).

    Clears cached availability checks and CLI overrides.
    """
    global _available_backends, _cli_override, _active_backend
    _available_backends = {}
    _cli_override = None
    _active_backend = None
