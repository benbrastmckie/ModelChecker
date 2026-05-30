"""Solver abstraction layer for ModelChecker.

This package provides a unified interface for SMT solvers, enabling
ModelChecker to use Z3, cvc5, or other compatible backends.

Usage:
    from model_checker.solver import create_solver, get_active_backend
    from model_checker.solver.protocols import SolverResult

    solver = create_solver()
    solver.add(constraint)
    result = solver.check()
    if SolverResult.is_sat(result):
        model = solver.model()

Backend Selection:
    - CLI flag: --z3 or --cvc5
    - Environment variable: MODEL_CHECKER_SOLVER=z3|cvc5
    - Settings: general_settings["solver"] = "z3"|"cvc5"
    - Default: z3
"""

from .protocols import (
    SolverProtocol,
    TrackedSolverProtocol,
    ModelProtocol,
    SolverResult,
)
from .registry import (
    create_solver,
    get_active_backend,
    set_cli_backend,
    clear_cli_backend,
    validate_backend,
    detect_z3,
    detect_cvc5,
    list_available_backends,
)
from .types import (
    SolverExpr,
    SolverModel,
    SolverSort,
    BoolExpr,
    BitVecExpr,
    ArithExpr,
    BackendName,
    ConstraintLabel,
)
from .compat import (
    is_true,
    is_false,
    simplify,
    eval_model,
    get_bitvec_value,
    substitute,
)
from .types_runtime import (
    SolverException,
    get_native_exception,
)

__all__ = [
    # Protocols
    "SolverProtocol",
    "TrackedSolverProtocol",
    "ModelProtocol",
    "SolverResult",
    # Registry
    "create_solver",
    "get_active_backend",
    "set_cli_backend",
    "clear_cli_backend",
    "validate_backend",
    "detect_z3",
    "detect_cvc5",
    "list_available_backends",
    # Types
    "SolverExpr",
    "SolverModel",
    "SolverSort",
    "BoolExpr",
    "BitVecExpr",
    "ArithExpr",
    "BackendName",
    "ConstraintLabel",
    # Compat helpers
    "is_true",
    "is_false",
    "simplify",
    "eval_model",
    "get_bitvec_value",
    "substitute",
    # Runtime types and exceptions
    "SolverException",
    "get_native_exception",
]
