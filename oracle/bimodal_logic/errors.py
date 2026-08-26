"""bimodal_logic.errors - Exceptions raised by the Z3 oracle provider.

This module is intentionally small and self-contained: `oracle/` ships no
packaging metadata and must not acquire a cross-package dependency on
`model_checker.theory_lib.errors` for a single exception shape. The class
below mirrors the *shape* of that package's `Z3TimeoutError` (a formatted
message, a `context` dict, and a `suggestion` string) without importing or
subclassing it.
"""

from __future__ import annotations

from typing import Any


class OracleTimeoutError(Exception):
    """Raised when the Z3 solver exhausts its time budget without deciding.

    This is distinct from a genuine "no countermodel exists" (UNSAT) result:
    it signals that the solver did not reach a verdict within `timeout_ms`,
    not that the formula was proven valid. Callers that previously treated a
    `None` return from `find_countermodel()` as "valid" must instead handle
    this exception as a third, inconclusive outcome.
    """

    def __init__(
        self,
        timeout_ms: int,
        temporal_depth: int,
        M: int,
        suggestion: str | None = None,
        max_rlimit: int | None = None,
    ) -> None:
        if max_rlimit:
            # An rlimit-exhausted UNKNOWN is classified identically to a
            # wall-clock timeout by ModelDefaults.solve() (is_timeout=True
            # either way -- see code/docs/core/TESTING_GUIDE.md section 8.6),
            # so the message must not claim the wall-clock budget is what
            # fired when a deterministic rlimit budget was also in play.
            message = (
                f"Z3 solver did not decide the formula within {timeout_ms} ms "
                f"or {max_rlimit} rlimit units "
                f"(temporal_depth={temporal_depth}, time_bound M={M}); "
                "treat as inconclusive, not as a proof of validity"
            )
        else:
            message = (
                f"Z3 solver did not decide the formula within {timeout_ms} ms "
                f"(temporal_depth={temporal_depth}, time_bound M={M}); "
                "treat as inconclusive, not as a proof of validity"
            )
        self.context: dict[str, Any] = {
            "timeout_ms": timeout_ms,
            "temporal_depth": temporal_depth,
            "M": M,
        }
        if max_rlimit:
            self.context["max_rlimit"] = max_rlimit
        self.suggestion = suggestion or (
            "Increase timeout_ms, or reduce the formula's temporal_depth, "
            "and retry; a timeout is not evidence the formula is valid."
        )
        super().__init__(message)

    def __str__(self) -> str:
        parts = [str(self.args[0])]
        if self.suggestion:
            parts.append(f"Suggestion: {self.suggestion}")
        return " | ".join(parts)
