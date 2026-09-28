"""Production-side independent checker resolver: is a standalone `check_certificate` binary
available, and how do I invoke it?

## Why this module exists, and why it is not `tests/_lean_check.py`

`tests/_lean_check.py` answers the same question, but it lives in the test tree, runs its
60-second `probe()` unconditionally at import time (`PROBE_TIMEOUT_SECONDS = 60`, sized for a
`lake exe` build check), and is imported by production code nowhere. A mandatory per-run gate on
every reported countermodel (see `semantic/model.py`'s module docstring, "The re-check hook")
cannot pay a 60-second import-time cost, and must not make production code depend on the test
tree. This module is the inversion: `tests/_lean_check.py` is refactored (a later phase) to
delegate to this one, never the other way around.

## Resolution order

1. `BIMODAL_CHECKER_BIN` -- an explicit binary path, set by a user who obtained a standalone
   checker artifact directly. Takes precedence over everything else because it is the most
   specific signal of intent.
2. A standalone binary cached at `$XDG_CACHE_HOME/model_checker/bimodal/check_certificate`
   (`~/.cache/model_checker/bimodal/check_certificate` when `XDG_CACHE_HOME` is unset) -- the
   location an out-of-band installer would populate.
3. The built binary inside a `BIMODAL_LOGIC_PATH` checkout (or `~/Projects/BimodalLogic` when
   unset), at `.lake/build/bin/check_certificate`, invoked **directly** -- never through
   `lake exe check_certificate`, which pays `lake`'s own build-check overhead (~2.2s) on every
   invocation; the built binary alone costs ~50ms (measured; see
   `docs/SETTINGS.md`'s "Certificate Verification" section).
4. Unavailable.

## Lazy, bounded, memoized

Nothing above is probed until `resolve_checker()` is first called, and the result is memoized
for the lifetime of the process -- importing this module performs no subprocess call. Each
candidate's probe is bounded by `PROBE_TIMEOUT_SECONDS`, sized for the ~50ms binary this module
invokes directly, not for a `lake` build.

## The capability handshake (not the commit pin)

A resolved binary is not accepted as available merely because it exists and responds: its
response to a trivial, well-formed probe certificate must additionally carry a `status` of
`"countermodel"`, an `"acceptance"` value in the vocabulary
`BimodalTools/CertificateImport.lean`'s `Acceptance` inductive actually defines (`"decided"`,
`"entailment"`), and an `"echo"` that matches the exact bytes this module sent, bytewise. This is
the *enforcement* mechanism: `tests/_lean_check.py` used to also carry a `BIMODAL_LOGIC_COMMIT`
pin, consumed by nothing, which had already drifted (from `d55e2760` to `d1a24b30`, observed
same-day) before this module existed, and has since been retired. Pinning a commit cannot
prevent a checkout from being rebuilt at a different, incompatible commit; checking the binary's
actual behaviour can. A
checkout resolution therefore records its checkout's HEAD as *provenance* for the output label
-- informational, not a gate -- while the handshake is the real gate.

**Environment absence versus capability/protocol failure.** Mirroring the split
`tests/_lean_check.py`'s own module docstring insists on keeping (a prior single-vocabulary probe
once let a real regression through as a silent skip): a candidate that never responds within the
timeout is an *environment* condition (nothing to talk to). A candidate that responds, but not
with the expected shape, is a *capability* or *protocol* failure -- the binary exists and runs,
but this module cannot trust what it says. All three are folded into a single `Unavailable`
reason string here (this module has no test collection to skip cleanly out of, unlike
`tests/_lean_check.py`), but the reason text always names which of the three occurred, so a
consumer or log reader can tell them apart.

## Optional integrity pinning

When a SHA-256 digest is configured -- via `BIMODAL_CHECKER_SHA256`, or a `<binary>.sha256` file
beside a cached or explicit binary -- a resolved binary whose digest does not match is refused
before it is even invoked, with a named reason. Absent any configured digest, no check is
performed: this is the hook an out-of-band artifact-distribution route needs, not a new
mandatory requirement on every user.
"""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import threading
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

from .certificate import canonical_wire_bytes

__all__ = [
    "CACHE_BINARY_NAME",
    "CHECK_TIMEOUT_SECONDS",
    "KNOWN_ACCEPTANCE_VALUES",
    "PROBE_TIMEOUT_SECONDS",
    "CheckerHandle",
    "CheckOutcome",
    "ProtocolFailure",
    "Unavailable",
    "cache_dir",
    "check_certificate",
    "resolve_checker",
]

# Bound appropriate to a ~50ms binary invoked directly (measured: see checker.py's module
# docstring), not to a `lake` build -- deliberately far smaller than
# `tests/_lean_check.py`'s PROBE_TIMEOUT_SECONDS = 60.
PROBE_TIMEOUT_SECONDS: float = 5.0

# Default bound for a real (non-probe) invocation. Generous relative to the measured ~50ms cost
# to tolerate a larger certificate than the trivial probe payload, while still being bounded.
CHECK_TIMEOUT_SECONDS: float = 10.0

CACHE_BINARY_NAME = "check_certificate"

# `BimodalTools/CertificateImport.lean`'s `Acceptance` inductive: exactly these two
# constructors exist today (`decided`, `entailment`); a third, reserved for per-certificate
# kernel checking, is explicitly not introduced there yet (see that module's docstring). An
# `acceptance` value outside this set is a capability failure naming the value seen, not a
# silent pass-through -- a future third value must be added here deliberately, not by accident.
KNOWN_ACCEPTANCE_VALUES = frozenset({"decided", "entailment"})

_PROBE_PAYLOAD: Dict[str, Any] = {
    "target": {"premises": [], "conclusions": [{"tag": "atom", "name": "p"}], "time": 0},
    "bx": [],
    "lassos": [{"back": [[]], "mid": [], "fwd": [[]]}],
}


def cache_dir() -> Path:
    """`$XDG_CACHE_HOME/model_checker/bimodal`, or `~/.cache/model_checker/bimodal` when
    `XDG_CACHE_HOME` is unset -- the location an out-of-band installer populates."""
    xdg = os.environ.get("XDG_CACHE_HOME")
    base = Path(xdg).expanduser() if xdg else Path("~/.cache").expanduser()
    return base / "model_checker" / "bimodal"


@dataclass(frozen=True)
class CheckerHandle:
    """A resolved, handshake-verified checker: where it lives, which resolution step found
    it, and (for a checkout resolution only) the checkout's HEAD commit as recorded
    provenance -- informational, never a gate (see module docstring)."""

    path: Path
    source: str  # "explicit" | "cache" | "checkout"
    provenance: Optional[str] = None


@dataclass(frozen=True)
class Unavailable:
    """No checker resolved. `reason` names every candidate tried and why each was rejected,
    using the vocabulary "environment absence" / "capability failure" / "protocol failure"
    from the module docstring so a reader can tell the three apart."""

    reason: str


@dataclass(frozen=True)
class CheckOutcome:
    """The result of a real (non-probe) `check_certificate` invocation.

    `available` is `False` exactly when no checker could be resolved or the resolved checker
    did not respond in time; `reason` names why. Otherwise `verdict` carries the parsed JSON
    verdict, `sent` the exact canonical bytes sent, and `checker` the handle that produced it.
    """

    available: bool
    reason: Optional[str] = None
    verdict: Optional[Dict[str, Any]] = None
    sent: Optional[str] = None
    checker: Optional[CheckerHandle] = None


class ProtocolFailure(RuntimeError):
    """Raised by `check_certificate` when a resolved checker responds to a *real* certificate,
    but its `echo` does not match the exact bytes sent -- the two sides are talking about
    different certificates (mirrors `tests/_lean_check.py`'s `assert_echo_matches_sent`).
    This is deliberately an exception, not folded into `CheckOutcome`: a protocol failure must
    surface as loudly as `semantic/model.py`'s existing mandatory `recheck` guard, never be
    swallowed as an ordinary "unavailable" or "rejected" outcome.
    """


def _invoke(binary: Path, payload: Dict[str, Any], timeout: float) -> Tuple[Optional[Dict[str, Any]], str]:
    """Invoke `binary` directly (never through `lake exe`) on one JSON payload. Returns
    `(verdict, sent)`; `verdict` is `None` on timeout, a non-zero exit, a missing binary, or an
    unparseable response -- the caller decides how to report that."""
    sent = canonical_wire_bytes(payload)
    try:
        result = subprocess.run(
            [str(binary)],
            input=sent,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except (subprocess.TimeoutExpired, OSError):
        return None, sent
    if result.returncode != 0:
        return None, sent
    line = result.stdout.strip().splitlines()[-1] if result.stdout.strip() else ""
    try:
        return json.loads(line), sent
    except (json.JSONDecodeError, IndexError):
        return None, sent


def _validate_handshake(verdict: Dict[str, Any], sent: str) -> Optional[str]:
    """The capability handshake against a probe response. Returns `None` on success, else a
    reason naming which of "capability failure" / "protocol failure" occurred (module
    docstring's vocabulary)."""
    if verdict.get("status") != "countermodel":
        return f"capability failure: probe certificate produced unexpected verdict: {verdict!r}"
    acceptance = verdict.get("acceptance")
    if acceptance is None:
        return "capability failure: probe certificate is missing the 'acceptance' field"
    if acceptance not in KNOWN_ACCEPTANCE_VALUES:
        return (
            "capability failure: probe certificate carries an acceptance value outside the "
            f"known vocabulary {sorted(KNOWN_ACCEPTANCE_VALUES)!r}: {acceptance!r}"
        )
    echo = verdict.get("echo")
    if echo is None or echo.strip() != sent.strip():
        return "protocol failure: probe certificate's echo does not match the bytes sent"
    return None


def _expected_digest(binary: Path) -> Optional[str]:
    """The configured SHA-256 digest for `binary`, or `None` if none is configured.
    `BIMODAL_CHECKER_SHA256` takes precedence over a `<binary>.sha256` file beside it."""
    env_digest = os.environ.get("BIMODAL_CHECKER_SHA256")
    if env_digest:
        return env_digest.strip().lower()
    digest_file = binary.parent / (binary.name + ".sha256")
    if digest_file.is_file():
        return digest_file.read_text().strip().split()[0].lower()
    return None


def _digest_matches(binary: Path, expected: str) -> bool:
    digest = hashlib.sha256()
    with open(binary, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest().lower() == expected.lower()


def _git_head(checkout_root: Path) -> Optional[str]:
    """Best-effort: the checkout's HEAD commit, or `None` if `git` is unavailable or the
    checkout is not a git repository. Recorded as provenance only -- see module docstring for
    why this is not the enforcement mechanism."""
    try:
        result = subprocess.run(
            ["git", "-C", str(checkout_root), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            timeout=5,
        )
    except (subprocess.TimeoutExpired, OSError):
        return None
    if result.returncode != 0:
        return None
    return result.stdout.strip() or None


def _explicit_candidate() -> Optional[Tuple[str, Path, Optional[Path]]]:
    value = os.environ.get("BIMODAL_CHECKER_BIN")
    if not value:
        return None
    return ("explicit", Path(value).expanduser(), None)


def _cache_candidate() -> Optional[Tuple[str, Path, Optional[Path]]]:
    """Unlike `_explicit_candidate`, this is an automatic discovery location, not a
    user-declared one -- it counts as a candidate only when a binary actually sits there, so
    an ordinary "nothing configured" environment reports that cleanly rather than naming a
    location the user never asked about."""
    candidate = cache_dir() / CACHE_BINARY_NAME
    return ("cache", candidate, None) if candidate.is_file() else None


def _checkout_candidate() -> Optional[Tuple[str, Path, Optional[Path]]]:
    """Automatic discovery, like `_cache_candidate`: counts as a candidate only when the
    checkout and its built binary both actually exist."""
    env_path = os.environ.get("BIMODAL_LOGIC_PATH")
    root = Path(env_path).expanduser() if env_path else Path("~/Projects/BimodalLogic").expanduser()
    if not (root.is_dir() and (root / "lakefile.toml").is_file()):
        return None
    binary = root / ".lake" / "build" / "bin" / CACHE_BINARY_NAME
    return ("checkout", binary, root) if binary.is_file() else None


def _candidates() -> list:
    found = []
    for factory in (_explicit_candidate, _cache_candidate, _checkout_candidate):
        candidate = factory()
        if candidate is not None:
            found.append(candidate)
    return found


def _resolve_uncached() -> "object":
    candidates = _candidates()
    if not candidates:
        return Unavailable(
            reason=(
                "environment absence: no checker candidate configured -- set "
                "BIMODAL_CHECKER_BIN, place a binary at "
                f"{cache_dir() / CACHE_BINARY_NAME}, or check out BimodalLogic "
                "(BIMODAL_LOGIC_PATH or ~/Projects/BimodalLogic) with check_certificate built"
            )
        )

    reasons = []
    for source, path, checkout_root in candidates:
        if not path.is_file():
            reasons.append(f"{source} ({path}): environment absence: no such file")
            continue
        expected_digest = _expected_digest(path)
        if expected_digest is not None and not _digest_matches(path, expected_digest):
            reasons.append(
                f"{source} ({path}): capability failure: does not match the configured "
                "SHA-256 digest"
            )
            continue
        verdict, sent = _invoke(path, _PROBE_PAYLOAD, PROBE_TIMEOUT_SECONDS)
        if verdict is None:
            reasons.append(
                f"{source} ({path}): environment absence: did not respond within "
                f"{PROBE_TIMEOUT_SECONDS}s or failed to run"
            )
            continue
        failure = _validate_handshake(verdict, sent)
        if failure is not None:
            reasons.append(f"{source} ({path}): {failure}")
            continue
        provenance = _git_head(checkout_root) if checkout_root is not None else None
        return CheckerHandle(path=path, source=source, provenance=provenance)

    return Unavailable(reason="; ".join(reasons))


_MEMO_LOCK = threading.Lock()
_UNSET = object()
_memoized_result: object = _UNSET


def resolve_checker(*, force: bool = False):
    """Resolve which independent checker (if any) is available, memoized for the process.

    Lazy: nothing is probed until this is first called -- importing this module performs no
    subprocess call. `force=True` re-probes, discarding any memoized result (a test-only escape
    hatch; production callers never need it since availability does not change within a
    process's lifetime).
    """
    global _memoized_result
    with _MEMO_LOCK:
        if _memoized_result is not _UNSET and not force:
            return _memoized_result
        _memoized_result = _resolve_uncached()
        return _memoized_result


def _reset_for_tests() -> None:
    """Test-only: clear the memoized resolution so the next `resolve_checker()` call
    re-probes. Never called by production code."""
    global _memoized_result
    with _MEMO_LOCK:
        _memoized_result = _UNSET


def check_certificate(payload: Dict[str, Any], timeout: float = CHECK_TIMEOUT_SECONDS) -> CheckOutcome:
    """Invoke the resolved checker on `payload` (a real certificate wire payload, e.g. from
    `WitnessFamily.to_json`), returning a `CheckOutcome`.

    Raises `ProtocolFailure` if the checker responds but its `echo` does not match the bytes
    sent -- see that exception's docstring for why this is not folded into `CheckOutcome`.
    """
    resolved = resolve_checker()
    if isinstance(resolved, Unavailable):
        return CheckOutcome(available=False, reason=resolved.reason)

    verdict, sent = _invoke(resolved.path, payload, timeout)
    if verdict is None:
        return CheckOutcome(
            available=False,
            reason=(
                f"{resolved.source} checker at {resolved.path} did not respond within "
                f"{timeout}s"
            ),
        )

    status = verdict.get("status")
    if status != "error":
        echo = verdict.get("echo")
        if echo is None or echo.strip() != sent.strip():
            raise ProtocolFailure(
                "checker echo does not match the bytes sent -- the two sides are talking "
                f"about different certificates. sent={sent!r} echo={echo!r} verdict={verdict!r}"
            )

    return CheckOutcome(available=True, verdict=verdict, sent=sent, checker=resolved)
