"""Shared fixtures for the packaging contract test suite.

Builds a fresh wheel and sdist from `code/` into a pytest temp directory (never reading the
stale `code/dist/`/`code/build/` directories that may exist from prior manual builds) and
exposes their member-path listings to the rest of `tests/packaging/`.

Toolchain provisioning has an ambient fast path (use `build` if already importable in the
current interpreter) and a venv fallback (provisioned with `PIP_USER=0` / `--no-user`, since
this host's `~/.config/pip/pip.conf` sets `install.user = true` globally, which a venv
rejects). Provisioning failure is `pytest.skip` (loud reason) when `CI` is unset, and
`pytest.fail` when `CI` is set -- packaging drift must never pass silently in CI.
"""

from __future__ import annotations

import os
import subprocess
import sys
import tarfile
import venv
import zipfile
from pathlib import Path
from typing import Dict

import pytest

# code/ -- three parents up from this file (code/tests/packaging/conftest.py).
CODE_ROOT = Path(__file__).resolve().parent.parent.parent


def _provisioning_failure(reason: str) -> None:
    """Apply the CI-gated skip/fail policy: never a silent pass."""
    if os.environ.get("CI"):
        pytest.fail(reason)
    else:
        pytest.skip(reason)


@pytest.fixture(scope="session")
def packaging_toolchain(tmp_path_factory: pytest.TempPathFactory) -> str:
    """Return the path to a Python interpreter with `build` importable.

    Fast path: if `build` is importable in the ambient interpreter, use it directly (no venv
    provisioning, no network). Otherwise provision an isolated venv and install `build` into it.
    """
    try:
        import build  # noqa: F401

        return sys.executable
    except ImportError:
        pass

    venv_dir = tmp_path_factory.mktemp("pkgvenv")
    try:
        venv.EnvBuilder(with_pip=True).create(venv_dir)
    except Exception as exc:  # pragma: no cover -- environment-dependent failure path
        _provisioning_failure(f"Failed to create packaging-test venv at {venv_dir}: {exc}")
        raise  # unreachable when CI unset (skip raises above); satisfies type checkers

    interp = venv_dir / "bin" / "python"
    if not interp.exists():
        interp = venv_dir / "Scripts" / "python.exe"  # pragma: no cover -- Windows path

    env = dict(os.environ)
    env["PIP_USER"] = "0"
    result = subprocess.run(
        [str(interp), "-m", "pip", "install", "--no-user", "build", "setuptools", "wheel"],
        env=env,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        _provisioning_failure(
            "Failed to install build toolchain into packaging-test venv "
            f"(exit {result.returncode}):\n{result.stderr[-2000:]}"
        )
        raise RuntimeError("unreachable")  # pragma: no cover

    return str(interp)


@pytest.fixture(scope="session")
def built_artifacts(
    packaging_toolchain: str, tmp_path_factory: pytest.TempPathFactory
) -> Dict[str, Path]:
    """Build a fresh wheel and sdist from `code/` into a pytest temp directory.

    Never touches `code/dist/` or `code/build/`, which may hold stale artifacts from prior
    manual builds -- the build runs with an explicit `cwd=` (never `os.chdir`) so it composes
    cleanly with `tests/conftest.py`'s autouse `test_isolation` fixture.
    """
    outdir = tmp_path_factory.mktemp("pkgdist")
    result = subprocess.run(
        [packaging_toolchain, "-m", "build", "--no-isolation", "--outdir", str(outdir)],
        cwd=str(CODE_ROOT),
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, (
        f"build failed (exit {result.returncode}) in {CODE_ROOT}:\n"
        f"STDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
    )

    wheels = sorted(outdir.glob("*.whl"))
    sdists = sorted(outdir.glob("*.tar.gz"))
    assert len(wheels) == 1, f"expected exactly one wheel in {outdir}, found {wheels}"
    assert len(sdists) == 1, f"expected exactly one sdist in {outdir}, found {sdists}"

    return {"wheel": wheels[0], "sdist": sdists[0]}


def wheel_members(whl: Path) -> frozenset:
    """Return the frozenset of member paths inside a wheel (a zip archive)."""
    with zipfile.ZipFile(whl) as zf:
        return frozenset(zf.namelist())


def sdist_members(tgz: Path) -> frozenset:
    """Return the frozenset of member paths inside a sdist (a gzipped tarball)."""
    with tarfile.open(tgz) as tf:
        return frozenset(tf.getnames())


def normalize_sdist(members: frozenset) -> frozenset:
    """Strip the leading `{name}-{version}/` path component from sdist member paths."""
    normalized = set()
    for member in members:
        _, sep, rest = member.partition("/")
        if sep:
            normalized.add(rest)
        # else: the bare top-level directory entry itself (no rest) -- drop it, not a real path.
    return frozenset(normalized)


@pytest.fixture(scope="session")
def wheel_member_set(built_artifacts: Dict[str, Path]) -> frozenset:
    """Session-scoped member-path listing of the built wheel."""
    return wheel_members(built_artifacts["wheel"])


@pytest.fixture(scope="session")
def sdist_member_set(built_artifacts: Dict[str, Path]) -> frozenset:
    """Session-scoped, normalized (leading `{name}-{version}/` stripped) member-path listing
    of the built sdist."""
    return normalize_sdist(sdist_members(built_artifacts["sdist"]))
