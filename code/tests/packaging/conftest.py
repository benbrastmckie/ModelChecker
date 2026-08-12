"""Shared fixtures for the packaging contract test suite.

Builds a fresh wheel and sdist from `code/` into a pytest temp directory (never reading the
stale `code/dist/`/`code/build/` directories that may exist from prior manual builds) and
exposes their member-path listings to the rest of `tests/packaging/`.

Toolchain provisioning has an ambient fast path (use `build` if already importable in the
current interpreter) and a venv fallback (provisioned with `PIP_USER=0` / `--no-user`, since
this host's `~/.config/pip/pip.conf` sets `install.user = true` globally, which a venv
rejects). Provisioning failure is `pytest.skip` (loud reason) when `CI` is unset, and
`pytest.fail` when `CI` is set -- packaging drift must never pass silently in CI.

**Build-cache correctness note**: `python -m build --no-isolation` invokes setuptools' legacy
`setup.py` commands (`build_py`, `egg_info`, `sdist`) *in place* against `code/`, and those
commands are incremental by default -- `build_py` only re-copies a data file if its source is
newer than the previously-copied destination, and `egg_info` can reuse an existing
`src/model_checker.egg-info/SOURCES.txt` without regenerating it. If `code/build/` or
`src/model_checker.egg-info/` already hold output from a prior (possibly much older) manual
build, "building fresh into a pytest temp dir" is not actually fresh: `--outdir` only redirects
the *final* wheel/sdist location, not these intermediate caches, so a build can silently ship
stale package-data that no longer matches the current `pyproject.toml`/`MANIFEST.in` -- this was
observed directly: with `docs/*.md` temporarily removed from `[tool.setuptools.package-data]`
during implementation, the wheel still contained every `docs/*.md` file until `code/build/` and
`src/model_checker.egg-info/` were removed first. `built_artifacts` below therefore deletes both
before every session build (and again afterward, so the repository is left as it found it) --
this is test-fixture hygiene for our own build's correctness, not the "clean up `code/dist/`
for the user" non-goal (see the plan's Non-Goals): `code/dist/` itself is never touched here,
since `--outdir` already keeps the build's actual output out of it.
"""

from __future__ import annotations

import functools
import os
import shutil
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

# Intermediate setuptools build-cache locations that must be cleared before every build to
# guarantee freshness -- see the build-cache correctness note above. Never `code/dist/`.
_STALE_BUILD_CACHE_PATHS = (
    CODE_ROOT / "build",
    CODE_ROOT / "src" / "model_checker.egg-info",
)


def _clear_stale_build_cache() -> None:
    for stale_path in _STALE_BUILD_CACHE_PATHS:
        shutil.rmtree(stale_path, ignore_errors=True)


def _provisioning_failure(reason: str) -> None:
    """Apply the CI-gated skip/fail policy: never a silent pass."""
    if os.environ.get("CI"):
        pytest.fail(reason)
    else:
        pytest.skip(reason)


@functools.lru_cache(maxsize=1)
def _nix_cxx_runtime_lib_dir() -> str:
    """Return the Nix C++ runtime library directory, or `""` when it does not apply.

    On a non-FHS host (NixOS), a pip-installed `z3-solver` wheel's bundled `libz3.so` cannot
    resolve `libstdc++.so.6` from inside an isolated venv, because the wheel's binaries are not
    `nix-ld`-patched and so search only FHS-standard paths that do not exist here. Pointing
    `LD_LIBRARY_PATH` at the Nix stdenv's C++ runtime resolves it -- the same recipe the release
    rehearsal established for verifying a published wheel on this platform.

    Returns `""` (and the caller then changes nothing) whenever this does not apply: no `nix` on
    PATH, the evaluation failing or timing out, or the resolved directory not existing. On a
    standard FHS Linux runner -- CI included -- there is no `nix` binary, so this is inert and
    the subprocess environment is left exactly as it was.
    """
    if not shutil.which("nix"):
        return ""
    try:
        result = subprocess.run(
            ["nix", "eval", "--raw", "nixpkgs#stdenv.cc.cc.lib"],
            capture_output=True,
            text=True,
            timeout=180,
        )
    except (OSError, subprocess.SubprocessError):  # pragma: no cover -- host-dependent
        return ""
    if result.returncode != 0:  # pragma: no cover -- host-dependent
        return ""
    lib_dir = Path(result.stdout.strip()) / "lib"
    return str(lib_dir) if lib_dir.is_dir() else ""


def _add_cxx_runtime_to_env(env: Dict[str, str]) -> Dict[str, str]:
    """Prepend the Nix C++ runtime dir to `LD_LIBRARY_PATH` in `env`, when it applies.

    Mutates and returns `env`. A no-op wherever `_nix_cxx_runtime_lib_dir()` returns `""`.
    """
    lib_dir = _nix_cxx_runtime_lib_dir()
    if not lib_dir:
        return env
    existing = env.get("LD_LIBRARY_PATH", "")
    env["LD_LIBRARY_PATH"] = f"{lib_dir}:{existing}" if existing else lib_dir
    return env


def handle_known_venv_libz3_link_failure(result: subprocess.CompletedProcess) -> None:
    """Apply the same CI-gated skip/fail policy as `_provisioning_failure`, but only for one
    specific, identified failure signature: the isolated packaging-test venv's pip-installed
    `z3-solver` wheel failing to locate its own bundled `libz3.so`/`libstdc++.so.6` at runtime.

    Observed directly on this project's NixOS development environment: `z3-solver` installs
    successfully via pip into the venv (no install-time error), but any subprocess invocation
    that actually imports `z3` fails with `Z3Exception("libz3.%s not found." % _ext)`, because
    the wheel's bundled shared libraries expect an FHS-standard library search path that Nix's
    non-FHS layout does not provide outside of `nix-ld`-patched binaries (which pip-installed
    wheels are not). The *ambient*, non-isolated interpreter has no such problem, because its
    `z3` package resolves through the Nix store with correctly wired RPATHs -- this is
    exclusively an isolated-venv dynamic-linking limitation of the current host, not a
    model_checker code defect, so it is handled with the same provisioning-failure policy
    `packaging_toolchain`/`built_artifacts` already use: skip outside CI (a dev-machine
    limitation), fail loudly in CI (where a standard Linux runner should not hit this).

    **This is now a backstop, not the expected path.** `installed_venv` prepends the Nix C++
    runtime directory to `LD_LIBRARY_PATH` (see `_add_cxx_runtime_to_env`), which resolves the
    signature described above at its source, so these tests execute rather than skip on this
    platform. This handler remains for any host where that repair does not apply -- some other
    non-FHS layout, or a `nix eval` that cannot run -- so such a host still degrades to a
    loud, reason-carrying skip instead of an unexplained failure.

    Any other failure is left completely untouched -- this function only recognizes this one
    exact signature and returns silently (no skip, no fail) for everything else, so real defects
    are never masked by it.
    """
    combined = (result.stdout or "") + (result.stderr or "")
    if "libz3.so not found" in combined or "libz3.so: cannot open shared object file" in combined:
        _provisioning_failure(
            "Isolated packaging-test venv's pip-installed z3-solver cannot locate its bundled "
            "libz3.so/libstdc++.so.6 in this environment (observed on NixOS, where pip-installed "
            "binary wheels expect FHS-standard library paths that only nix-ld-patched binaries "
            "get) -- a dev-machine dynamic-linking limitation of the isolated venv, not a "
            "model_checker defect. The identical z3 package works via the ambient interpreter."
        )


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

    Never writes into `code/dist/` (the build's actual output always lands in a pytest temp dir
    via `--outdir`) and clears `code/build/`/`src/model_checker.egg-info/` immediately before
    (and after) the build -- see the build-cache correctness note in this module's docstring for
    why that is required for the build to be genuinely fresh. The build runs with an explicit
    `cwd=` (never `os.chdir`) so it composes cleanly with `tests/conftest.py`'s autouse
    `test_isolation` fixture.
    """
    outdir = tmp_path_factory.mktemp("pkgdist")
    _clear_stale_build_cache()
    try:
        result = subprocess.run(
            [packaging_toolchain, "-m", "build", "--no-isolation", "--outdir", str(outdir)],
            cwd=str(CODE_ROOT),
            capture_output=True,
            text=True,
        )
    finally:
        _clear_stale_build_cache()
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


# --- Real console-script harness --------------------------------------------------------------
#
# Relocated from test_entry_point.py so it is shareable across the whole packaging test
# directory -- pytest fixture visibility is directory-scoped, and a fixture defined inside a
# single test module cannot be consumed by a sibling module. Moving it here, alongside
# packaging_toolchain/built_artifacts, avoids building a second venv harness for the same
# purpose (see the CLI end-to-end verification suite's research report and plan for why that is
# required).


def _venv_bin_dir(venv_dir: Path) -> Path:
    bin_dir = venv_dir / "bin"
    if not bin_dir.is_dir():
        bin_dir = venv_dir / "Scripts"  # pragma: no cover -- Windows path
    return bin_dir


@pytest.fixture(scope="session")
def installed_venv(built_artifacts: Dict[str, Path], tmp_path_factory: pytest.TempPathFactory) -> Dict[str, object]:
    """Create a fresh venv under a pytest temp dir and install the built wheel into it.

    Session-scoped: the venv is built exactly once per test session and shared by every test
    in `tests/packaging/` that requests it (directly or transitively).
    """
    import venv

    venv_dir = tmp_path_factory.mktemp("pkgentryvenv")
    try:
        venv.EnvBuilder(with_pip=True).create(venv_dir)
    except Exception as exc:  # pragma: no cover -- environment-dependent failure path
        _provisioning_failure(f"Failed to create entry-point venv at {venv_dir}: {exc}")
        raise RuntimeError("unreachable")  # pragma: no cover

    bin_dir = _venv_bin_dir(venv_dir)
    interp = bin_dir / ("python.exe" if os.name == "nt" else "python")

    # Strip PYTHONPATH: the outer test invocation typically runs with PYTHONPATH=src (per
    # project convention) so that the source tree resolves on sys.path -- inherited verbatim
    # into this subprocess, that would make pip's "already satisfied" check see model_checker
    # as already importable via the source tree and skip (re)installing the wheel, silently
    # leaving the console script uninstalled. This venv must resolve model_checker from its own
    # site-packages only.
    env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}
    env["PIP_USER"] = "0"
    # Make the venv's pip-installed `z3-solver` able to resolve its own bundled shared
    # libraries on a non-FHS host. Inert on a standard FHS Linux runner (CI included). This is
    # set before the install so the single returned `env` covers both provisioning and every
    # later console-script/`python -m` invocation that consumes `installed_venv["env"]`.
    _add_cxx_runtime_to_env(env)
    result = subprocess.run(
        [str(interp), "-m", "pip", "install", "--no-user", str(built_artifacts["wheel"])],
        env=env,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        _provisioning_failure(
            f"Failed to install built wheel into venv (exit {result.returncode}):\n"
            f"{result.stderr[-2000:]}"
        )
        raise RuntimeError("unreachable")  # pragma: no cover

    return {"venv_dir": venv_dir, "bin_dir": bin_dir, "python": interp, "env": env}


def _console_script_path(installed_venv: Dict[str, object]) -> Path:
    """Return the path to the installed `model-checker` console script.

    Importable helper (not itself a fixture) so callers can compose it with `installed_venv`
    directly, per this phase's requirement that it be usable from later console-script and
    generate-then-execute test files.
    """
    script_name = "model-checker.exe" if os.name == "nt" else "model-checker"
    return installed_venv["bin_dir"] / script_name
