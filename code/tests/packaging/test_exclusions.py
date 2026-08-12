"""Exclusion assertions for the packaging contract.

Mirrors `MANIFEST.in`'s `prune`/`global-exclude` rules and the exclusion-related comments in
`pyproject.toml`'s `[tool.setuptools.package-data]` block: none of the six named path classes
may appear in either the wheel or the (normalized) sdist. Each class is a separately named,
separately failing test, parametrized over both artifacts so a failure names both the exclusion
class and the artifact it was found in, with the offending member paths listed in the failure
message for CI-log diagnosability.
"""

from pathlib import PurePosixPath

import pytest

pytestmark = [pytest.mark.packaging, pytest.mark.slow]


def _has_path_component(path: str, component: str) -> bool:
    return component in PurePosixPath(path).parts


def _is_named(path: str, name: str) -> bool:
    return PurePosixPath(path).name == name


def _under_theory_lib_subdir(path: str, subdir: str) -> bool:
    """True if `path` matches `.../theory_lib/<any-theory>/<subdir>/...`, mirroring
    MANIFEST.in's `prune */theory_lib/*/{subdir}` rule (single wildcard level between
    `theory_lib` and the excluded subdirectory)."""
    parts = PurePosixPath(path).parts
    for i in range(len(parts) - 2):
        if parts[i] == "theory_lib" and parts[i + 2] == subdir:
            return True
    return False


def _is_pycache_or_pyc(path: str) -> bool:
    return _has_path_component(path, "__pycache__") or path.endswith(".pyc")


# Module-level table: each entry is a separately named, separately failing exclusion class.
# Mirrors the six classes named in the task description and in MANIFEST.in's
# prune/global-exclude lines.
EXCLUSION_CLASSES = {
    "oracle": lambda p: _has_path_component(p, "oracle"),
    "TODO.md": lambda p: _is_named(p, "TODO.md"),
    "theory_lib/*/history": lambda p: _under_theory_lib_subdir(p, "history"),
    "theory_lib/*/reports": lambda p: _under_theory_lib_subdir(p, "reports"),
    "theory_lib/*/examples_refactored": lambda p: _under_theory_lib_subdir(
        p, "examples_refactored"
    ),
    "__pycache__/*.pyc": _is_pycache_or_pyc,
}


@pytest.fixture(params=["wheel", "sdist"])
def artifact_members(request, wheel_member_set, sdist_member_set):
    """Yield (artifact_name, member_set) for both the wheel and the normalized sdist, so every
    exclusion-class test below runs once per artifact."""
    if request.param == "wheel":
        return "wheel", wheel_member_set
    return "sdist", sdist_member_set


@pytest.mark.parametrize("exclusion_name", list(EXCLUSION_CLASSES))
def test_exclusion_class_absent(exclusion_name, artifact_members):
    artifact_name, members = artifact_members
    predicate = EXCLUSION_CLASSES[exclusion_name]
    offenders = sorted(path for path in members if predicate(path))
    assert not offenders, (
        f"exclusion class {exclusion_name!r} unexpectedly present in the {artifact_name}: "
        f"{offenders}"
    )
