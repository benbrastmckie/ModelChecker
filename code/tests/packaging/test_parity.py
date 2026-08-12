"""Wheel/sdist parity assertions for the packaging contract.

`pyproject.toml`'s `[tool.setuptools.package-data]` allowlist and `MANIFEST.in`'s sdist rules
each carry a comment asserting they stay in sync with each other. This module makes that
invariant executable.

**Parity, defined precisely** (this is the comparison set; nothing outside it is asserted):

1. Normalize each artifact to a comparable "package view" restricted to the `model_checker/`
   subtree:
   - Wheel members already use the installed layout, so the view is every member starting with
     `model_checker/`.
   - Sdist members (after `conftest.py`'s `normalize_sdist`, which already strips the leading
     `{name}-{version}/` component) still carry the `src/` source-layout prefix, so the view
     strips a further leading `src/` and restricts to `model_checker/`.
   - This restriction structurally excludes wheel `*.dist-info/*` (prefixed
     `model_checker-{version}.dist-info/`, no slash after `model_checker`) and sdist
     `*.egg-info/*` (prefixed `src/model_checker.egg-info/`, a dot not a slash after
     `model_checker`), plus sdist-only root metadata (`PKG-INFO`, `setup.py`, `setup.cfg`,
     `pyproject.toml`, `MANIFEST.in`, the root `README.md`, `LICENSE`) -- none of those paths
     start with `model_checker/` in the restricted view.
2. Within that restricted view, two sub-classes are compared for **set equality**:
   - **`.py` module paths**: every member ending in `.py`.
   - **Packaged data paths**: members named `README.md`, `CITATION.md`, or `LICENSE.md`
     (anywhere in the tree), plus `docs/*.md` and `notebooks/*.ipynb` members.

Everything else in the restricted view (e.g. other markdown files that happen to be swept in by
`include-package-data`) is out of scope for this parity assertion, even if it happens to also
match between the two artifacts.

**Recorded `docs/*.md` outcome** (resolves the plan's open question): building fresh and
inspecting the sdist directly shows `docs/*.md` already present in the sdist for every theory --
`include-package-data = true` auto-folds `[tool.setuptools.package-data]`'s `docs/*.md` entry
into the sdist's `SOURCES.txt`. `MANIFEST.in` is therefore left unchanged; there is no real
drift to fix, and adding a redundant `recursive-include` rule would be "fixing" a non-bug.
"""

from pathlib import PurePosixPath

import pytest

pytestmark = [pytest.mark.packaging, pytest.mark.slow]


def _wheel_package_view(members: frozenset) -> frozenset:
    return frozenset(p for p in members if p.startswith("model_checker/"))


def _sdist_package_view(members: frozenset) -> frozenset:
    """`members` is already normalize_sdist()-ed (leading `{name}-{version}/` stripped); this
    strips the further `src/` source-layout prefix and restricts to `model_checker/`."""
    view = set()
    for path in members:
        if path.startswith("src/model_checker/"):
            view.add(path[len("src/") :])
    return frozenset(view)


def _is_py_module(path: str) -> bool:
    return path.endswith(".py")


def _is_data_path(path: str) -> bool:
    name = PurePosixPath(path).name
    parent_name = PurePosixPath(path).parent.name
    if name in {"README.md", "CITATION.md", "LICENSE.md"}:
        return True
    if name.endswith(".md") and parent_name == "docs":
        return True
    if name.endswith(".ipynb") and parent_name == "notebooks":
        return True
    return False


def _symmetric_diff_message(label: str, wheel_only: set, sdist_only: set) -> str:
    return (
        f"{label} parity broken between wheel and sdist under model_checker/\n"
        f"  wheel-only ({len(wheel_only)}): {sorted(wheel_only)}\n"
        f"  sdist-only ({len(sdist_only)}): {sorted(sdist_only)}"
    )


@pytest.fixture(scope="session")
def wheel_package_view(wheel_member_set):
    return _wheel_package_view(wheel_member_set)


@pytest.fixture(scope="session")
def sdist_package_view(sdist_member_set):
    return _sdist_package_view(sdist_member_set)


def test_py_module_parity(wheel_package_view, sdist_package_view):
    wheel_py = {p for p in wheel_package_view if _is_py_module(p)}
    sdist_py = {p for p in sdist_package_view if _is_py_module(p)}
    wheel_only = wheel_py - sdist_py
    sdist_only = sdist_py - wheel_py
    assert wheel_py == sdist_py, _symmetric_diff_message(".py module", wheel_only, sdist_only)


def test_data_path_parity(wheel_package_view, sdist_package_view):
    wheel_data = {p for p in wheel_package_view if _is_data_path(p)}
    sdist_data = {p for p in sdist_package_view if _is_data_path(p)}
    wheel_only = wheel_data - sdist_data
    sdist_only = sdist_data - wheel_data
    assert wheel_data == sdist_data, _symmetric_diff_message(
        "packaged data", wheel_only, sdist_only
    )
