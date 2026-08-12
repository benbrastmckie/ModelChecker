"""Registry-driven inclusion assertions for the packaging contract.

Every registered theory (driven off `registry.get_registered()`, never a hardcoded literal or
count) must ship its `theory_lib/docs/THEORY_ARCHITECTURE.md`-contract metadata, docs, and
notebooks in both the wheel and the sdist. Docs assertions use **minimum-set** semantics: the
six canonical `docs/*.md` files must be present, but extras (e.g. exclusion's `docs/DATA.md`)
are tolerated and must not fail this suite.
"""

from pathlib import Path

import pytest

from model_checker import registry

pytestmark = [pytest.mark.packaging, pytest.mark.slow]

# The registry is the single source of truth -- never hardcode theory names or counts here.
AVAILABLE_THEORIES = registry.get_registered()

# code/ -- three parents up from this file (code/tests/packaging/test_inclusions.py).
CODE_ROOT = Path(__file__).resolve().parent.parent.parent

# Sourced from theory_lib/docs/THEORY_ARCHITECTURE.md's Theory Contract.
REQUIRED_ROOT_FILES = ["README.md", "CITATION.md", "LICENSE.md", "VERSION"]
REQUIRED_DOCS_FILES = [
    "README.md",
    "API_REFERENCE.md",
    "ARCHITECTURE.md",
    "ITERATE.md",
    "SETTINGS.md",
    "USER_GUIDE.md",
]

# The wheel and (normalized) sdist package the theory_lib tree under different path prefixes:
# the wheel is the installed package layout (`model_checker/...`), while the sdist retains the
# `src/` source layout (`src/model_checker/...`) since `package-dir = {"" = "src"}`.
ARTIFACT_PREFIXES = {"wheel": "model_checker", "sdist": "src/model_checker"}


@pytest.fixture(params=["wheel", "sdist"])
def artifact(request, wheel_member_set, sdist_member_set):
    """Yield (artifact_name, path_prefix, member_set) for both the wheel and the normalized
    sdist, so every inclusion test below runs once per artifact."""
    name = request.param
    members = wheel_member_set if name == "wheel" else sdist_member_set
    return name, ARTIFACT_PREFIXES[name], members


@pytest.mark.parametrize("theory", AVAILABLE_THEORIES)
@pytest.mark.parametrize("filename", REQUIRED_ROOT_FILES)
def test_root_metadata_file_present(theory, filename, artifact):
    artifact_name, prefix, members = artifact
    expected = f"{prefix}/theory_lib/{theory}/{filename}"
    assert expected in members, (
        f"{expected!r} missing from the {artifact_name} for theory {theory!r}"
    )


@pytest.mark.parametrize("theory", AVAILABLE_THEORIES)
@pytest.mark.parametrize("filename", REQUIRED_DOCS_FILES)
def test_docs_file_present(theory, filename, artifact):
    """Minimum-set semantics: only the six canonical docs files are asserted present. Extras
    (e.g. exclusion's docs/DATA.md) are not asserted against and never fail this test."""
    artifact_name, prefix, members = artifact
    expected = f"{prefix}/theory_lib/{theory}/docs/{filename}"
    assert expected in members, (
        f"{expected!r} missing from the {artifact_name} for theory {theory!r}"
    )


def _on_disk_notebooks(theory: str):
    notebooks_dir = CODE_ROOT / "src" / "model_checker" / "theory_lib" / theory / "notebooks"
    if not notebooks_dir.is_dir():
        return []
    return sorted(p.name for p in notebooks_dir.glob("*.ipynb"))


@pytest.mark.parametrize("theory", AVAILABLE_THEORIES)
def test_notebooks_present_where_on_disk(theory, artifact):
    """A theory with no on-disk `notebooks/` directory yields no assertions here -- this is
    conditional coverage, not a per-theory requirement."""
    artifact_name, prefix, members = artifact
    notebooks = _on_disk_notebooks(theory)
    if not notebooks:
        pytest.skip(f"theory {theory!r} has no on-disk notebooks/ directory")

    for notebook in notebooks:
        expected = f"{prefix}/theory_lib/{theory}/notebooks/{notebook}"
        assert expected in members, (
            f"{expected!r} missing from the {artifact_name} for theory {theory!r}"
        )
