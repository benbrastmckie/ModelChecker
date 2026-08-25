"""`.github/workflows/tests.yml` and `flake.nix` run textually identical pytest invocations
(parallel gating pass plus serial `xdist_serial` pass) under two different toolchains -- the
PyPI `z3-solver` wheel and the nixpkgs-native Z3/Python closure. This module makes that
"kept in sync" invariant executable instead of a comment a future edit can silently break.

**Extraction, deliberately regex-based for both files, not `yaml.safe_load` for `tests.yml`**:
`flake.nix` is not YAML and must be regex-extracted regardless; `tests.yml`'s "Run general test
suite" step is a plain multi-line shell string once parsed, so `yaml.safe_load` would only save
locating that one step -- and `PyYAML` is not an installed dependency in either CI toolchain
(`.github/workflows/tests.yml`'s "Install test dependencies" step installs
`z3-solver networkx pytest pytest-xdist pytest-timeout ipywidgets matplotlib typing-extensions`,
none of which requires it; `flake.nix`'s `devPython` package list carries no yaml-providing
package either). Adding a new CI dependency is out of this phase's scope, so both files are
parsed the same way: a targeted line regex matching the two `pytest ...` invocation lines,
mirroring how `flake.nix` had to be handled anyway.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
TESTS_YML = REPO_ROOT / ".github" / "workflows" / "tests.yml"
FLAKE_NIX = REPO_ROOT / "flake.nix"
PYPROJECT_TOML = REPO_ROOT / "code" / "pyproject.toml"

# flake.nix's checks.default derivation sets `src = ./code`, so the sandboxed `nix flake check`
# build only ever contains the code/ subtree -- .github/workflows/tests.yml and flake.nix itself,
# both outside code/, are structurally absent there (this module's own __file__ resolves to
# /build/code/tests/ci/..., i.e. REPO_ROOT resolves to /build, which has no .github/ or flake.nix
# under it). This guard's actual job -- catching a real divergence between the two files -- is
# still done: .github/workflows/tests.yml's own `general-tests` job checks out the FULL repo via
# actions/checkout@v4, so this guard runs there with both files present. Skip cleanly here rather
# than fail on an environment this guard cannot evaluate in.
_MISSING_REPO_ROOT_FILES = [p for p in (TESTS_YML, FLAKE_NIX) if not p.exists()]
if _MISSING_REPO_ROOT_FILES:
    pytest.skip(
        "Repo-root files not present in this sandbox (expected under `nix flake check`'s "
        "checks.default, whose `src = ./code` excludes the repo root): "
        + ", ".join(str(p) for p in _MISSING_REPO_ROOT_FILES)
        + ". This guard runs in .github/workflows/tests.yml's general-tests job instead, where "
        "actions/checkout@v4 provides the full repository.",
        allow_module_level=True,
    )

# Matches a `pytest <paths> ...` invocation line regardless of leading indentation. The two
# files order their path arguments differently (`tests/ src/model_checker` vs
# `src/model_checker tests`) -- that ordering is a pre-existing divergence outside this guard's
# declared scope (marker expression, `-n`, `--timeout`, `--timeout-method`), so the path
# arguments themselves are not asserted equal here.
_PYTEST_LINE_RE = re.compile(r'^[ \t]*pytest\s+\S+\s+\S+\s+-m\s+"[^"]*".*$', re.MULTILINE)
_MARKER_EXPR_RE = re.compile(r'-m\s+"([^"]*)"')
_N_WORKERS_RE = re.compile(r"(?<!\S)-n\s+(\d+)")
_TIMEOUT_RE = re.compile(r"--timeout=(\d+)")
_TIMEOUT_METHOD_RE = re.compile(r"--timeout-method=(\S+)")


class _Invocation:
    """One parsed `pytest ...` CI invocation line."""

    def __init__(self, source: str, line: str):
        self.source = source
        self.line = line
        m = _MARKER_EXPR_RE.search(line)
        assert m, f"{source}: could not find a -m \"...\" marker expression in: {line!r}"
        self.marker_expr = m.group(1)
        n_match = _N_WORKERS_RE.search(line)
        self.n_workers = n_match.group(1) if n_match else None
        timeout_match = _TIMEOUT_RE.search(line)
        assert timeout_match, f"{source}: no --timeout=<N> found in: {line!r}"
        self.timeout = timeout_match.group(1)
        method_match = _TIMEOUT_METHOD_RE.search(line)
        assert method_match, f"{source}: no --timeout-method=<X> found in: {line!r}"
        self.timeout_method = method_match.group(1)

    @property
    def is_parallel(self) -> bool:
        return self.n_workers is not None


def _extract_invocations(path: Path) -> list[_Invocation]:
    text = path.read_text()
    lines = _PYTEST_LINE_RE.findall(text)
    label = str(path.relative_to(REPO_ROOT))
    assert lines, f"{label}: no `pytest ...` invocation lines found -- extraction regex is stale"
    return [_Invocation(label, line) for line in lines]


@pytest.fixture(scope="module")
def tests_yml_invocations() -> list[_Invocation]:
    return _extract_invocations(TESTS_YML)


@pytest.fixture(scope="module")
def flake_nix_invocations() -> list[_Invocation]:
    return _extract_invocations(FLAKE_NIX)


def _split_parallel_serial(invocations: list[_Invocation], label: str) -> tuple[_Invocation, _Invocation]:
    parallel = [inv for inv in invocations if inv.is_parallel]
    serial = [inv for inv in invocations if not inv.is_parallel]
    assert len(parallel) == 1, f"{label}: expected exactly one parallel (`-n`) pass, found {len(parallel)}"
    assert len(serial) == 1, f"{label}: expected exactly one serial (no `-n`) pass, found {len(serial)}"
    return parallel[0], serial[0]


def test_parallel_pass_marker_expression_matches(tests_yml_invocations, flake_nix_invocations):
    yml_parallel, _ = _split_parallel_serial(tests_yml_invocations, "tests.yml")
    nix_parallel, _ = _split_parallel_serial(flake_nix_invocations, "flake.nix")
    assert yml_parallel.marker_expr == nix_parallel.marker_expr, (
        f"Parallel-pass marker expression diverged between {yml_parallel.source} "
        f"({yml_parallel.marker_expr!r}) and {nix_parallel.source} ({nix_parallel.marker_expr!r})"
    )


def test_serial_pass_marker_expression_matches(tests_yml_invocations, flake_nix_invocations):
    _, yml_serial = _split_parallel_serial(tests_yml_invocations, "tests.yml")
    _, nix_serial = _split_parallel_serial(flake_nix_invocations, "flake.nix")
    assert yml_serial.marker_expr == nix_serial.marker_expr, (
        f"Serial-pass marker expression diverged between {yml_serial.source} "
        f"({yml_serial.marker_expr!r}) and {nix_serial.source} ({nix_serial.marker_expr!r})"
    )


def test_worker_count_matches(tests_yml_invocations, flake_nix_invocations):
    yml_parallel, _ = _split_parallel_serial(tests_yml_invocations, "tests.yml")
    nix_parallel, _ = _split_parallel_serial(flake_nix_invocations, "flake.nix")
    assert yml_parallel.n_workers == nix_parallel.n_workers, (
        f"-n worker count diverged between {yml_parallel.source} ({yml_parallel.n_workers!r}) "
        f"and {nix_parallel.source} ({nix_parallel.n_workers!r})"
    )


def test_timeout_value_and_method_match(tests_yml_invocations, flake_nix_invocations):
    all_invocations = tests_yml_invocations + flake_nix_invocations
    timeouts = {(inv.source, inv.line): inv.timeout for inv in all_invocations}
    methods = {(inv.source, inv.line): inv.timeout_method for inv in all_invocations}
    distinct_timeouts = set(timeouts.values())
    distinct_methods = set(methods.values())
    assert len(distinct_timeouts) == 1, f"--timeout value is not identical across all invocations: {timeouts}"
    assert len(distinct_methods) == 1, f"--timeout-method value is not identical across all invocations: {methods}"


def _registered_markers() -> set[str]:
    text = PYPROJECT_TOML.read_text()
    markers_block = re.search(r"markers\s*=\s*\[(.*?)\n\]", text, re.DOTALL)
    assert markers_block, "code/pyproject.toml: could not find [tool.pytest.ini_options].markers array"
    names = set()
    for entry in re.findall(r'"([^"]+)"', markers_block.group(1)):
        name = entry.split(":", 1)[0].strip()
        names.add(name)
    assert names, "code/pyproject.toml: markers array parsed but yielded no marker names"
    return names


def test_every_ci_marker_is_registered(tests_yml_invocations, flake_nix_invocations):
    registered = _registered_markers()
    all_invocations = tests_yml_invocations + flake_nix_invocations
    for inv in all_invocations:
        tokens = {tok for tok in inv.marker_expr.split() if tok not in {"and", "or", "not"}}
        unregistered = tokens - registered
        assert not unregistered, (
            f"{inv.source}: marker expression {inv.marker_expr!r} references unregistered "
            f"marker(s) {sorted(unregistered)} -- a typo here would silently deselect nothing. "
            f"Registered markers: {sorted(registered)}"
        )
