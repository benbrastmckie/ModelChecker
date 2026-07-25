"""Shared pytest configuration for the standalone oracle/ test tree.

Registration lives here rather than in an `oracle/pytest.ini` or
`oracle/pyproject.toml`: a conftest.py is loaded during collection independent
of pytest's rootdir/inifile resolution, so it registers marks for any
`oracle/`-rooted invocation without becoming the first-found inifile and
without perturbing rootdir semantics for the tree.

`differential` and `slow` are already declared in `code/pyproject.toml`, but
that file is a sibling of `oracle/`, not an ancestor -- pytest's ini-discovery
never reaches it when the invocation is rooted at `oracle/` (or at the repo
root, since the repo root itself has no ini file). Re-declaring them here
closes that ini-discovery gap.
"""

from __future__ import annotations

import pytest

# Node-id (function name, id-fragment) pairs that must run outside parallel
# workers. Matched by both the test function name and a substring of the
# parametrize id, so a bare id-fragment match cannot spill onto an unrelated
# parametrize site that happens to share a case name.
_XDIST_SERIAL_NODEID_FRAGMENTS = (
    ("test_enriched_vs_primitive_sat_agreement", "[some_past]"),
    ("test_regression_all_active_examples", "[BM_CM_1"),
)


def pytest_configure(config: pytest.Config) -> None:
    """Register custom marks used across the oracle/ suite.

    `differential` and `slow` mirror the descriptions in
    `code/pyproject.toml` so the two declarations do not drift.
    """
    config.addinivalue_line(
        "markers",
        "differential: Tests that compare MC oracle against reference oracles",
    )
    config.addinivalue_line(
        "markers",
        "slow: Tests that are computationally expensive and skipped in CI",
    )
    config.addinivalue_line(
        "markers",
        "xdist_serial: Tests whose Z3 solve budget has under ~2x headroom, "
        "which CPU contention under pytest-xdist can push past budget -- "
        "reported as no-countermodel rather than as an error (see "
        "code/docs/core/TESTING_GUIDE.md section 8.6). Run these in the "
        "serial pass of oracle/run-oracle-suite.sh, never under -n.",
    )


def pytest_collection_modifyitems(config: pytest.Config, items: list[pytest.Item]) -> None:
    """Apply `xdist_serial` to the parametrized cases that cannot be marked at
    the source without breaking the shared data structures they are built
    from (`ENRICHED_PRIMITIVE_PAIRS`'s `ids=` comprehensions and
    `regression_examples`'s `.items()` consumers -- see
    `code/docs/core/TESTING_GUIDE.md` section 8.6 for the underlying
    contention mechanism this mark exists to route around).
    """
    marker = pytest.mark.xdist_serial
    for item in items:
        for func_name, id_fragment in _XDIST_SERIAL_NODEID_FRAGMENTS:
            if func_name in item.nodeid and id_fragment in item.nodeid:
                item.add_marker(marker)
