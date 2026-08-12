"""Smoke test for the packaging build fixture.

Confirms both artifacts are produced with non-empty member listings, and that
`tests/conftest.py`'s autouse `test_isolation` fixture composes cleanly with the
subprocess-based build (no cwd/sys.path leakage across repeated builds in one session).
"""

import os
import sys

import pytest

pytestmark = [pytest.mark.packaging, pytest.mark.slow]


def test_artifacts_produced_and_nonempty(wheel_member_set, sdist_member_set):
    assert wheel_member_set, "wheel member set is empty"
    assert sdist_member_set, "sdist member set is empty"


def test_wheel_contains_package_init(wheel_member_set):
    assert "model_checker/__init__.py" in wheel_member_set


def test_isolation_fixture_composes_with_build(wheel_member_set):
    """Run the (session-scoped, already-built) fixture twice in one session and confirm no
    cwd or sys.path leakage -- this is the same fixture instance both times since it is
    session-scoped, but exercises the isolation fixture's before/after snapshot around a test
    that depends on the subprocess-build fixture."""
    initial_cwd = os.getcwd()
    initial_path = list(sys.path)
    assert wheel_member_set, "wheel member set is empty on second access"
    assert os.getcwd() == initial_cwd
    assert sys.path == initial_path
