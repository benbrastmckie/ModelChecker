"""Contract tests for the `installed_venv` install-source selector and version resolution.

Pins the env-var contract (D1) and both version-resolution paths (D2) from
`specs/168_pypi_install_and_full_cli_verification_ci/plans/01_pypi-install-verification-pipeline.md`
against the pure helper functions `conftest.py` exposes -- no venv, no network, no subprocess.
Every case that would otherwise touch `os.environ` uses `monkeypatch.setenv`/`delenv` so no test
leaks state into another. The `latest` version-resolution path is asserted through a
`monkeypatch.setattr`'d stand-in for the JSON-API lookup function -- this module never performs
a live network call.
"""

from __future__ import annotations

import pytest

from .conftest import (
    MODEL_CHECKER_PACKAGING_INSTALL_SOURCE,
    MODEL_CHECKER_PACKAGING_INSTALL_VERSION,
    _pip_install_args,
    _pypi_json_api_url,
    _resolve_install_source,
    _resolve_install_version,
)
from . import conftest as packaging_conftest

pytestmark = pytest.mark.packaging


# --- _resolve_install_source() --------------------------------------------------------------


def test_resolve_install_source_defaults_to_local_when_unset(monkeypatch):
    monkeypatch.delenv(MODEL_CHECKER_PACKAGING_INSTALL_SOURCE, raising=False)
    assert _resolve_install_source() == "local"


@pytest.mark.parametrize("source", ["local", "testpypi", "pypi"])
def test_resolve_install_source_passes_through_each_valid_value(monkeypatch, source):
    monkeypatch.setenv(MODEL_CHECKER_PACKAGING_INSTALL_SOURCE, source)
    assert _resolve_install_source() == source


def test_resolve_install_source_fails_loudly_on_unrecognized_value(monkeypatch):
    monkeypatch.setenv(MODEL_CHECKER_PACKAGING_INSTALL_SOURCE, "not-a-real-source")
    with pytest.raises(pytest.fail.Exception) as exc_info:
        _resolve_install_source()
    assert "not-a-real-source" in str(exc_info.value)


# --- _resolve_install_version(source) -------------------------------------------------------


def test_resolve_install_version_defaults_to_pyproject_version_when_unset(monkeypatch):
    monkeypatch.delenv(MODEL_CHECKER_PACKAGING_INSTALL_VERSION, raising=False)
    resolved = _resolve_install_version("local")
    assert resolved == packaging_conftest._pyproject_version()


def test_resolve_install_version_uses_explicit_literal_with_no_network_call(monkeypatch):
    def _fail_if_called(source):
        raise AssertionError("_latest_published_version must not be called for an explicit literal")

    monkeypatch.setattr(packaging_conftest, "_latest_published_version", _fail_if_called)
    monkeypatch.setenv(MODEL_CHECKER_PACKAGING_INSTALL_VERSION, "1.2.3")
    assert _resolve_install_version("pypi") == "1.2.3"


def test_resolve_install_version_latest_delegates_to_json_api_lookup(monkeypatch):
    calls = []

    def _fake_latest(source):
        calls.append(source)
        return "9.9.9"

    monkeypatch.setattr(packaging_conftest, "_latest_published_version", _fake_latest)
    monkeypatch.setenv(MODEL_CHECKER_PACKAGING_INSTALL_VERSION, "latest")
    assert _resolve_install_version("testpypi") == "9.9.9"
    assert calls == ["testpypi"]


# --- _pypi_json_api_url(source) -------------------------------------------------------------


def test_pypi_json_api_url_for_pypi():
    assert _pypi_json_api_url("pypi") == "https://pypi.org/pypi/model-checker/json"


def test_pypi_json_api_url_for_testpypi():
    assert _pypi_json_api_url("testpypi") == "https://test.pypi.org/pypi/model-checker/json"


# --- _pip_install_args(source, version, wheel_path) -----------------------------------------


def test_pip_install_args_local_uses_wheel_path_form(tmp_path):
    wheel_path = tmp_path / "model_checker-1.3.7-py3-none-any.whl"
    wheel_path.touch()
    args = _pip_install_args("local", "1.3.7", wheel_path=wheel_path)
    assert args == [str(wheel_path)]


def test_pip_install_args_testpypi_uses_both_index_urls_and_exact_pin():
    args = _pip_install_args("testpypi", "1.3.7")
    assert "--index-url" in args
    assert "https://test.pypi.org/simple/" in args
    assert "--extra-index-url" in args
    assert "https://pypi.org/simple/" in args
    assert "model-checker==1.3.7" in args


def test_pip_install_args_pypi_uses_default_index_and_exact_pin():
    args = _pip_install_args("pypi", "1.3.7")
    assert "--index-url" not in args
    assert "--extra-index-url" not in args
    assert "model-checker==1.3.7" in args
