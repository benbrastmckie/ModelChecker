"""Unit tests for `semantic/checker.py`, the production-side independent checker resolver
(item 1's precondition -- see `docs/TRUST_PIPELINE.md`'s remaining-work table).

Every test controls the module's own memoization explicitly via `_reset_for_tests()` and
monkeypatches `_invoke` (never real `subprocess.run`) so these tests need no BimodalLogic
checkout or `lake` -- unlike `tests/_lean_check.py`'s differential tests, this suite must pass
in an environment with no checker at all.
"""

from __future__ import annotations

import os
import time

import pytest

from model_checker.theory_lib.bimodal.semantic import checker as checker_module
from model_checker.theory_lib.bimodal.semantic.checker import (
    CheckerHandle,
    ProtocolFailure,
    Unavailable,
    check_certificate,
    resolve_checker,
)


@pytest.fixture(autouse=True)
def _clean_environment(monkeypatch, tmp_path):
    """Every test starts from a clean slate: no checker-related environment variable set, a
    memoized resolution reset, and a cache directory redirected into `tmp_path` so a real
    developer machine's `~/.cache` (or `~/Projects/BimodalLogic`) never leaks into a test."""
    monkeypatch.delenv("BIMODAL_CHECKER_BIN", raising=False)
    # Deliberately set (never delenv) to a nonexistent path: the resolver falls back to
    # ~/Projects/BimodalLogic when this variable is unset, and a real checkout may exist there
    # on the machine running these tests (or in CI). Pointing at a nonexistent path keeps every
    # test deterministic regardless of what else is checked out on disk.
    monkeypatch.setenv("BIMODAL_LOGIC_PATH", str(tmp_path / "no_such_bimodal_logic_checkout"))
    monkeypatch.delenv("BIMODAL_CHECKER_SHA256", raising=False)
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    checker_module._reset_for_tests()
    yield
    checker_module._reset_for_tests()


def _fake_probe_verdict(sent: str, *, acceptance="entailment", status="countermodel", echo=True):
    verdict = {"status": status}
    if status == "countermodel":
        verdict["time"] = 0
        if acceptance is not None:
            verdict["acceptance"] = acceptance
    if echo:
        verdict["echo"] = sent
    return verdict


class TestResolutionOrder:
    def test_no_candidate_configured_yields_unavailable_with_a_named_reason(self):
        result = resolve_checker()
        assert isinstance(result, Unavailable)
        assert "no checker candidate configured" in result.reason
        assert str(checker_module.cache_dir() / checker_module.CACHE_BINARY_NAME) in result.reason

    def test_explicit_binary_path_is_preferred_when_it_resolves(self, tmp_path, monkeypatch):
        explicit = tmp_path / "explicit_binary"
        explicit.write_text("#!/bin/sh\n")
        explicit.chmod(0o755)
        monkeypatch.setenv("BIMODAL_CHECKER_BIN", str(explicit))

        def fake_invoke(binary, payload, timeout):
            sent = checker_module.canonical_wire_bytes(payload)
            return _fake_probe_verdict(sent), sent

        monkeypatch.setattr(checker_module, "_invoke", fake_invoke)
        result = resolve_checker()
        assert isinstance(result, CheckerHandle)
        assert result.source == "explicit"
        assert result.path == explicit

    def test_cache_binary_used_when_no_explicit_path_is_set(self, tmp_path, monkeypatch):
        cache_binary = checker_module.cache_dir() / checker_module.CACHE_BINARY_NAME
        cache_binary.parent.mkdir(parents=True, exist_ok=True)
        cache_binary.write_text("#!/bin/sh\n")
        cache_binary.chmod(0o755)

        def fake_invoke(binary, payload, timeout):
            sent = checker_module.canonical_wire_bytes(payload)
            return _fake_probe_verdict(sent), sent

        monkeypatch.setattr(checker_module, "_invoke", fake_invoke)
        result = resolve_checker()
        assert isinstance(result, CheckerHandle)
        assert result.source == "cache"
        assert result.path == cache_binary

    def test_checkout_binary_used_last_and_records_provenance(self, tmp_path, monkeypatch):
        checkout = tmp_path / "BimodalLogic"
        (checkout / ".lake" / "build" / "bin").mkdir(parents=True)
        (checkout / "lakefile.toml").write_text("")
        binary = checkout / ".lake" / "build" / "bin" / "check_certificate"
        binary.write_text("#!/bin/sh\n")
        binary.chmod(0o755)
        monkeypatch.setenv("BIMODAL_LOGIC_PATH", str(checkout))

        def fake_invoke(binary_path, payload, timeout):
            sent = checker_module.canonical_wire_bytes(payload)
            return _fake_probe_verdict(sent), sent

        monkeypatch.setattr(checker_module, "_invoke", fake_invoke)
        monkeypatch.setattr(checker_module, "_git_head", lambda root: "deadbeef")
        result = resolve_checker()
        assert isinstance(result, CheckerHandle)
        assert result.source == "checkout"
        assert result.path == binary
        assert result.provenance == "deadbeef"

    def test_absent_checker_yields_unavailable_rather_than_raising(self, tmp_path, monkeypatch):
        monkeypatch.setenv("BIMODAL_CHECKER_BIN", str(tmp_path / "does_not_exist"))
        result = resolve_checker()
        assert isinstance(result, Unavailable)
        assert "no such file" in result.reason


class TestLazyBoundedMemoizedProbe:
    def test_probe_runs_at_most_once_per_process(self, tmp_path, monkeypatch):
        explicit = tmp_path / "explicit_binary"
        explicit.write_text("#!/bin/sh\n")
        monkeypatch.setenv("BIMODAL_CHECKER_BIN", str(explicit))

        call_count = {"n": 0}

        def counting_invoke(binary, payload, timeout):
            call_count["n"] += 1
            sent = checker_module.canonical_wire_bytes(payload)
            return _fake_probe_verdict(sent), sent

        monkeypatch.setattr(checker_module, "_invoke", counting_invoke)
        resolve_checker()
        resolve_checker()
        resolve_checker()
        assert call_count["n"] == 1

    def test_import_performs_no_subprocess_call(self):
        """Importing the module must not probe -- resolution is lazy. Run in a subprocess
        (never `importlib.reload`, which would redefine `Unavailable`/`CheckerHandle` as new
        class objects, breaking every subsequent `isinstance` check in this same test
        session)."""
        import subprocess
        import sys

        code = (
            "import time\n"
            "t = time.time()\n"
            "import model_checker.theory_lib.bimodal.semantic.checker as m\n"
            "elapsed = time.time() - t\n"
            "assert m._memoized_result is m._UNSET, 'import must not resolve eagerly'\n"
            "assert elapsed < 1.0, elapsed\n"
        )
        result = subprocess.run(
            [sys.executable, "-c", code], capture_output=True, text=True, timeout=15
        )
        assert result.returncode == 0, result.stdout + result.stderr

    @pytest.mark.xdist_serial
    def test_probe_timeout_yields_unavailable_not_a_hang(self, tmp_path, monkeypatch):
        explicit = tmp_path / "explicit_binary"
        explicit.write_text("#!/bin/sh\n")
        monkeypatch.setenv("BIMODAL_CHECKER_BIN", str(explicit))

        def timing_out_invoke(binary, payload, timeout):
            return None, checker_module.canonical_wire_bytes(payload)

        monkeypatch.setattr(checker_module, "_invoke", timing_out_invoke)
        start = time.time()
        result = resolve_checker()
        elapsed = time.time() - start
        assert isinstance(result, Unavailable)
        assert "did not respond" in result.reason
        assert elapsed < 1.0  # the fake never actually sleeps; this guards against a real hang


class TestCapabilityHandshake:
    def _configure_explicit(self, tmp_path, monkeypatch):
        explicit = tmp_path / "explicit_binary"
        explicit.write_text("#!/bin/sh\n")
        monkeypatch.setenv("BIMODAL_CHECKER_BIN", str(explicit))
        return explicit

    def test_missing_acceptance_field_is_a_capability_failure(self, tmp_path, monkeypatch):
        self._configure_explicit(tmp_path, monkeypatch)

        def fake_invoke(binary, payload, timeout):
            sent = checker_module.canonical_wire_bytes(payload)
            return _fake_probe_verdict(sent, acceptance=None), sent

        monkeypatch.setattr(checker_module, "_invoke", fake_invoke)
        result = resolve_checker()
        assert isinstance(result, Unavailable)
        assert "capability failure" in result.reason
        assert "acceptance" in result.reason

    def test_unrecognized_acceptance_value_is_a_capability_failure_naming_the_value(
        self, tmp_path, monkeypatch
    ):
        self._configure_explicit(tmp_path, monkeypatch)

        def fake_invoke(binary, payload, timeout):
            sent = checker_module.canonical_wire_bytes(payload)
            return _fake_probe_verdict(sent, acceptance="kernel_checked"), sent

        monkeypatch.setattr(checker_module, "_invoke", fake_invoke)
        result = resolve_checker()
        assert isinstance(result, Unavailable)
        assert "capability failure" in result.reason
        assert "kernel_checked" in result.reason

    def test_echo_mismatch_on_probe_is_a_protocol_failure(self, tmp_path, monkeypatch):
        self._configure_explicit(tmp_path, monkeypatch)

        def fake_invoke(binary, payload, timeout):
            sent = checker_module.canonical_wire_bytes(payload)
            verdict = _fake_probe_verdict(sent)
            verdict["echo"] = "{}"  # deliberately wrong
            return verdict, sent

        monkeypatch.setattr(checker_module, "_invoke", fake_invoke)
        result = resolve_checker()
        assert isinstance(result, Unavailable)
        assert "protocol failure" in result.reason

    def test_non_countermodel_probe_status_is_a_capability_failure(self, tmp_path, monkeypatch):
        self._configure_explicit(tmp_path, monkeypatch)

        def fake_invoke(binary, payload, timeout):
            sent = checker_module.canonical_wire_bytes(payload)
            return {"status": "error", "message": "boom"}, sent

        monkeypatch.setattr(checker_module, "_invoke", fake_invoke)
        result = resolve_checker()
        assert isinstance(result, Unavailable)
        assert "capability failure" in result.reason


class TestOptionalDigestPin:
    def test_binary_not_matching_configured_digest_is_refused(self, tmp_path, monkeypatch):
        explicit = tmp_path / "explicit_binary"
        explicit.write_text("real content")
        monkeypatch.setenv("BIMODAL_CHECKER_BIN", str(explicit))
        monkeypatch.setenv("BIMODAL_CHECKER_SHA256", "0" * 64)

        def fake_invoke(binary, payload, timeout):
            raise AssertionError("must not invoke a binary that failed the digest check")

        monkeypatch.setattr(checker_module, "_invoke", fake_invoke)
        result = resolve_checker()
        assert isinstance(result, Unavailable)
        assert "SHA-256" in result.reason

    def test_binary_matching_configured_digest_is_accepted(self, tmp_path, monkeypatch):
        import hashlib

        explicit = tmp_path / "explicit_binary"
        explicit.write_text("real content")
        digest = hashlib.sha256(b"real content").hexdigest()
        monkeypatch.setenv("BIMODAL_CHECKER_BIN", str(explicit))
        monkeypatch.setenv("BIMODAL_CHECKER_SHA256", digest)

        def fake_invoke(binary, payload, timeout):
            sent = checker_module.canonical_wire_bytes(payload)
            return _fake_probe_verdict(sent), sent

        monkeypatch.setattr(checker_module, "_invoke", fake_invoke)
        result = resolve_checker()
        assert isinstance(result, CheckerHandle)

    def test_digest_file_beside_binary_is_used_when_no_env_var_is_set(self, tmp_path, monkeypatch):
        import hashlib

        explicit = tmp_path / "explicit_binary"
        explicit.write_text("real content")
        digest = hashlib.sha256(b"real content").hexdigest()
        (tmp_path / "explicit_binary.sha256").write_text(digest + "\n")
        monkeypatch.setenv("BIMODAL_CHECKER_BIN", str(explicit))

        def fake_invoke(binary, payload, timeout):
            sent = checker_module.canonical_wire_bytes(payload)
            return _fake_probe_verdict(sent), sent

        monkeypatch.setattr(checker_module, "_invoke", fake_invoke)
        result = resolve_checker()
        assert isinstance(result, CheckerHandle)


class TestCheckCertificate:
    def test_unavailable_checker_yields_unavailable_outcome(self):
        outcome = check_certificate({"target": {"premises": [], "conclusions": [], "time": 0}, "bx": [], "lassos": []})
        assert outcome.available is False
        assert outcome.reason is not None

    def test_matching_echo_yields_available_outcome_with_verdict(self, tmp_path, monkeypatch):
        explicit = tmp_path / "explicit_binary"
        explicit.write_text("#!/bin/sh\n")
        monkeypatch.setenv("BIMODAL_CHECKER_BIN", str(explicit))

        def fake_invoke(binary, payload, timeout):
            sent = checker_module.canonical_wire_bytes(payload)
            return _fake_probe_verdict(sent), sent

        monkeypatch.setattr(checker_module, "_invoke", fake_invoke)
        payload = {"target": {"premises": [], "conclusions": [], "time": 0}, "bx": [], "lassos": []}
        outcome = check_certificate(payload)
        assert outcome.available is True
        assert outcome.verdict["acceptance"] == "entailment"
        assert outcome.checker.source == "explicit"

    def test_echo_mismatch_on_real_invocation_raises_protocol_failure(self, tmp_path, monkeypatch):
        explicit = tmp_path / "explicit_binary"
        explicit.write_text("#!/bin/sh\n")
        monkeypatch.setenv("BIMODAL_CHECKER_BIN", str(explicit))

        probe_sent_holder = {}

        def fake_invoke(binary, payload, timeout):
            sent = checker_module.canonical_wire_bytes(payload)
            if "probed" not in probe_sent_holder:
                probe_sent_holder["probed"] = True
                return _fake_probe_verdict(sent), sent
            # Real invocation: respond with a mismatched echo.
            verdict = _fake_probe_verdict(sent)
            verdict["echo"] = "{}"
            return verdict, sent

        monkeypatch.setattr(checker_module, "_invoke", fake_invoke)
        payload = {"target": {"premises": [], "conclusions": [], "time": 0}, "bx": [], "lassos": []}
        with pytest.raises(ProtocolFailure):
            check_certificate(payload)


class TestNoTestTreeDependency:
    def test_module_does_not_import_the_test_tree(self):
        import inspect

        import model_checker.theory_lib.bimodal.semantic.checker as mod

        source = inspect.getsource(mod)
        assert "tests." not in source
        assert "from ..tests" not in source
