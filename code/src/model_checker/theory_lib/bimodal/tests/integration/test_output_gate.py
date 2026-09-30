"""Integration tests for the certificate verification output gate:
`'verify'`'s three values, the three rendered output states, and `'required'`'s withholding
error. See `docs/SETTINGS.md`'s "Certificate Verification" section (Phase 5) for the
user-facing contract this module locks down, and `semantic/model.py`'s module docstring
("The output gate") for the mechanism.

Three of the four scenarios below need no real checker binary at all -- they force one
unavailable via environment isolation, matching `tests/unit/test_checker.py`'s own discipline.
Only `TestRealCheckerReportsIndependentlyChecked` needs a real BimodalLogic checkout and `lake`,
and skips cleanly, with a named reason, without one -- mirroring
`test_certificate_lean_agreement.py`'s own skip discipline via the shared `_lean_check` probe.
"""

from __future__ import annotations

import sys

import pytest

from model_checker.theory_lib.bimodal.semantic import checker as checker_module
from model_checker.theory_lib.bimodal.tests._build_support import _build, _settings
from model_checker.theory_lib.bimodal.tests._lean_check import SKIP_REASON
from model_checker.theory_lib.errors import ModelConstructionError

# The forbidden overclaim (F2, docs/TRUST_PIPELINE.md's remaining-work table): this phrase
# describes the reserved third Acceptance value (per-certificate kernel checking by
# re-elaboration), which nothing this checker produces today -- see
# BimodalTools/CertificateImport.lean's Acceptance docstring. No rendered output may contain it.
FORBIDDEN_OVERCLAIM = "kernel-checked proof"


def _dewrapped_verification(out: str) -> str:
    """Reconstruct the (possibly multi-line, wrapped) `Verification:` block back into a
    single space-joined string, so a test can assert on a phrase that might straddle a
    wrap boundary without caring exactly where the wrap fell."""
    verification_lines = []
    capturing = False
    for line in out.splitlines():
        if line.startswith("Verification:"):
            capturing = True
            verification_lines.append(line[len("Verification: "):])
        elif capturing and line.startswith("  "):
            verification_lines.append(line.strip())
        elif capturing:
            break
    return " ".join(verification_lines)


@pytest.fixture(autouse=True)
def _isolated_checker_resolution():
    """Every test in this module controls checker resolution explicitly (environment
    variables plus `_reset_for_tests()`) -- never inherit a memoized resolution left behind by
    an earlier test in the same pytest session, and never leak one forward either."""
    checker_module._reset_for_tests()
    yield
    checker_module._reset_for_tests()


def _force_no_checker(monkeypatch, tmp_path):
    monkeypatch.setenv("BIMODAL_LOGIC_PATH", str(tmp_path / "no_such_bimodal_logic_checkout"))
    monkeypatch.delenv("BIMODAL_CHECKER_BIN", raising=False)


class TestVerificationLineWidthAndRoundTrip:
    """`Verification:` is the longest line in a default run (234 chars unwrapped) and must
    wrap at print time to an 80-column budget without losing or duplicating a word at a
    wrap boundary, and without breaking the existing one-occurrence-per-example contract.
    Covers both no-checker scenarios this module already exercises without a real checker
    binary."""

    def _assert_wrapped_correctly(self, structure, capsys):
        structure.print_evaluation(output=sys.stdout)
        out = capsys.readouterr().out
        lines = out.splitlines()
        assert max((len(line) for line in lines), default=0) <= 80
        assert out.count("Verification:") == 1

        # Round-trip: stripping the "Verification: " prefix off the first line and each
        # continuation line's indent, then joining with spaces, recovers the unwrapped
        # label exactly -- no word lost or duplicated at a wrap boundary.
        assert _dewrapped_verification(out) == structure._verification_label()
        assert FORBIDDEN_OVERCLAIM not in out

    def test_verify_off_wraps_within_budget(self, monkeypatch, tmp_path, capsys):
        _force_no_checker(monkeypatch, tmp_path)
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1, verify="off")
        self._assert_wrapped_correctly(structure, capsys)

    def test_verify_auto_with_no_checker_wraps_within_budget(self, monkeypatch, tmp_path, capsys):
        _force_no_checker(monkeypatch, tmp_path)
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1, verify="auto")
        self._assert_wrapped_correctly(structure, capsys)


class TestVerifyAutoWithNoChecker:
    """'auto' (the default): the countermodel is always reported, labelled Python-re-checked
    only when no checker is available -- absence never fails a solve."""

    def test_reports_unchecked_countermodel_with_the_honest_label(
        self, monkeypatch, tmp_path, capsys
    ):
        _force_no_checker(monkeypatch, tmp_path)
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1, verify="auto")
        assert structure.z3_model_status is True
        assert structure.certificate is not None
        assert structure.verification_checked is False
        assert structure.verification_reason is not None

        structure.print_certificate(output=sys.stdout)
        structure.print_evaluation(output=sys.stdout)
        out = capsys.readouterr().out
        assert "Histories:" in out
        dewrapped = _dewrapped_verification(out)
        assert "re-checked by this repository's own pure-Python decision procedures only" in dewrapped
        assert "no independent checker available" in dewrapped
        assert out.count("Verification:") == 1
        assert FORBIDDEN_OVERCLAIM not in out


class TestVerifyOffNeverInvokesTheChecker:
    """'off': no independent check is attempted -- the checker is never even asked to
    resolve, matching item 1's "no checker invocation occurs at all" requirement."""

    def test_verify_off_performs_no_resolution_at_all(self, monkeypatch, tmp_path, capsys):
        _force_no_checker(monkeypatch, tmp_path)

        def fail_if_called(*args, **kwargs):
            raise AssertionError("verify='off' must never resolve or invoke the checker")

        monkeypatch.setattr(checker_module, "resolve_checker", fail_if_called)
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1, verify="off")
        assert structure.certificate is not None
        assert structure.verification_checked is False
        assert structure.verification_reason is None

        structure.print_certificate(output=sys.stdout)
        structure.print_evaluation(output=sys.stdout)
        out = capsys.readouterr().out
        assert "independent check skipped" in out
        assert out.count("Verification:") == 1
        assert FORBIDDEN_OVERCLAIM not in out


class TestVerifyRequiredWithholdsWithoutAChecker:
    """'required': a countermodel that cannot be independently checked is withheld -- raised
    as an error, never printed."""

    def test_raises_instead_of_reporting_when_no_checker_is_available(
        self, monkeypatch, tmp_path
    ):
        _force_no_checker(monkeypatch, tmp_path)
        with pytest.raises(ModelConstructionError, match="required"):
            _build(["A"], ["B"], back=1, mid=0, fwd=1, verify="required")

    def test_withholding_error_names_how_to_obtain_a_checker(self, monkeypatch, tmp_path):
        _force_no_checker(monkeypatch, tmp_path)
        with pytest.raises(ModelConstructionError) as excinfo:
            _build(["A"], ["B"], back=1, mid=0, fwd=1, verify="required")
        assert "BIMODAL_CHECKER_BIN" in str(excinfo.value) or "SETTINGS.md" in str(
            excinfo.value
        )


class TestUnknownVerifyValueFailsFast:
    def test_unknown_verify_value_is_rejected_early(self):
        with pytest.raises(ValueError, match="verify"):
            _build(["A"], ["B"], back=1, mid=0, fwd=1, verify="paranoid")


@pytest.mark.skipif(SKIP_REASON is not None, reason=SKIP_REASON or "")
class TestRealCheckerReportsIndependentlyChecked:
    """Runs only with a real BimodalLogic checkout and `lake` available (the same resolution
    order `tests/_lean_check.py`'s module-level probe already used to compute `SKIP_REASON`) --
    the only scenario in this module that needs a real subprocess invocation."""

    def test_verify_auto_with_a_real_checker_reports_the_checked_label(self, capsys):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1, verify="auto")
        assert structure.certificate is not None
        assert structure.verification_checked is True
        assert structure.verification_acceptance in ("decided", "entailment")

        structure.print_certificate(output=sys.stdout)
        structure.print_evaluation(output=sys.stdout)
        out = capsys.readouterr().out
        assert "independently checked" in out
        assert "WitnessFamily.Refutes" in out
        assert out.count("Verification:") == 1
        # The checkout hash is shortened to 12 hex characters on screen.
        if structure.verification_provenance:
            assert structure.verification_provenance[:12] in out
            assert structure.verification_provenance not in out
        assert FORBIDDEN_OVERCLAIM not in out

    def test_verify_required_with_a_real_checker_reports_normally(self):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1, verify="required")
        assert structure.certificate is not None
        assert structure.verification_checked is True
