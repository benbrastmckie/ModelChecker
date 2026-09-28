"""Unit tests for `BimodalStructure` under the certificate redesign (Phase 12): the
`_setup_solver` finalize hook (D6), extraction + independent re-check on every satisfying
model (obligation S3), the fail-fast guard on a corrupted certificate, and the D8
never-report-validity contract for the no-certificate case. Also carries the A0
frame-class standing test (deferred here from Phase 9 -- see that phase's handoff -- since
it needs this phase's own working solve-and-render path).
"""

from __future__ import annotations

import sys

import pytest

from model_checker.theory_lib.bimodal.semantic.certificate import recheck
from model_checker.theory_lib.bimodal.tests._build_support import _build as _shared_build


def _build(premises, conclusions, **setting_overrides):
    """Build one example through the shared `Syntax -> ModelConstraints -> BimodalStructure`
    pipeline (`_build_support._build`), with one local addition: `'verify'` defaults to `'off'`
    unless a test explicitly overrides it. This module's tests are about extraction,
    re-checking, and print formatting, not about which of item 1's three verification states
    renders -- they must not depend on whether a real checker binary happens to be resolvable
    on the machine running them. A test that specifically exercises `'verify'`
    (`TestVerificationLabelRendering`) passes it explicitly, which wins here. This is the one
    call site the implementation plan's Phase 2 keeps a local wrapper for, rather than
    collapsing to a bare import of the shared helper -- see `_build_support.py`'s own docstring
    for the same note from the other side."""
    if 'verify' not in setting_overrides:
        setting_overrides = dict(setting_overrides, verify='off')
    return _shared_build(premises, conclusions, **setting_overrides)


class TestFinalizeCalledExactlyOnceAcrossSetupAndReSolve:
    def test_setup_solver_finalizes_the_certificate_before_solving(self):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        assert structure.semantics._certificate_finalized is True
        assert len(structure.semantics.frame_constraints) > 0

    def test_setup_solver_called_again_does_not_duplicate_the_global_constraints(self):
        """D6: `re_solve()` and the model iterator (a later phase) both call
        `_setup_solver` again on the same `model_constraints` -- `finalize_certificate()`'s
        own idempotence (already unit-tested directly in `test_semantics_core.py`) is what
        makes a second `_setup_solver` call here safe. `re_solve()` itself is not exercised
        directly: `ModelDefaults.solve()`'s own `finally` clause always clears `self.solver`
        after a solve (framework-wide, not bimodal-specific), so a bare post-construction
        `re_solve()` call is not a meaningful scenario for any theory without the caller
        (the iterator) first re-populating `self.solver` -- exactly what Phase 15 does."""
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        count_after_first_solve = len(structure.semantics.frame_constraints)
        structure._setup_solver(structure.model_constraints)
        assert len(structure.semantics.frame_constraints) == count_after_first_solve


class TestEverySatisfiableSolveProducesAReCheckedCertificate:
    def test_simple_countermodel_produces_a_certificate_passing_the_rechecker(self):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        assert structure.z3_model_status is True
        assert structure.certificate is not None
        assert structure.target_time is not None

        verdict = recheck(
            structure.certificate,
            premises=structure.semantics._premise_formulas,
            conclusions=structure.semantics._conclusion_formulas,
            target_time=structure.target_time,
        )
        assert verdict["status"] == "countermodel", verdict

    def test_boxed_premise_countermodel_has_the_expected_lasso_count(self):
        structure = _build(["\\Box A"], ["B"], back=1, mid=0, fwd=1)
        assert structure.z3_model_status is True
        assert structure.certificate is not None
        # Main lasso plus exactly one witness lasso for the single boxed subformula.
        assert len(structure.certificate.lassos) == 2

    def test_main_point_position_is_updated_to_the_extracted_target_time(self):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        assert structure.main_point["position"] == structure.target_time
        # The same dict object semantics itself carries (D3/D6 aliasing discipline).
        assert structure.semantics.main_point is structure.main_point


class TestUnsatisfiableSolveNeverClaimsValidity:
    def test_certificate_and_target_time_are_none_when_unsatisfiable(self):
        # A / not-A is unsatisfiable at every position: no premise implication can hold
        # for a premise and its own negation as the sole conclusion at the same target.
        structure = _build(["A", "\\neg A"], [], back=1, mid=0, fwd=1)
        assert structure.z3_model_status is False
        assert structure.certificate is None
        assert structure.target_time is None


class TestFailFastGuardOnACorruptedCertificate:
    """The S3 obligation (`__init__`'s own module docstring): a Z3 model whose extracted
    certificate fails the independent pure-Python re-check must raise
    `ModelConstructionError` immediately, never silently accept it. `extract_certificate`
    is monkeypatched to return a deliberately-corrupted `WitnessFamily` -- a lasso whose
    `mid` label violates local coherence (an `Imp` node whose membership contradicts its
    own biconditional) -- confirming the hook (Phase 12's `BimodalStructure.__init__`) is
    genuinely reached on every satisfiable solve, not merely exercised by coincidence
    whenever the real encoder happens to produce a bad certificate (Phase 16's own
    discovery of a real instance of exactly this failure mode, since fixed, is what this
    test exists to keep caught should it ever recur)."""

    def test_corrupted_certificate_raises_model_construction_error(self, monkeypatch):
        from model_checker.theory_lib.errors import ModelConstructionError
        from model_checker.theory_lib.bimodal.semantic.certificate import (
            LabelledLasso,
            WitnessFamily,
        )
        from model_checker.theory_lib.bimodal.semantic.formula import Atom, Bot, Imp
        from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics

        # An Imp node present in the label but with a left/right combination that
        # violates the (C1) biconditional: `f in label` should equal
        # `(f.left not in label) or (f.right in label)`. Here f = (A -> bot) is placed in
        # the label while A is ALSO in the label and bot is NOT -- the biconditional's RHS
        # is False, contradicting the LHS `True`.
        bad_formula = Imp(Atom("A"), Bot())
        bad_label = frozenset({bad_formula, Atom("A")})
        corrupted_lasso = LabelledLasso(back=(bad_label,), mid=(), fwd=(bad_label,))
        corrupted_family = WitnessFamily(bx={}, lassos=(corrupted_lasso,))

        def fake_extract_certificate(self, z3_model):
            return corrupted_family, 0

        monkeypatch.setattr(
            BimodalSemantics, "extract_certificate", fake_extract_certificate
        )

        with pytest.raises(ModelConstructionError, match="obligation S3"):
            _build(["A"], ["B"], back=1, mid=0, fwd=1)


class TestExtractionHelpers:
    def test_extract_states_lists_one_entry_per_lasso(self):
        structure = _build(["\\Box A"], ["B"], back=1, mid=0, fwd=1)
        states = structure.extract_states()
        assert len(states["worlds"]) == len(structure.certificate.lassos)
        assert states["possible"] == []
        assert states["impossible"] == []

    def test_extract_evaluation_world_names_the_main_lasso(self):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        assert structure.extract_evaluation_world() == f"lasso{structure.main_point['lasso']}"

    def test_extract_relations_describes_the_shift_when_a_certificate_exists(self):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        relations = structure.extract_relations()
        assert "shift" in relations

    def test_extract_relations_is_empty_without_a_certificate(self):
        structure = _build(["A", "\\neg A"], [], back=1, mid=0, fwd=1)
        assert structure.extract_relations() == {}
        assert structure.extract_states()["worlds"] == []
        assert structure.extract_evaluation_world() is None


class TestPrintingDoesNotClaimValidity:
    def test_print_certificate_does_not_raise_with_a_certificate(self, capsys):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        # capsys captures sys.stdout, not the theory's sys.__stdout__ default -- pass it
        # explicitly, matching every other theory's test convention for this default.
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        assert "Certificate:" in out
        assert "valid" not in out.lower()

    def test_print_certificate_reports_no_certificate_without_claiming_invalidity_or_validity(self, capsys):
        structure = _build(["A", "\\neg A"], [], back=1, mid=0, fwd=1)
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        assert "No certificate found" in out
        assert "not a validity claim" in out
        assert "invalid" not in out.lower()

    def test_print_evaluation_reports_no_certificate_case(self, capsys):
        structure = _build(["A", "\\neg A"], [], back=1, mid=0, fwd=1)
        structure.print_evaluation(output=sys.stdout)
        out = capsys.readouterr().out
        assert "No certificate found" in out


class TestVerificationLabelRendering:
    """Item 1's output gate: `print_certificate` and
    `print_evaluation` render one of the three honest states -- see
    `tests/integration/test_output_gate.py` for the full-pipeline coverage of all three plus
    `'verify': 'required'` withholding. This class covers only the two states reachable
    without a real checker binary: 'off', and 'auto' with the checker forced unavailable
    (never the checked state, which needs a real subprocess -- that belongs to the
    integration test, which skips cleanly without one)."""

    def test_verify_off_renders_the_skipped_label_and_never_probes(self, capsys, monkeypatch):
        from model_checker.theory_lib.bimodal.semantic import checker as checker_module

        def fail_if_called(*args, **kwargs):
            raise AssertionError("verify='off' must never invoke the checker resolver")

        monkeypatch.setattr(checker_module, "resolve_checker", fail_if_called)
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1, verify="off")
        structure.print_certificate(output=sys.stdout)
        structure.print_evaluation(output=sys.stdout)
        out = capsys.readouterr().out
        assert "Verification: independent check skipped" in out
        assert "kernel-checked proof" not in out

    def test_verify_auto_with_no_checker_renders_the_unchecked_label(self, capsys, monkeypatch, tmp_path):
        monkeypatch.setenv("BIMODAL_LOGIC_PATH", str(tmp_path / "no_such_checkout"))
        monkeypatch.delenv("BIMODAL_CHECKER_BIN", raising=False)
        from model_checker.theory_lib.bimodal.semantic import checker as checker_module

        checker_module._reset_for_tests()
        try:
            structure = _build(["A"], ["B"], back=1, mid=0, fwd=1, verify="auto")
            structure.print_certificate(output=sys.stdout)
            structure.print_evaluation(output=sys.stdout)
            out = capsys.readouterr().out
            assert "Verification: re-checked by this repository's own pure-Python" in out
            assert "no independent checker available" in out
            assert "kernel-checked proof" not in out
        finally:
            # Never leak this test's forced-unavailable resolution into a later test in the
            # same pytest session (resolve_checker() memoizes per process, not per test).
            checker_module._reset_for_tests()


class TestGoldenOutputCertificateFormat:
    """Golden-output coverage for report 01 section 4.4's output shape: each history as
    `(back)^w | mid | (fwd)^w` over atom valuations, with the evaluation position marked."""

    def test_single_slot_lasso_renders_back_mid_fwd_with_the_marked_position(self, capsys):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        lines = [line for line in out.splitlines() if line.strip().startswith("L0")]
        assert len(lines) == 1
        # Exactly one of the two slots (back or fwd) is the marked (bracketed) evaluation
        # position and carries {A}; the other is empty. Which slot the solver picks for the
        # target is not fixed by the constraints (D5's one-hot selector ranges over the
        # whole window), so assert the golden shape rather than a specific slot.
        line = lines[0].strip()
        assert line in (
            "L0 (main): ([{A}])^w | - | ({})^w",
            "L0 (main): ({})^w | - | ([{A}])^w",
        ), line

    def test_boxed_subformula_table_lists_the_guess_and_a_false_boxs_witness(self, capsys):
        structure = _build(["\\Box A"], ["B"], back=1, mid=0, fwd=1)
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        assert "Boxed subformulas:" in out
        assert "Box(Atom(base='A', fresh_index=None)) = " in out
        # Whichever way the guess landed, the table format itself is exercised; if guessed
        # false, a witness line for L1 must also appear.
        if "= False" in out:
            assert "Witness: L1" in out


# Local to the property this module pins -- the A0 frame-class standing test's
# non-inconclusiveness across a swept grid of lengths -- and deliberately not merged with
# `test_certificate_a2_triangle.py`'s A2-triangle grid or `test_search_period_coverage.py`'s
# `_GRID`, each of which pins an independent property over its own premises/conclusions and
# grid points (implementation plan Phase 2, declined route F2).
_A0_SWEPT_GRID = [
    (1, 1, 1), (2, 1, 1), (3, 1, 1),
    (1, 1, 2), (2, 1, 2), (3, 1, 2),
    (2, 1, 3), (3, 1, 3),
    (2, 2, 2),
    (4, 1, 4),
    (1, 0, 1),
]


class TestA0FrameClassStandingTest:
    """Amendment task deferred from Phase 9 (see that phase's handoff): the `prior_UZ` and
    `z1` instances are classified minimum-frame-class `.ZTime`
    (`ProofSystem/Axioms.lean:612-613`), so by (SOUND) no certificate can ever exist for
    them even though they are not valid at every temporal order
    (`not_validIn_base_prior_UZ`/`not_validIn_base_z1`,
    `Metalogic/Independence/ZTimeSharpness.lean:225, 236`). The deciding test now runs at
    every configured length in the swept grid `_A0_SWEPT_GRID` rather than one modest
    length, and asserts non-inconclusiveness (`timeout is False`) alongside the no-certificate
    verdict: `models/structure.py` maps a solver UNKNOWN to `status=False` with `timeout=True`,
    so the no-certificate assertion alone does not distinguish "no countermodel exists" from
    "the solver gave up" -- and §7.2's claim is the former. See `docs/ADEQUACY.md` sections 7.2
    and 7.4. The search's non-monotonicity in `back`/`mid`/`fwd` (§7.1's divisibility argument)
    does **not** disturb A0, as (SOUND) predicts it cannot -- which is what makes the swept grid
    a useful control and not merely more cases: every point below is independently, genuinely
    UNSAT rather than merely one point that happened to be.
    """

    # prior_UZ: F phi -> (neg phi Until phi), guard-first (Lean's Untl(guard=neg phi,
    # event=phi)). Bimodal's \Future primitive means "always in the future" (G); the
    # defined "eventually" (F) operator is the lowercase \future. ModelChecker's own
    # \Until is now guard-first too (D2): "X \Until Y" translates to Untl(guard=X,
    # event=Y), so guard=neg A / event=A is written "(\neg A) \Until A", positional
    # identity with no swap.
    #
    # The deciding question is whether a Z-time COUNTERMODEL to this axiom's validity
    # exists -- i.e. whether the search can make it FALSE somewhere -- not whether it
    # is merely satisfiable (nearly every formula is). So it goes in `conclusions` with
    # no premises: a found certificate would be a countermodel refuting the axiom; "no
    # certificate" is the deciding, expected outcome for a ZTime-valid axiom.
    @pytest.mark.parametrize("back,mid,fwd", _A0_SWEPT_GRID)
    def test_prior_uz_instance_reports_no_certificate(self, back, mid, fwd):
        structure = _build(
            [], ["(\\future A \\rightarrow (\\neg A \\Until A))"], back=back, mid=mid, fwd=fwd
        )
        assert structure.z3_model_status is False
        assert structure.certificate is None
        assert structure.timeout is False

    # z1: G(G phi -> phi) -> (F G phi -> G phi), with G = \Future (primitive) and
    # F = \future (defined, DefFutureOperator). Unary operators chain directly onto
    # their argument without extra parens (examples.py's own convention, e.g.
    # '\\Future \\past A'). As with prior_UZ, this is the conclusion of an empty-premise
    # search: a found certificate would be a countermodel to z1's validity.
    @pytest.mark.parametrize("back,mid,fwd", _A0_SWEPT_GRID)
    def test_z1_instance_reports_no_certificate(self, back, mid, fwd):
        formula = (
            "(\\Future (\\Future A \\rightarrow A) \\rightarrow "
            "(\\future \\Future A \\rightarrow \\Future A))"
        )
        structure = _build([], [formula], back=back, mid=mid, fwd=fwd)
        assert structure.z3_model_status is False
        assert structure.certificate is None
        assert structure.timeout is False
