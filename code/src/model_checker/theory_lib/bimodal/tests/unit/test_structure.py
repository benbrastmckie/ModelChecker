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
        assert structure.extract_evaluation_world() == f"L{structure.main_point['lasso']}"

    def test_extract_states_names_lassos_as_on_screen(self):
        structure = _build(["\\Box A"], ["B"], back=1, mid=0, fwd=1)
        assert structure.extract_states()["worlds"] == ["L0", "L1"]

    def test_extract_relations_describes_the_shift_when_a_certificate_exists(self):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        relations = structure.extract_relations()
        assert "shift" in relations

    def test_extract_relations_lists_box_guesses_with_certificate_witnesses(self):
        structure = _build(
            ["\\Box (A \\vee B)"], ["\\Box A", "\\Box B"], back=2, mid=1, fwd=2
        )
        guesses = structure.extract_relations()["box_guesses"]
        assert len(guesses) == 3
        for entry in guesses:
            assert set(entry) == {"formula", "guess", "witness"}
            assert isinstance(entry["formula"], str)
            assert isinstance(entry["guess"], bool)
            if entry["guess"]:
                assert entry["witness"] is None
            else:
                assert set(entry["witness"]) == {"lasso", "position"}
        # Sorted by repr for determinism: the three children are A, B, (A -> ...) in repr order.
        assert [e["formula"] for e in guesses] == sorted(e["formula"] for e in guesses)

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
        assert "Histories:" in out
        assert "Certificate:" not in out
        assert "valid" not in out.lower()

    def test_print_certificate_reports_no_certificate_without_claiming_invalidity_or_validity(self, capsys):
        structure = _build(["A", "\\neg A"], [], back=1, mid=0, fwd=1)
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        assert "Histories:" in out
        assert "Certificate:" not in out
        assert "No certificate found within the configured bounds" in out
        assert "not a validity claim" in out
        assert "invalid" not in out.lower()

    def test_print_evaluation_reports_no_certificate_case(self, capsys):
        structure = _build(["A", "\\neg A"], [], back=1, mid=0, fwd=1)
        structure.print_evaluation(output=sys.stdout)
        out = capsys.readouterr().out
        assert "No certificate found" in out

    def test_print_all_reports_no_certificate_exactly_once(self, capsys):
        structure = _build(["A", "\\neg A"], [], back=1, mid=0, fwd=1)
        structure.print_all(structure.settings, "EX", "Bimodal", output=sys.stdout)
        out = capsys.readouterr().out
        assert out.count("No certificate found") == 1
        assert "not a validity claim" in out
        assert "Histories:" in out
        assert "Certificate:" not in out
        assert "Search bounds: back=1, mid=0, fwd=1" in out
        assert "Atomic States" not in out


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
        assert out.count("Verification:") == 1
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
            assert out.count("Verification:") == 1
            assert "kernel-checked proof" not in out
        finally:
            # Never leak this test's forced-unavailable resolution into a later test in the
            # same pytest session (resolve_checker() memoizes per process, not per test).
            checker_module._reset_for_tests()


class TestBoxWitnessFromCertificate:
    """The printed witness for a false box is computed from the certificate itself, never
    from `WitnessRegistry._witness_lassos`: the registry index is reserved capacity, not
    provenance (`box_faithfulness_constraints` lets any lasso falsify a box), so on the
    `MD_CM_1` shape the registry names `L1` for `□A` while the only falsifier is on `L3`."""

    @staticmethod
    def _md_cm_1():
        return _build(["\\Box (A \\vee B)"], ["\\Box A", "\\Box B"], back=2, mid=1, fwd=2)

    def test_every_false_box_gets_a_witness_the_certificate_accepts(self):
        from model_checker.theory_lib.bimodal.semantic.certificate import _box_window
        from model_checker.theory_lib.bimodal.semantic.formula import Box

        structure = self._md_cm_1()
        children = {f.child for f in structure.semantics.witness_registry.closure if isinstance(f, Box)}
        false_children = [c for c in children if not structure.certificate.bx_of(c)]
        assert false_children, "MD_CM_1 must guess at least one box false"
        for child in false_children:
            witness = structure.box_witness(child)
            assert witness is not None
            lasso_index, t = witness
            lasso = structure.certificate.lassos[lasso_index]
            assert t in _box_window(lasso)
            assert child not in lasso.label(t)

    def test_witness_is_not_read_from_the_registry_index(self):
        from model_checker.theory_lib.bimodal.semantic.formula import Atom

        structure = self._md_cm_1()
        registry = structure.semantics.witness_registry._witness_lassos
        for child in (Atom("A"), Atom("B")):
            if structure.certificate.bx_of(child):
                continue
            lasso_index, t = structure.box_witness(child)
            reserved = registry[child]
            reserved_lasso = structure.certificate.lassos[reserved]
            # Either the reserved lasso genuinely falsifies at the reported position, or
            # the reported lasso differs from the reserved one -- never a reserved index
            # reported without evidence.
            assert child not in structure.certificate.lassos[lasso_index].label(t)
            if lasso_index == reserved:
                assert child not in reserved_lasso.label(t)

    def test_a_non_main_falsifier_is_preferred_when_one_exists(self):
        from model_checker.theory_lib.bimodal.semantic.certificate import _box_window
        from model_checker.theory_lib.bimodal.semantic.formula import Box

        structure = self._md_cm_1()
        lassos = structure.certificate.lassos
        children = {f.child for f in structure.semantics.witness_registry.closure if isinstance(f, Box)}
        for child in children:
            if structure.certificate.bx_of(child):
                continue
            non_main = [
                (i, t) for i, lasso in enumerate(lassos) if i != 0
                for t in _box_window(lasso) if child not in lasso.label(t)
            ]
            if non_main:
                assert structure.box_witness(child)[0] != 0

    def test_falls_back_to_the_main_lasso_honestly(self):
        from model_checker.theory_lib.bimodal.semantic.certificate import LabelledLasso, WitnessFamily
        from model_checker.theory_lib.bimodal.semantic.formula import Atom

        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        a = Atom("A")
        only_main_falsifies = WitnessFamily(
            bx={a: False},
            lassos=(
                LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset({a}),)),
                LabelledLasso(back=(frozenset({a}),), mid=(), fwd=(frozenset({a}),)),
            ),
        )
        structure.certificate = only_main_falsifies
        assert structure.box_witness(a) == (0, -1)

    def test_true_box_has_no_witness(self):
        from model_checker.theory_lib.bimodal.semantic.formula import Atom, Bot, Imp

        structure = self._md_cm_1()
        a_or_b = Imp(Imp(Atom("A"), Bot()), Atom("B"))
        assert structure.certificate.bx_of(a_or_b) is True
        assert structure.box_witness(a_or_b) is None

    def test_box_guesses_is_sorted_and_carries_the_witness(self):
        from model_checker.theory_lib.bimodal.semantic.formula import Atom

        structure = self._md_cm_1()
        guesses = structure.box_guesses()
        assert [repr(f) for f, _, _ in guesses] == sorted(repr(f) for f, _, _ in guesses)
        by_formula = {f: (g, w) for f, g, w in guesses}
        assert by_formula[Atom("A")] == (False, structure.box_witness(Atom("A")))
        assert structure.box_guesses() == guesses  # deterministic across calls

    def test_no_certificate_means_no_guesses(self):
        structure = _build(["A", "\\neg A"], [], back=1, mid=0, fwd=1)
        assert structure.box_guesses() == []
        assert structure.extract_relations() == {}


LEGEND = (
    "(t:atoms) states joined by ⟹, … marks the periodic back/fwd segments, "
    "| separates back | mid | fwd, [ ] marks the evaluation point"
)


def _joiner_columns(row: str) -> list:
    """Column indices of every ` ⟹ ` and ` | ` joiner in a history row, in order."""
    import re
    return [m.start() for m in re.finditer(r" ⟹ | \| ", row)]


class TestGoldenOutputHistoriesFormat:
    """Golden-output coverage for the `Histories:` block: one time-labelled arrow-chain row
    per lasso -- `… (-2:B) ⟹ (-1:B) | (0:B) | (+1:B) ⟹ [+2:A] …` -- with `(t:atoms)` states,
    ` ⟹ ` within the periodic back/fwd segments, ` | ` between segments, `…` marking the
    periodic repetition, a role column, the evaluation point marked `[ ]`, empty labels as
    `∅`, columns aligned across rows, a `Box guesses:` table whose witness is the
    certificate-derived `(lasso, t)` pair, and formulas in the user's own notation."""

    @staticmethod
    def _md_cm_1():
        return _build(["\\Box (A \\vee B)"], ["\\Box A", "\\Box B"], back=2, mid=1, fwd=2)

    def test_single_slot_lasso_renders_back_mid_fwd_with_the_marked_position(self, capsys):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        lines = [line for line in out.splitlines() if line.strip().startswith("L0")]
        assert len(lines) == 1
        # Exactly one of the two slots (back or fwd) is the marked (bracketed) evaluation
        # position and carries A; the other is empty. Which slot the solver picks for the
        # target is not fixed by the constraints (D5's one-hot selector ranges over the
        # whole window), so assert the golden shape rather than a specific slot.
        # An empty `mid` collapses to a single ` | ` between back and fwd, never `| |`.
        line = lines[0].strip()
        assert line in (
            "L0  main  … [-1:A] | (0:∅) …",
            "L0  main  … (-1:∅) | [0:A] …",
        ), line

    def test_histories_line_carries_the_legend(self, capsys):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        legend_lines = [line for line in out.splitlines() if line.startswith("Histories:")]
        assert len(legend_lines) == 1
        assert LEGEND in legend_lines[0]
        assert "Certificate:" not in out

    def test_full_print_all_on_md_cm_1(self, capsys):
        import re

        structure = self._md_cm_1()
        # `BuildExample` interprets before printing and carries the general settings
        # `print_model` reads; do the same outside it.
        structure.interpret(structure.premises + structure.conclusions)
        structure.settings["print_z3"] = False
        structure.print_all(structure.settings, "MD_CM_1", "Bimodal", output=sys.stdout)
        out = capsys.readouterr().out

        # Header: bounds and lasso count replace the meaningless atomic-state count.
        assert "Search bounds: back=2, mid=1, fwd=2 (4 lassos: 1 main + 3 reserved witnesses)" in out
        assert "Atomic States" not in out

        # Histories: one row per lasso with a role column; roles come from the certificate scan.
        rows = {line.split()[0]: line for line in out.splitlines() if re.match(r"\s+L\d\s", line)}
        assert set(rows) == {"L0", "L1", "L2", "L3"}
        assert re.search(r"L0\s+main\s+…", rows["L0"])
        roles = [re.match(r"\s+L\d\s+(.*?)\s{2,}…", line).group(1) for line in rows.values()]
        assert "main" in roles
        assert any(r.startswith("witness for \\Box ") for r in roles)
        assert "reserved, unused" in roles
        # Each row is an arrow chain of `(t:atoms)` states: back=2 and fwd=2 give exactly
        # two ` ⟹ ` joiners, mid=1 gives exactly two ` | ` separators, `…` brackets the
        # periodic segments, and every state carries its signed time.
        cell = r"[(\[][+-]?\d+:[^)\]]+[)\]]"
        chain = rf"^\s+L\d\s+.+?\s{{2,}}… {cell} ⟹ {cell} \| {cell} \| {cell} ⟹ {cell} …$"
        for name, row in rows.items():
            assert re.match(chain, row), (name, row)
            assert row.count(" | ") == 2 and row.count(" ⟹ ") == 2, row
            times = re.findall(r"[(\[]([+-]?\d+):", row)
            assert times == ["-2", "-1", "0", "+1", "+2"], row
        marked = [name for name, row in rows.items() if "[" in row]
        assert marked == ["L0"]  # the evaluation point is marked on L0 only
        assert re.search(r"\[[+-]?\d+:[^\]]+\]", rows["L0"])
        assert "^ω" not in out
        # Column alignment: every joiner sits at the same column index in every row.
        columns = {name: _joiner_columns(row) for name, row in rows.items()}
        assert len({tuple(c) for c in columns.values()}) == 1, columns

        # Box guesses: user notation, aligned columns, witness read from the certificate.
        assert "Box guesses:" in out
        assert re.search(r"\\Box A\s+false\s+falsified at L\d, t=[+-]?\d+", out)
        assert re.search(r"\\Box B\s+false\s+falsified at L\d, t=[+-]?\d+", out)
        assert re.search(r"\\Box \(A \\vee B\)\s+true\s*$", out, re.MULTILINE)
        for match in re.finditer(r"falsified at L(\d), t=([+-]?\d+)", out):
            lasso_index, t = int(match.group(1)), int(match.group(2))
            assert lasso_index < len(structure.certificate.lassos)
            # The witness for each false box is genuinely a falsifier (C3).
        for child, guess, witness in structure.box_guesses():
            if not guess:
                lasso_index, t = witness
                assert child not in structure.certificate.lassos[lasso_index].label(t)

        # Evaluation point and exactly one verification line.
        assert re.search(r"Evaluation point: L0 at t=[+-]?\d+", out)
        assert out.count("Verification:") == 1
        assert out.count("Histories:") == 1
        assert "Certificate:" not in out

        # Interpreted sentences read `(True at L0, t=-2)`, and no repr leaks anywhere.
        assert re.search(r"\(True at L0, t=[+-]?\d+\)", out)
        assert "in lasso" not in out
        for leak in ("Atom(", "Imp(", "Box(", "Bot("):
            assert leak not in out, leak
        assert "\033[" not in out  # capsys is not a TTY

    def test_joiners_align_across_rows_when_cell_widths_differ(self, capsys):
        """A hand-built family whose lassos carry cells of different widths at the same
        position (`{A,B}` vs `A` vs `∅`): each position's column is padded to its widest
        cell, so every ` ⟹ ` and ` | ` joiner sits at the same column index in every row."""
        from model_checker.theory_lib.bimodal.semantic.certificate import LabelledLasso, WitnessFamily
        from model_checker.theory_lib.bimodal.semantic.formula import Atom

        structure = _build(["A", "B"], ["\\Box (A \\wedge B)"], back=1, mid=1, fwd=1)
        a, b = Atom("A"), Atom("B")
        wide = frozenset({a, b})
        narrow = frozenset({a})
        empty = frozenset()
        family = WitnessFamily(
            lassos=(
                LabelledLasso(back=(wide,), mid=(narrow,), fwd=(wide,)),
                LabelledLasso(back=(empty,), mid=(wide,), fwd=(narrow,)),
            ),
            bx=structure.certificate.bx,
        )
        structure.certificate = family
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        rows = [line for line in out.splitlines() if line.strip().startswith("L")]
        assert len(rows) == 2
        assert "{A,B}" in rows[0] and "∅" in rows[1]
        assert _joiner_columns(rows[0]) == _joiner_columns(rows[1]) != []
        assert not any(row.endswith(" ") for row in rows)

    def test_empty_labels_render_as_the_empty_set_glyph(self, capsys):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1)
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        assert "∅" in out
        assert "{}" not in out

    def test_witness_line_names_a_lasso_and_signed_time(self, capsys):
        structure = _build(["\\Box A"], ["B"], back=1, mid=0, fwd=1)
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        assert "Box guesses:" in out
        if "false" in out:
            import re
            assert re.search(r"falsified at L\d, t=(?:0|[+-]\d+)", out)

    def test_derived_operators_print_in_the_users_derived_notation(self, capsys):
        """`\\Diamond A` compiles to `\\neg \\Box \\neg A`, and `Syntax` records the derived
        subsentence `\\Box \\neg A` by name -- so the boxed closure member prints in that
        notation, never as a dataclass repr and never as the structural `□¬A` fallback
        (which `semantic/render.py` reserves for formulas no sentence names, e.g. an
        iteration diff's changed label bit)."""
        structure = _build(["\\Diamond A"], ["B"], back=1, mid=0, fwd=1)
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        assert "\\Box \\neg A" in out
        assert "Box(" not in out and "Imp(" not in out

    def test_cp1252_stream_gets_ascii_fallbacks_without_raising(self):
        """`TESTING_GUIDE.md` section 9.2: real encoded streams, never `StringIO`. The glyphs
        a real example reaches are `⟹` and `…` (every history row) and `∅` (empty labels);
        the renderer's own operator glyphs are covered by `test_render.py`'s cp1252 leg. `…`
        is a cp1252 code point and must SURVIVE there; only an `ascii` stream gets `...`."""
        import io

        from model_checker.utils.testing import make_encoding_test_streams, read_encoding_test_stream

        structure = _build(["A"], ["\\Box A"], back=1, mid=0, fwd=1)
        structure.interpret(structure.premises + structure.conclusions)
        structure.settings["print_z3"] = False
        streams = make_encoding_test_streams()
        structure.print_all(structure.settings, "EX", "Bimodal", output=streams["cp1252"])
        rendered = read_encoding_test_stream(streams["cp1252"])
        assert "=>" in rendered
        assert "{}" in rendered  # ∅ fallback
        assert "…" in rendered  # U+2026 is cp1252 0x85: no fallback
        assert "⟹" not in rendered and "∅" not in rendered

        ascii_stream = io.TextIOWrapper(io.BytesIO(), encoding="ascii", newline="")
        structure.print_all(structure.settings, "EX", "Bimodal", output=ascii_stream)
        ascii_stream.flush()
        ascii_rendered = ascii_stream.buffer.getvalue().decode("ascii")
        assert "..." in ascii_rendered and "=>" in ascii_rendered and "{}" in ascii_rendered

        structure.print_all(structure.settings, "EX", "Bimodal", output=streams["utf8"])
        control = read_encoding_test_stream(streams["utf8"])
        assert "⟹" in control and "…" in control and "∅" in control


class TestAlignedHistoryTable:
    """`align_vertically` (the `-a` flag) switches the certificate block to a time-aligned
    table: one row per representative position with a signed time and slot annotation, one
    column per lasso headed by its name and role, the evaluation point still marked `[ ]`."""

    def test_table_view_renders_rows_per_position_and_columns_per_lasso(self, capsys):
        import re

        structure = _build(
            ["\\Box (A \\vee B)"], ["\\Box A", "\\Box B"], back=2, mid=1, fwd=2,
            align_vertically=True,
        )
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        lines = out.splitlines()
        assert lines[0].startswith("Histories:")
        assert "[ ] marks the evaluation point" in lines[0]
        assert "Certificate:" not in out
        header = lines[1]
        assert re.match(r"\s+t\s+slot\s+\| L0 main\s+\| L1 ", header)
        assert "L3 " in header
        assert set(lines[2].strip()) <= {"-", "+"}  # the rule under the header
        rows = {line.split()[0]: line for line in lines[3:8]}
        assert list(rows) == ["-2", "-1", "0", "+1", "+2"]
        assert "back[0]" in rows["-2"] and "back[1]" in rows["-1"]
        assert "mid[0]" in rows["0"]
        assert "fwd[0]" in rows["+1"] and "fwd[1]" in rows["+2"]
        # Exactly one lasso cell in the whole table is bracketed: the main lasso at the
        # target (slot names like `back[0]` sit left of the `|` and are not cells).
        marked = [line for line in lines[3:8] if "[" in line.split("|", 1)[1]]
        assert len(marked) == 1
        target_row = marked[0]
        assert target_row.split()[0] == ("0" if structure.target_time == 0 else f"{structure.target_time:+d}")
        assert "Box guesses:" in out
        assert "⟹" not in out  # no arrow-chain rows in table mode
        assert "\033[" not in out

    def test_default_keeps_one_line_rows(self, capsys):
        structure = _build(["\\Box A"], ["B"], back=1, mid=0, fwd=1)
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        assert "slot" not in out
        assert any(line.strip().startswith("L0  main") for line in out.splitlines())
        assert "⟹" in out and "…" in out

    def test_empty_mid_table_has_no_mid_rows(self, capsys):
        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1, align_vertically=True)
        structure.print_certificate(output=sys.stdout)
        out = capsys.readouterr().out
        assert "mid[" not in out
        assert "back[0]" in out and "fwd[0]" in out
        assert "∅" in out  # empty labels keep the glyph in cells

    def test_table_cp1252_leg_does_not_raise(self):
        from model_checker.utils.testing import make_encoding_test_streams, read_encoding_test_stream

        structure = _build(["A"], ["B"], back=1, mid=0, fwd=1, align_vertically=True)
        streams = make_encoding_test_streams()
        structure.print_certificate(output=streams["cp1252"])
        rendered = read_encoding_test_stream(streams["cp1252"])
        assert "{}" in rendered and "∅" not in rendered

    def test_align_vertically_is_a_known_bimodal_setting(self):
        """`-a` is no longer dropped with `Flag 'align_vertically' doesn't correspond to any
        known setting`: the semantics declares it, so `SettingsManager` knows it."""
        from model_checker.settings.settings import SettingsManager
        from model_checker.theory_lib.bimodal import get_theory
        from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics

        assert BimodalSemantics.ADDITIONAL_GENERAL_SETTINGS == {"align_vertically": False}
        manager = SettingsManager(get_theory(), theory_name="bimodal")
        assert manager.DEFAULT_GENERAL_SETTINGS["align_vertically"] is False


class TestColorGating:
    def test_tty_output_carries_colors_and_pipes_do_not(self, monkeypatch):
        import io

        monkeypatch.delenv("NO_COLOR", raising=False)
        monkeypatch.delenv("FORCE_COLOR", raising=False)
        monkeypatch.setenv("TERM", "xterm")

        class _TTY(io.StringIO):
            def isatty(self):
                return True

        structure = _build(["\\Box A"], ["B"], back=1, mid=0, fwd=1)
        plain = io.StringIO()
        structure.print_certificate(output=plain)
        structure.print_evaluation(output=plain)
        assert "\033[" not in plain.getvalue()

        tty = _TTY()
        structure.print_certificate(output=tty)
        structure.print_evaluation(output=tty)
        assert "\033[" in tty.getvalue()

        monkeypatch.setenv("NO_COLOR", "1")
        quiet = _TTY()
        structure.print_certificate(output=quiet)
        assert "\033[" not in quiet.getvalue()


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
