"""Tests for bimodal data extraction methods, rewritten for the certificate redesign
(Phase 18). The retired encoding's `world_histories`/`main_world`/`time_shift_relations`
mock-based tests are replaced with tests against real built structures (the same
`Syntax -> ModelConstraints -> BimodalStructure` pipeline `test_structure.py` uses),
since `extract_states`/`extract_evaluation_world`/`extract_relations`/
`extract_propositions` now read `self.certificate`/`self.main_point`/`self.target_time`
(`semantic/model.py`), attributes only a real solve populates.
"""

from __future__ import annotations

from model_checker.theory_lib.bimodal.tests._build_support import _build, _settings


class TestExtractStatesWithCertificate:
    def test_worlds_are_one_per_lasso(self):
        """A countermodel example's `extract_states()['worlds']` names one 'lassoN' entry
        per lasso in the found certificate; bimodal has no possible/impossible distinction."""
        structure = _build(["A"], ["\\Box A"], back=1, mid=1, fwd=1)
        assert structure.certificate is not None, "expected a countermodel"
        states = structure.extract_states()
        assert states["possible"] == []
        assert states["impossible"] == []
        assert states["worlds"] == [
            f"lasso{i}" for i in range(len(structure.certificate.lassos))
        ]
        assert len(states["worlds"]) >= 1


class TestExtractStatesNoCertificate:
    def test_returns_empty_structure_when_no_certificate_found(self):
        """A theorem example (no countermodel) leaves `self.certificate is None`; extraction
        must return the empty structure, not raise or fabricate a phantom world (D8)."""
        structure = _build(["A"], ["A"], back=1, mid=1, fwd=1)
        assert structure.certificate is None
        assert structure.extract_states() == {"worlds": [], "possible": [], "impossible": []}


class TestExtractEvaluationWorld:
    def test_names_the_main_lasso(self):
        structure = _build(["A"], ["\\Box A"], back=1, mid=1, fwd=1)
        assert structure.certificate is not None
        world = structure.extract_evaluation_world()
        assert world == f"lasso{structure.main_point['lasso']}"

    def test_none_when_no_certificate(self):
        structure = _build(["A"], ["A"], back=1, mid=1, fwd=1)
        assert structure.certificate is None
        assert structure.extract_evaluation_world() is None


class TestExtractRelations:
    def test_describes_the_shift_action_structurally(self):
        """The task relation is the shift on the certified ShiftSet, true by construction
        (docs/ADEQUACY.md section 3) -- not enumerated, since infinitely many pairs are
        related. Extraction returns a structural description under the `shift` key."""
        structure = _build(["A"], ["\\Box A"], back=1, mid=1, fwd=1)
        assert structure.certificate is not None
        relations = structure.extract_relations()
        assert "shift" in relations
        assert "description" in relations["shift"]

    def test_empty_when_no_certificate(self):
        structure = _build(["A"], ["A"], back=1, mid=1, fwd=1)
        assert structure.certificate is None
        assert structure.extract_relations() == {}


class TestExtractPropositions:
    def test_empty_without_syntax_propositions(self):
        """`extract_propositions` reads `self.syntax.propositions`
        (`{name: sentence_obj}`), guarded by its own `hasattr` check (D8-style: never
        fabricate, just report empty) -- but nothing in the current framework actually
        populates `Syntax.propositions` (confirmed: no assignment to it anywhere in
        `model_checker.syntactic`/`model_checker.builder`), so this returns `{}` on a real
        built structure too, certificate or not. This test records that fact directly
        rather than asserting a shape the framework never produces."""
        structure = _build(["A"], ["\\Box A"], back=1, mid=1, fwd=1)
        assert structure.certificate is not None
        assert not hasattr(structure.syntax, "propositions")
        assert structure.extract_propositions() == {}

    def test_populated_when_syntax_propositions_present(self):
        """If `syntax.propositions` IS present (e.g. set by a future caller), extraction
        maps each sentence letter to one truth value per lasso."""
        structure = _build(["A"], ["\\Box A"], back=1, mid=1, fwd=1)
        assert structure.certificate is not None

        class _FakeSentence:
            def __init__(self, sentence_letter, proposition):
                self.sentence_letter = sentence_letter
                self.proposition = proposition

        structure.interpret(structure.premises + structure.conclusions)
        sentence_letter = next(iter(structure.syntax.sentence_letters))
        proposition = sentence_letter.proposition
        assert proposition is not None, "interpret() should have attached a proposition"
        structure.syntax.propositions = {
            "A": _FakeSentence(sentence_letter.sentence_letter, proposition)
        }

        propositions = structure.extract_propositions()
        assert propositions, "expected at least one sentence letter's truth values"
        for _letter, per_world in propositions.items():
            assert set(per_world.keys()) == {
                f"lasso{i}" for i in range(len(structure.certificate.lassos))
            }
            for value in per_world.values():
                assert value is None or isinstance(value, bool)

    def test_empty_when_no_certificate(self):
        structure = _build(["A"], ["A"], back=1, mid=1, fwd=1)
        assert structure.certificate is None
        assert structure.extract_propositions() == {}
