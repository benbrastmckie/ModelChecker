"""Oracle-side test for the Z3OracleProvider frame-class declaration.

Extracted from `model_checker`'s
`theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` (task 118 Phase 5): that
in-package module's `TestFrameClassDeclarationConsistency` class had one test method
requiring a runtime import of `bimodal_logic.provider.Z3OracleProvider`, while its
sibling methods test the in-package `BimodalSemantics.frame_constraints` directly and
have no oracle dependency. Per the "zero references" gate
(`grep -rl bimodal_logic code/src/model_checker/` must return nothing), this single
oracle-dependent method moved here; the other three methods stayed in place.

See `bimodal_logic/provider.py` module docstring for the full terminology
disambiguation and axiom mapping (the "Base" frame-class claim vs. BimodalLogic's
proof-system `FrameClass.Base`).
"""

from __future__ import annotations


class TestFrameClassDeclarationConsistency:
    """Tests verifying the oracle's 'Base' frame class claim is justified.

    The oracle declares supported_frame_classes = frozenset({"Base"}), meaning
    the Z3 frame satisfies the three TaskFrame axioms. This class documents
    what 'Base' means in this context.

    See bimodal_logic/provider.py module docstring for the full terminology
    disambiguation and axiom mapping.
    """

    def test_base_means_taskframe_axioms_not_frameclassbase(self):
        """Document that 'Base' refers to TaskFrame axioms, not FrameClass.Base.

        The oracle's supported_frame_classes = frozenset({"Base"}) uses 'Base'
        to mean "satisfies TaskFrame axioms" (three axioms: nullity, converse,
        compose). This is NOT the same as BimodalLogic's proof-system
        FrameClass.Base (which encompasses 37 axioms across the proof theory).

        This test documents the mapping by verifying the oracle class declares
        supported_frame_classes. The corresponding in-package check that the Z3
        frame constraints actually implement the three TaskFrame axioms lives in
        `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py`
        (`test_three_taskframe_axioms_present_in_frame_constraints` and its
        sibling axiom-specific tests).
        """
        from bimodal_logic.provider import Z3OracleProvider
        assert hasattr(Z3OracleProvider, 'supported_frame_classes'), (
            "Z3OracleProvider should declare supported_frame_classes"
        )
        assert Z3OracleProvider.supported_frame_classes == frozenset({"Base"}), (
            "Z3OracleProvider.supported_frame_classes should be frozenset({'Base'})"
        )
