"""Explicit all-tag coverage tests for `temporal_depth()`.

## Change of meaning

This module previously carried four test classes: `TestBoundaryAnalysis` and
`TestBoundaryDocumentation` (pure-Python and live-solver verification of the
retired encoding's boundary-safety formula `M_safe(d) = max(d+2, 3)`),
`TestExampleRegression` (a generic all-active-examples SAT/UNSAT check, using
the retired `N`/`M` settings directly), and `TestTemporalDepthAllTags` (an
explicit all-17-JSON-tag coverage test for `temporal_depth()`, supplementing
`test_json_translation.py`'s own 26 tests).

The first three classes' entire subject -- the bounded-window boundary-safety
concern -- no longer exists (see `oracle/bimodal_logic/translation.py`'s
`temporal_depth()` docstring, and `theory_lib/bimodal/docs/ADEQUACY.md`
section 5, for why the certificate encoding has no vacuity artifact to guard
against). `TestExampleRegression`'s own claim ("every active example decides
correctly") is fully redundant with `test_oracle_provider.py`'s
`TestOracleExampleRegression` (the full, unconditional 53-example corpus, no
exclusions) and `theory_lib/bimodal/tests/unit/test_bimodal.py` itself. All
three are deleted, not rewritten -- there is nothing left to update.

`TestTemporalDepthAllTags` survives unchanged: `temporal_depth()` itself is a
plain, encoding-independent formula-depth metric (confirmed unaffected by the
certificate redesign), and this class's own claim (every JSON tag produces
the depth its docstring's rules specify) remains true and worth keeping as an
explicit gate, supplementing `test_json_translation.py`.
"""

from __future__ import annotations

# Import temporal_depth for the all-tags test
from bimodal_logic.translation import temporal_depth


class TestTemporalDepthAllTags:
    """Explicit all-17-tags coverage test for temporal_depth().

    The 17 JSON formula tags:
    Primitive (6): atom, bot, imp, box, untl, snce
    Enriched (11): neg, top, and, or, diamond, next, prev,
                   some_future, some_past, all_future, all_past

    This supplements the existing 26 tests in test_json_translation.py with
    a single test that confirms every tag produces the expected depth value,
    serving as an explicit gate check.
    """

    def test_all_17_tags_coverage(self):
        """Verify temporal_depth() handles all 17 JSON formula tags correctly.

        One representative formula is constructed for each tag.
        The expected depth follows the depth rules in temporal_depth() docstring.
        """
        atom_p = {"tag": "atom", "name": "p"}

        tag_cases = [
            # tag=atom: leaf, depth 0
            ("atom", atom_p, 0),

            # tag=bot: leaf, depth 0
            ("bot", {"tag": "bot"}, 0),

            # tag=top: leaf, depth 0
            ("top", {"tag": "top"}, 0),

            # tag=neg: extensional unary, depth(arg)
            ("neg", {"tag": "neg", "arg": atom_p}, 0),

            # tag=imp: extensional binary, max(left, right)
            ("imp", {"tag": "imp", "left": atom_p, "right": atom_p}, 0),

            # tag=and: extensional binary, max(left, right)
            ("and", {"tag": "and", "left": atom_p, "right": atom_p}, 0),

            # tag=or: extensional binary, max(left, right)
            ("or", {"tag": "or", "left": atom_p, "right": atom_p}, 0),

            # tag=box: modal, NO increment -- depth(child)
            ("box", {"tag": "box", "child": atom_p}, 0),

            # tag=diamond: modal, NO increment -- depth(arg)
            ("diamond", {"tag": "diamond", "arg": atom_p}, 0),

            # tag=untl: temporal primitive, 1 + max(event, guard)
            ("untl", {"tag": "untl", "event": atom_p, "guard": atom_p}, 1),

            # tag=snce: temporal primitive, 1 + max(event, guard)
            ("snce", {"tag": "snce", "event": atom_p, "guard": atom_p}, 1),

            # tag=next: temporal enriched, 1 + depth(arg)
            ("next", {"tag": "next", "arg": atom_p}, 1),

            # tag=prev: temporal enriched, 1 + depth(arg)
            ("prev", {"tag": "prev", "arg": atom_p}, 1),

            # tag=some_future: temporal enriched, 1 + depth(arg)
            ("some_future", {"tag": "some_future", "arg": atom_p}, 1),

            # tag=some_past: temporal enriched, 1 + depth(arg)
            ("some_past", {"tag": "some_past", "arg": atom_p}, 1),

            # tag=all_future: temporal enriched, 1 + depth(arg)
            ("all_future", {"tag": "all_future", "arg": atom_p}, 1),

            # tag=all_past: temporal enriched, 1 + depth(arg)
            ("all_past", {"tag": "all_past", "arg": atom_p}, 1),
        ]

        assert len(tag_cases) == 17, "Must have exactly 17 tag test cases"

        for tag_name, formula_json, expected_depth in tag_cases:
            actual = temporal_depth(formula_json)
            assert actual == expected_depth, (
                f"temporal_depth() for tag='{tag_name}': "
                f"expected {expected_depth}, got {actual}"
            )

    def test_nested_temporal_tags_depth(self):
        """Verify temporal_depth correctly computes nested temporal operators.

        Tests cases from the boundary claim: G(G(p)) has depth 2,
        F(G(p)) has depth 2, H(F(p)) has depth 2, G(G(G(p))) has depth 3.
        """
        atom_p = {"tag": "atom", "name": "p"}

        # G(G(p)) = all_future(all_future(atom)) -> depth=2
        gg_p = {"tag": "all_future", "arg": {"tag": "all_future", "arg": atom_p}}
        assert temporal_depth(gg_p) == 2, "G(G(p)) should have depth 2"

        # F(G(p)) = some_future(all_future(atom)) -> depth=2
        fg_p = {"tag": "some_future", "arg": {"tag": "all_future", "arg": atom_p}}
        assert temporal_depth(fg_p) == 2, "F(G(p)) should have depth 2"

        # H(F(p)) = all_past(some_future(atom)) -> depth=2
        hf_p = {"tag": "all_past", "arg": {"tag": "some_future", "arg": atom_p}}
        assert temporal_depth(hf_p) == 2, "H(F(p)) should have depth 2"

        # G(G(G(p))) = all_future(all_future(all_future(atom))) -> depth=3
        ggg_p = {
            "tag": "all_future",
            "arg": {"tag": "all_future", "arg": {"tag": "all_future", "arg": atom_p}}
        }
        assert temporal_depth(ggg_p) == 3, "G(G(G(p))) should have depth 3"
